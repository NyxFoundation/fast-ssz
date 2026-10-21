//! Sequence wire construction shared by typed collection codecs.

use crate::{
    codec::{fixed_size, Ssz},
    error::CodecError,
    scalar,
};

pub(crate) fn encode_parts<T: Ssz>(values: &[T]) -> Result<Vec<Vec<u8>>, CodecError> {
    let mut parts = Vec::new();
    let mut index = 0;
    while index < values.len() {
        parts.push(values[index].encode()?);
        index += 1;
    }
    Ok(parts)
}

fn append(output: &mut Vec<u8>, bytes: &[u8]) {
    let mut index = 0;
    while index < bytes.len() {
        output.push(bytes[index]);
        index += 1;
    }
}

fn leading_and_total(parts: &[Vec<u8>], fixed: bool) -> Result<(usize, usize), CodecError> {
    let leading = if fixed { 0 } else { parts.len() as u128 * 4 };
    if leading >= 4_294_967_296 {
        return Err(CodecError::SizeOverflow);
    }
    let mut total = leading;
    let mut index = 0;
    while index < parts.len() {
        total += parts[index].len() as u128;
        if total >= 4_294_967_296 {
            return Err(CodecError::SizeOverflow);
        }
        index += 1;
    }
    Ok((leading as usize, total as usize))
}

fn assemble(parts: &[Vec<u8>], fixed: bool) -> Result<Vec<u8>, CodecError> {
    let (leading, _) = leading_and_total(parts, fixed)?;
    let mut output = Vec::new();
    if !fixed {
        let mut offset = leading;
        let mut index = 0;
        while index < parts.len() {
            append(&mut output, &scalar::encode_u32(offset as u32));
            offset += parts[index].len();
            index += 1;
        }
    }
    let mut index = 0;
    while index < parts.len() {
        append(&mut output, &parts[index]);
        index += 1;
    }
    Ok(output)
}

pub(crate) fn encode_sequence<T: Ssz>(values: &[T]) -> Result<Vec<u8>, CodecError> {
    let parts = encode_parts(values)?;
    let fixed = match fixed_size::<T>() {
        Ok(None) => false,
        // Overflow means a fixed mathematical width, not a variable layout.
        Ok(Some(_)) | Err(CodecError::SizeOverflow) => true,
        Err(error) => return Err(error),
    };
    assemble(&parts, fixed)
}
