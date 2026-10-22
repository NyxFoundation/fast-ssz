//! Sequence wire construction shared by typed collection codecs.

use crate::{
    codec::{fixed_size, Ssz},
    error::CodecError,
    scalar,
};

// None records reference success with an inaccessible oversized child, not
// empty bytes. Later protocol faults must still precede parent assembly.
pub(crate) fn encode_parts<T: Ssz>(values: &[T]) -> Result<Option<Vec<Vec<u8>>>, CodecError> {
    let mut parts = Vec::new();
    let mut oversized = false;
    let mut index = 0;
    while index < values.len() {
        match values[index].encode() {
            Ok(part) => parts.push(part),
            Err(CodecError::NativeOutputOverflow) => oversized = true,
            Err(error) => return Err(error),
        }
        index += 1;
    }
    Ok(if oversized { None } else { Some(parts) })
}

pub(crate) fn append(output: &mut Vec<u8>, bytes: &[u8]) {
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
    match parts {
        Some(parts) => assemble(&parts, fixed),
        // Every sequence has a strict 2^32 assembly envelope, even fixed ones.
        // A child larger than usize::MAX necessarily exceeds that envelope.
        None => Err(CodecError::SizeOverflow),
    }
}
