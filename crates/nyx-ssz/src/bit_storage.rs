//! Packed storage operations shared by the owned bitfield types and codecs.

use crate::{
    bitfield::{self, BitfieldError},
    error::CodecError,
    tree_hash::{bitlist_payload, packed_root},
};

pub(crate) fn fault(error: BitfieldError) -> CodecError {
    match error {
        BitfieldError::EmptyVector => CodecError::EmptyVector,
        BitfieldError::InvalidLength => CodecError::InvalidLength,
        BitfieldError::PaddingBits => CodecError::PaddingBits,
        BitfieldError::OverLimit => CodecError::OverLimit,
        BitfieldError::EmptyEncoding => CodecError::EmptyEncoding,
        BitfieldError::NoDelimiter => CodecError::NoDelimiter,
        BitfieldError::TrailingZeros => CodecError::TrailingZeros,
    }
}

pub(crate) fn copy_bytes(bytes: &[u8]) -> Vec<u8> {
    let mut output = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        output.push(bytes[index]);
        index += 1;
    }
    output
}

pub(crate) fn validate_vector(bytes: &[u8], length: usize) -> Result<(), CodecError> {
    bitfield::validate_bit_vector(bytes, length).map_err(fault)
}

pub(crate) fn validate_list(bytes: &[u8], limit: Option<usize>) -> Result<(), CodecError> {
    match bitfield::decode_progressive_bit_list(bytes, limit) {
        Ok(_) => Ok(()),
        Err(error) => Err(fault(error)),
    }
}

pub(crate) fn delimited_len(bytes: &[u8]) -> u128 {
    if bytes.is_empty() {
        return 0;
    }
    let last = bytes.len() - 1;
    last as u128 * 8 + bitfield::highest_bit(bytes[last]) as u128
}

pub(crate) fn get_bit(bytes: &[u8], index: u128) -> Option<bool> {
    let byte = index / 8;
    if byte >= bytes.len() as u128 {
        return None;
    }
    Some((bytes[byte as usize] >> (index % 8) as u32) & 1 == 1)
}

pub(crate) fn get_list_bit(bytes: &[u8], index: u128) -> Option<bool> {
    if index >= delimited_len(bytes) {
        return None;
    }
    get_bit(bytes, index)
}

pub(crate) fn normalize_list(bytes: &[u8], limit: Option<usize>) -> Result<Vec<u8>, CodecError> {
    if let Some(capacity) = limit {
        if delimited_len(bytes) > capacity as u128 {
            return Err(CodecError::OverLimit);
        }
    }
    let mut output = copy_bytes(bytes);
    if bytes.is_empty() {
        output.push(1);
    } else {
        let last = output.len() - 1;
        if output[last] == 0 {
            output[last] = 1;
        }
    }
    Ok(output)
}

pub(crate) fn root_bounded_list(bytes: &[u8], limit: usize) -> Result<[u8; 32], CodecError> {
    let view = match bitfield::decode_progressive_bit_list(bytes, Some(limit)) {
        Ok(view) => view,
        Err(error) => return Err(fault(error)),
    };
    let length = view.len_bits();
    let (count, mask) = bitlist_payload(bytes.len(), length);
    packed_root(bytes, count, mask, Some(limit.div_ceil(256)), Some(length))
}
