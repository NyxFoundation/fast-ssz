//! Allocation-free canonical normalization of owned packed bitfields.
use crate::{bit_storage::delimited_len, encoding, error::CodecError};

pub(crate) fn vector_len(bytes: &[u8], bits: usize) -> Result<usize, CodecError> {
    if bits == 0 {
        return Err(CodecError::EmptyVector);
    }
    if bytes.len() != bits.div_ceil(8) {
        return Err(CodecError::InvalidLength);
    }
    Ok(bytes.len())
}

pub(crate) fn write_vector(bytes: &[u8], bits: usize, output: &mut [u8]) -> Result<(), CodecError> {
    encoding::check_length(output, vector_len(bytes, bits)?)?;
    output.copy_from_slice(bytes);
    let remainder = bits % 8;
    if remainder != 0 {
        output[bytes.len() - 1] &= (1_u8 << remainder) - 1;
    }
    Ok(())
}

pub(crate) fn list_len(bytes: &[u8], limit: Option<usize>) -> Result<usize, CodecError> {
    if limit.is_some_and(|capacity| delimited_len(bytes) > capacity as u128) {
        return Err(CodecError::OverLimit);
    }
    Ok(bytes.len().max(1))
}

pub(crate) fn write_list(
    bytes: &[u8],
    limit: Option<usize>,
    output: &mut [u8],
) -> Result<(), CodecError> {
    encoding::check_length(output, list_len(bytes, limit)?)?;
    if bytes.is_empty() {
        output[0] = 1;
        return Ok(());
    }
    output.copy_from_slice(bytes);
    let last = output.len() - 1;
    if output[last] == 0 {
        output[last] = 1;
    }
    Ok(())
}
