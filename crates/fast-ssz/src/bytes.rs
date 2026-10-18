//! Borrowed, zero-copy codecs for SSZ byte vectors and byte lists.

/// A byte-array declaration or value violates the SSZ representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ByteError {
    EmptyVector,
    InvalidLength,
    OverLimit,
}

/// Serialize a byte vector with its declared, nonzero length.
///
/// The returned bytes borrow the input; no allocation or copying takes place.
pub fn encode_byte_vector(bytes: &[u8], length: usize) -> Result<&[u8], ByteError> {
    if length == 0 {
        return Err(ByteError::EmptyVector);
    }
    if bytes.len() != length {
        return Err(ByteError::InvalidLength);
    }
    Ok(bytes)
}

/// Deserialize a byte vector, refusing an invalid declaration or length.
pub fn decode_byte_vector(bytes: &[u8], length: usize) -> Result<&[u8], ByteError> {
    encode_byte_vector(bytes, length)
}

/// Serialize a byte list, enforcing its declared upper bound.
///
/// Empty lists and zero limits are permitted. The returned bytes borrow the input.
pub fn encode_byte_list(bytes: &[u8], limit: usize) -> Result<&[u8], ByteError> {
    if bytes.len() > limit {
        return Err(ByteError::OverLimit);
    }
    Ok(bytes)
}

/// Deserialize a byte list, refusing values above its declared upper bound.
pub fn decode_byte_list(bytes: &[u8], limit: usize) -> Result<&[u8], ByteError> {
    encode_byte_list(bytes, limit)
}
