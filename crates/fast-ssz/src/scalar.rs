//! Canonical encodings of SSZ scalar values.

/// A scalar encoding violates the SSZ byte representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScalarError {
    InvalidLength,
    InvalidBoolean,
}

/// Serialize an SSZ boolean to its unique one-byte encoding.
pub fn encode_bool(value: bool) -> [u8; 1] {
    if value {
        [1]
    } else {
        [0]
    }
}

/// Deserialize a boolean, rejecting noncanonical bytes and lengths.
pub fn decode_bool(bytes: &[u8]) -> Result<bool, ScalarError> {
    if bytes.len() != 1 {
        return Err(ScalarError::InvalidLength);
    }
    match bytes[0] {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(ScalarError::InvalidBoolean),
    }
}
