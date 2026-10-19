//! Borrowed, zero-copy codecs for SSZ byte vectors, lists and progressive lists.

/// A byte-array declaration or value violates the SSZ representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ByteError {
    EmptyVector,
    InvalidLength,
    OverLimit,
    OffsetOverflow,
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

fn check_progressive_bound(length: usize, limit: Option<usize>) -> Result<(), ByteError> {
    if let Some(capacity) = limit {
        if length > capacity {
            return Err(ByteError::OverLimit);
        }
    }
    Ok(())
}

fn check_sequence_width(length: usize) -> Result<(), ByteError> {
    if length > u32::MAX as usize {
        return Err(ByteError::OffsetOverflow);
    }
    Ok(())
}

/// Serialize a progressive byte list without allocating or copying.
///
/// `None` declares no capacity; `Some(limit)` adds a capacity check. Both forms
/// enforce the pinned reference's sequence encoding size of less than 2^32 bytes.
///
/// ```
/// use nyx_ssz::bytes::{encode_progressive_byte_list, ByteError};
/// let bytes = [0, 255];
/// assert_eq!(encode_progressive_byte_list(&bytes, None), Ok(bytes.as_slice()));
/// assert_eq!(encode_progressive_byte_list(&bytes, Some(1)), Err(ByteError::OverLimit));
/// ```
pub fn encode_progressive_byte_list(
    bytes: &[u8],
    limit: Option<usize>,
) -> Result<&[u8], ByteError> {
    check_progressive_bound(bytes.len(), limit)?;
    check_sequence_width(bytes.len())?;
    Ok(bytes)
}

/// Deserialize a progressive byte list while borrowing its input.
///
/// As in the reference decoder, the offset-width check precedes the capacity check.
pub fn decode_progressive_byte_list(
    bytes: &[u8],
    limit: Option<usize>,
) -> Result<&[u8], ByteError> {
    check_sequence_width(bytes.len())?;
    check_progressive_bound(bytes.len(), limit)?;
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::{check_progressive_bound, check_sequence_width, ByteError};

    #[test]
    fn should_accept_the_largest_sequence_width_when_it_fits_four_bytes() {
        assert_eq!(check_sequence_width(0), Ok(()));
        assert_eq!(check_sequence_width(u32::MAX as usize), Ok(()));
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn should_reject_oversized_sequence_widths_without_allocating_them() {
        assert_eq!(
            check_sequence_width(u32::MAX as usize + 1),
            Err(ByteError::OffsetOverflow)
        );
        assert_eq!(
            check_sequence_width(usize::MAX),
            Err(ByteError::OffsetOverflow)
        );
    }

    #[test]
    fn should_check_progressive_capacities_without_arithmetic_overflow() {
        assert_eq!(check_progressive_bound(usize::MAX, None), Ok(()));
        assert_eq!(
            check_progressive_bound(usize::MAX, Some(usize::MAX)),
            Ok(())
        );
        assert_eq!(
            check_progressive_bound(usize::MAX, Some(0)),
            Err(ByteError::OverLimit)
        );
    }
}
