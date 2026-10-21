//! Canonical SSZ bitfields, with low bits first and canonical padding/delimiters.

/// A bitfield value, declaration or byte encoding violates SSZ.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BitfieldError {
    EmptyVector,
    InvalidLength,
    PaddingBits,
    OverLimit,
    EmptyEncoding,
    NoDelimiter,
    TrailingZeros,
}

/// A validated progressive bitlist borrowing its canonical SSZ encoding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BitListView<'a> {
    encoded: &'a [u8],
}

impl<'a> BitListView<'a> {
    /// Return the borrowed encoding, including its mandatory delimiter bit.
    pub fn as_ssz_bytes(&self) -> &'a [u8] {
        self.encoded
    }

    /// Return the data bit count, excluding the delimiter.
    ///
    /// The count is widened because packed input can hold more bits than `usize` counts.
    pub fn len_bits(&self) -> u128 {
        let bytes = self.as_ssz_bytes();
        let final_byte = bytes[bytes.len() - 1];
        let whole = (bytes.len() - 1) as u128;
        whole * 8 + highest_bit(final_byte) as u128
    }
}

fn bit_at(bits: &[bool], index: usize) -> u8 {
    if index < bits.len() && bits[index] {
        1
    } else {
        0
    }
}

fn pack_byte(bits: &[bool]) -> u8 {
    bit_at(bits, 0)
        | (bit_at(bits, 1) << 1)
        | (bit_at(bits, 2) << 2)
        | (bit_at(bits, 3) << 3)
        | (bit_at(bits, 4) << 4)
        | (bit_at(bits, 5) << 5)
        | (bit_at(bits, 6) << 6)
        | (bit_at(bits, 7) << 7)
}

pub(crate) fn pack_bits(bits: &[bool]) -> Vec<u8> {
    let count = bits.len().div_ceil(8);
    let mut output = Vec::new();
    let mut index = 0;
    while index < count {
        output.push(pack_byte(&bits[index * 8..]));
        index += 1;
    }
    output
}

fn unpack_bits(bytes: &[u8], count: usize) -> Vec<bool> {
    let mut output = Vec::new();
    let mut index = 0;
    while index < count {
        output.push(((bytes[index / 8] >> (index % 8)) & 1) == 1);
        index += 1;
    }
    output
}

/// Encode exactly `length` bits; a zero-length vector is an illegal declaration.
pub fn encode_bit_vector(bits: &[bool], length: usize) -> Result<Vec<u8>, BitfieldError> {
    if length == 0 {
        return Err(BitfieldError::EmptyVector);
    }
    if bits.len() != length {
        return Err(BitfieldError::InvalidLength);
    }
    Ok(pack_bits(bits))
}

/// Decode exactly `length` bits, rejecting wrong byte counts and nonzero padding.
pub fn decode_bit_vector(bytes: &[u8], length: usize) -> Result<Vec<bool>, BitfieldError> {
    if length == 0 {
        return Err(BitfieldError::EmptyVector);
    }
    if bytes.len() != length.div_ceil(8) {
        return Err(BitfieldError::InvalidLength);
    }
    let remainder = length % 8;
    if remainder != 0 && bytes[bytes.len() - 1] >> remainder != 0 {
        return Err(BitfieldError::PaddingBits);
    }
    Ok(unpack_bits(bytes, length))
}

fn all_zero(bytes: &[u8]) -> bool {
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != 0 {
            return false;
        }
        index += 1;
    }
    true
}

fn highest_bit(byte: u8) -> usize {
    if (byte >> 7) & 1 == 1 {
        7
    } else if (byte >> 6) & 1 == 1 {
        6
    } else if (byte >> 5) & 1 == 1 {
        5
    } else if (byte >> 4) & 1 == 1 {
        4
    } else if (byte >> 3) & 1 == 1 {
        3
    } else if (byte >> 2) & 1 == 1 {
        2
    } else if (byte >> 1) & 1 == 1 {
        1
    } else {
        0
    }
}

/// Encode a bounded bitlist with its mandatory highest-set-bit delimiter.
pub fn encode_bit_list(bits: &[bool], limit: usize) -> Result<Vec<u8>, BitfieldError> {
    if bits.len() > limit {
        return Err(BitfieldError::OverLimit);
    }
    let mut output = pack_bits(bits);
    let remainder = bits.len() % 8;
    if remainder == 0 {
        output.push(1);
    } else {
        let last = output.len() - 1;
        output[last] |= 1u8 << remainder;
    }
    Ok(output)
}

/// Decode a canonical bounded bitlist without overflowing byte-to-bit counts.
pub fn decode_bit_list(bytes: &[u8], limit: usize) -> Result<Vec<bool>, BitfieldError> {
    if bytes.is_empty() {
        return Err(BitfieldError::EmptyEncoding);
    }
    let final_byte = bytes[bytes.len() - 1];
    if final_byte == 0 {
        return Err(if all_zero(bytes) {
            BitfieldError::NoDelimiter
        } else {
            BitfieldError::TrailingZeros
        });
    }
    let high = highest_bit(final_byte);
    let whole = bytes.len() - 1;
    if whole > limit / 8 {
        return Err(BitfieldError::OverLimit);
    }
    let base = whole * 8;
    if high > limit - base {
        return Err(BitfieldError::OverLimit);
    }
    Ok(unpack_bits(bytes, base + high))
}

/// Encode a progressive bitlist with no capacity or an optional declared capacity.
pub fn encode_progressive_bit_list(
    bits: &[bool],
    limit: Option<usize>,
) -> Result<Vec<u8>, BitfieldError> {
    let capacity = match limit {
        Some(capacity) => capacity,
        None => usize::MAX,
    };
    encode_bit_list(bits, capacity)
}

/// Decode a progressive bitlist without copying or expanding its packed bits.
///
/// `None` imposes no declared capacity. A successful view keeps the canonical
/// encoding, including the delimiter, and a bit count excluding that delimiter.
///
/// ```
/// use nyx_ssz::bitfield::decode_progressive_bit_list;
/// let encoded = [0x0d];
/// let view = decode_progressive_bit_list(&encoded, None).unwrap();
/// assert_eq!(view.len_bits(), 3);
/// assert_eq!(view.as_ssz_bytes(), &encoded);
/// ```
pub fn decode_progressive_bit_list(
    bytes: &[u8],
    limit: Option<usize>,
) -> Result<BitListView<'_>, BitfieldError> {
    if bytes.is_empty() {
        return Err(BitfieldError::EmptyEncoding);
    }
    let final_byte = bytes[bytes.len() - 1];
    if final_byte == 0 {
        return Err(if all_zero(bytes) {
            BitfieldError::NoDelimiter
        } else {
            BitfieldError::TrailingZeros
        });
    }
    let view = BitListView { encoded: bytes };
    let bit_len = view.len_bits();
    if let Some(capacity) = limit {
        if bit_len > capacity as u128 {
            return Err(BitfieldError::OverLimit);
        }
    }
    Ok(view)
}
