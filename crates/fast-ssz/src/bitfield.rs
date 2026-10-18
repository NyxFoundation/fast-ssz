//! Canonical SSZ bitvectors, with low bits first and zero high padding.

/// A bitfield value, declaration or byte encoding violates SSZ.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BitfieldError {
    EmptyVector,
    InvalidLength,
    PaddingBits,
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

fn pack_bits(bits: &[bool]) -> Vec<u8> {
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
