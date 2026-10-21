//! SSZ roots with canonical packing, bounded trees and progressive spines.

use crate::{bitfield::BitListView, error::CodecError, merkle::Node};

fn scalar_chunk<const N: usize>(encoded: [u8; N]) -> [u8; 32] {
    let mut root = [0; 32];
    root[..N].copy_from_slice(&encoded);
    root
}

/// Compute an SSZ boolean's root: its encoding followed by 31 zero bytes.
pub fn hash_tree_root_bool(value: bool) -> [u8; 32] {
    scalar_chunk(crate::scalar::encode_bool(value))
}

macro_rules! integer_root {
    ($ty:ty, $function:ident, $encode:ident) => {
        #[doc = concat!("Compute an SSZ `", stringify!($ty), "` root with little-endian zero padding.")]
        pub fn $function(value: $ty) -> [u8; 32] {
            scalar_chunk(crate::scalar::$encode(value))
        }
    };
}

integer_root!(u8, hash_tree_root_u8, encode_u8);
integer_root!(u16, hash_tree_root_u16, encode_u16);
integer_root!(u32, hash_tree_root_u32, encode_u32);
integer_root!(u64, hash_tree_root_u64, encode_u64);
integer_root!(u128, hash_tree_root_u128, encode_u128);

/// Compute an SSZ uint256's root: exactly its 32-byte little-endian encoding.
pub fn hash_tree_root_u256(value: &crate::U256) -> [u8; 32] {
    crate::scalar::encode_u256(value)
}

fn pack_bytes(bytes: &[u8], count: usize, final_mask: u8) -> Vec<Node> {
    let mut output = Vec::new();
    let mut node = [0; 32];
    let mut filled = 0;
    let mut index = 0;
    while index < count {
        let byte = if index + 1 == count {
            bytes[index] & final_mask
        } else {
            bytes[index]
        };
        node[filled] = byte;
        filled += 1;
        if filled == 32 {
            output.push(node);
            node = [0; 32];
            filled = 0;
        }
        index += 1;
    }
    if filled != 0 {
        output.push(node);
    }
    output
}

pub(crate) fn packed_root(
    bytes: &[u8],
    count: usize,
    final_mask: u8,
    capacity: Option<usize>,
    length: Option<u128>,
) -> Result<Node, CodecError> {
    let chunks = pack_bytes(bytes, count, final_mask);
    let root = match capacity {
        Some(capacity) => match crate::merkle::merkleize(&chunks, Some(capacity)) {
            Ok(root) => root,
            Err(_) => return Err(CodecError::OverLimit),
        },
        None => crate::merkle::merkleize_progressive(&chunks),
    };
    match length {
        Some(length) => Ok(crate::sha256::hash_pair(
            &root,
            &hash_tree_root_u128(length),
        )),
        None => Ok(root),
    }
}

fn check_bound(count: u128, limit: Option<usize>) -> Result<(), CodecError> {
    if let Some(limit) = limit {
        if count > limit as u128 {
            return Err(CodecError::OverLimit);
        }
    }
    Ok(())
}

/// Root a borrowed byte vector against its exact nonzero declaration.
pub fn hash_tree_root_byte_vector(bytes: &[u8], length: usize) -> Result<Node, CodecError> {
    if length == 0 {
        return Err(CodecError::EmptyVector);
    }
    if bytes.len() != length {
        return Err(CodecError::InvalidLength);
    }
    packed_root(bytes, bytes.len(), 255, Some(length.div_ceil(32)), None)
}

/// Root a byte list using its declared tree capacity and actual byte count.
pub fn hash_tree_root_byte_list(bytes: &[u8], limit: usize) -> Result<Node, CodecError> {
    check_bound(bytes.len() as u128, Some(limit))?;
    packed_root(
        bytes,
        bytes.len(),
        255,
        Some(limit.div_ceil(32)),
        Some(bytes.len() as u128),
    )
}

/// Root a progressive byte list without imposing the serialization offset envelope.
pub fn hash_tree_root_progressive_byte_list(
    bytes: &[u8],
    limit: Option<usize>,
) -> Result<Node, CodecError> {
    check_bound(bytes.len() as u128, limit)?;
    packed_root(bytes, bytes.len(), 255, None, Some(bytes.len() as u128))
}

/// Root exactly `length` low-bit-first data bits, with no list delimiter.
pub fn hash_tree_root_bit_vector(bits: &[bool], length: usize) -> Result<Node, CodecError> {
    if length == 0 {
        return Err(CodecError::EmptyVector);
    }
    if bits.len() != length {
        return Err(CodecError::InvalidLength);
    }
    let bytes = crate::bitfield::pack_bits(bits);
    packed_root(&bytes, bytes.len(), 255, Some(length.div_ceil(256)), None)
}

/// Root a bounded bitlist; its delimiter is not included in Merkle packing.
pub fn hash_tree_root_bit_list(bits: &[bool], limit: usize) -> Result<Node, CodecError> {
    check_bound(bits.len() as u128, Some(limit))?;
    let bytes = crate::bitfield::pack_bits(bits);
    packed_root(
        &bytes,
        bytes.len(),
        255,
        Some(limit.div_ceil(256)),
        Some(bits.len() as u128),
    )
}

/// Root progressive data bits with an optional declared bit capacity.
pub fn hash_tree_root_progressive_bit_list(
    bits: &[bool],
    limit: Option<usize>,
) -> Result<Node, CodecError> {
    check_bound(bits.len() as u128, limit)?;
    let bytes = crate::bitfield::pack_bits(bits);
    packed_root(&bytes, bytes.len(), 255, None, Some(bits.len() as u128))
}

pub(crate) fn bitlist_payload(byte_count: usize, bit_count: u128) -> (usize, u8) {
    let remainder = (bit_count % 8) as u32;
    if remainder == 0 {
        (byte_count - 1, 255)
    } else {
        (byte_count, (1u8 << remainder) - 1)
    }
}

/// Root a validated borrowed progressive bitlist without expanding its Boolean values.
///
/// The widened bit count is preserved. Delimiter removal neither mutates the
/// input nor allocates an intermediate encoding copy; the node buffer is allocated.
pub fn hash_tree_root_progressive_bit_list_view(
    value: &BitListView<'_>,
    limit: Option<usize>,
) -> Result<Node, CodecError> {
    let length = value.len_bits();
    check_bound(length, limit)?;
    let bytes = value.as_ssz_bytes();
    let (count, mask) = bitlist_payload(bytes.len(), length);
    packed_root(bytes, count, mask, None, Some(length))
}
