//! Bounded collection roots, packing basic elements but rooting composite ones.

use crate::{
    codec::{fixed_size, is_basic, Ssz},
    collection_wire::encode_parts,
    error::CodecError,
    merkle::{merkleize, MerkleizeError, Node},
    sha256::hash_pair,
    tree_hash::hash_tree_root_u128,
};

fn pack_parts(parts: &[Vec<u8>]) -> Vec<Node> {
    let mut chunks = Vec::new();
    let mut pending = [0; 32];
    let mut filled = 0;
    let mut part = 0;
    while part < parts.len() {
        let mut byte = 0;
        while byte < parts[part].len() {
            pending[filled] = parts[part][byte];
            filled += 1;
            if filled == 32 {
                chunks.push(pending);
                pending = [0; 32];
                filled = 0;
            }
            byte += 1;
        }
        part += 1;
    }
    if filled != 0 {
        chunks.push(pending);
    }
    chunks
}

fn root_elements<T: Ssz>(values: &[T]) -> Result<Vec<Node>, CodecError> {
    let mut roots = Vec::new();
    let mut index = 0;
    while index < values.len() {
        roots.push(values[index].hash_tree_root()?);
        index += 1;
    }
    Ok(roots)
}

fn basic_capacity<T: Ssz>(positions: usize) -> Result<usize, CodecError> {
    match fixed_size::<T>()? {
        Some(width @ (1 | 2 | 4 | 8 | 16 | 32)) => Ok(positions.div_ceil(32 / width)),
        _ => Err(CodecError::InvalidIntegerWidth),
    }
}

pub(crate) fn root_sequence<T: Ssz>(
    values: &[T],
    positions: usize,
    mix_length: bool,
) -> Result<Node, CodecError> {
    let (chunks, capacity) = if is_basic::<T>() {
        let parts = encode_parts(values)?;
        (pack_parts(&parts), basic_capacity::<T>(positions)?)
    } else {
        (root_elements(values)?, positions)
    };
    let contents = match merkleize(&chunks, Some(capacity)) {
        Ok(root) => root,
        // Only an unlawful child codec can exceed a checked parent's capacity.
        Err(MerkleizeError::LimitTooSmall) => return Err(CodecError::InvalidLength),
    };
    if mix_length {
        Ok(hash_pair(
            &contents,
            &hash_tree_root_u128(values.len() as u128),
        ))
    } else {
        Ok(contents)
    }
}
