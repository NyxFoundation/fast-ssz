//! Shared implementation for generated heterogeneous codecs.
use crate::{
    codec::{self, Ssz},
    container_wire,
    error::CodecError,
    merkle::{self, Node},
    sha256::hash_pair,
};

/// Completed value or nested refusal retained by a generated field decoder.
pub struct FieldDecodeState<T: Ssz> {
    pub value: Option<T>,
    pub child: Option<T::DecodeState>,
}

impl<T: Ssz> Default for FieldDecodeState<T> {
    fn default() -> Self {
        Self {
            value: None,
            child: None,
        }
    }
}

/// Encoded fields collected before applying the parent's four-byte budget.
#[derive(Default)]
pub struct FieldEncoder {
    slots: Vec<(bool, Vec<u8>)>,
    oversized: bool,
}

impl FieldEncoder {
    pub fn push<T: Ssz>(&mut self, value: &T) -> Result<(), CodecError> {
        match value.encode() {
            Ok(bytes) => self
                .slots
                .push((!matches!(codec::fixed_size::<T>(), Ok(None)), bytes)),
            Err(CodecError::NativeOutputOverflow) => self.oversized = true,
            Err(error) => return Err(error),
        }
        Ok(())
    }

    pub fn finish(self) -> Result<Vec<u8>, CodecError> {
        if self.oversized {
            return Err(CodecError::SizeOverflow);
        }
        container_wire::assemble(&self.slots)
    }
}

/// Root fields at ordinary contiguous or progressive sparse positions.
pub fn root_fields(roots: &[Node], active: Option<&[bool]>) -> Result<Node, CodecError> {
    let Some(active) = active else {
        return merkle::merkleize(roots, Some(roots.len())).map_err(|_| CodecError::InvalidLength);
    };
    if active.len() > 256 || active.iter().filter(|&&bit| bit).count() != roots.len() {
        return Err(CodecError::LayoutFieldCount);
    }
    let mut slots = Vec::with_capacity(active.len());
    let mut word = [0; 32];
    let mut ordinal = 0;
    for (index, &occupied) in active.iter().enumerate() {
        slots.push(if occupied {
            word[index / 8] |= 1 << (index % 8);
            let node = roots[ordinal];
            ordinal += 1;
            node
        } else {
            [0; 32]
        });
    }
    Ok(hash_pair(&merkle::merkleize_progressive(&slots), &word))
}

/// Union has no four-byte envelope; preserve the exact native success boundary.
pub fn encode_union<T: Ssz>(selector: u8, value: &T) -> Result<Vec<u8>, CodecError> {
    let body = value.encode()?;
    if body.len() == usize::MAX {
        return Err(CodecError::NativeOutputOverflow);
    }
    let mut bytes = Vec::with_capacity(body.len() + 1);
    bytes.push(selector);
    bytes.extend_from_slice(&body);
    Ok(bytes)
}

pub fn root_union<T: Ssz>(selector: u8, value: &T) -> Result<Node, CodecError> {
    let root = value.hash_tree_root()?;
    let mut word = [0; 32];
    word[0] = selector;
    Ok(hash_pair(&root, &word))
}
