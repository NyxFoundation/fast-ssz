//! Owned packed bitfield dictionaries, with complete logical observations.
//!
//! Private stored bytes are canonically re-encoded rather than assumed valid in
//! the value law. Safe constructors and decoders only produce canonical storage.

use crate::{
    bit_storage,
    bitcollections::{BitList, BitVector, ProgressiveBitList},
    bitfield,
    codec::Ssz,
    error::{CodecError, DecodeFailure},
    tree_hash,
    type_info::TypeDescriptor,
};

impl<const N: usize> Ssz for BitVector<N> {
    type DecodeState = ();
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::BitVector(N);

    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        bit_storage::normalize_vector(self.as_ssz_bytes(), N)
    }

    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<()>> {
        match Self::from_ssz_bytes(bit_storage::copy_bytes(bytes)) {
            Ok(value) => Ok(value),
            Err(kind) => Err(DecodeFailure { kind, state: () }),
        }
    }

    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        let encoded = self.encode()?;
        tree_hash::hash_tree_root_byte_vector(&encoded, N.div_ceil(8))
    }
}

impl<const MAX: usize> Ssz for BitList<MAX> {
    type DecodeState = ();
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::BitList(MAX);

    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        bit_storage::normalize_list(self.as_ssz_bytes(), Some(MAX))
    }

    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<()>> {
        match Self::from_ssz_bytes(bit_storage::copy_bytes(bytes)) {
            Ok(value) => Ok(value),
            Err(kind) => Err(DecodeFailure { kind, state: () }),
        }
    }

    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        let encoded = self.encode()?;
        bit_storage::root_bounded_list(&encoded, MAX)
    }
}

impl Ssz for ProgressiveBitList {
    type DecodeState = ();
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::ProgressiveBitList(None);

    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        bit_storage::normalize_list(self.as_ssz_bytes(), None)
    }

    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<()>> {
        match Self::from_ssz_bytes(bit_storage::copy_bytes(bytes)) {
            Ok(value) => Ok(value),
            Err(kind) => Err(DecodeFailure { kind, state: () }),
        }
    }

    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        let encoded = self.encode()?;
        let view = match bitfield::decode_progressive_bit_list(&encoded, None) {
            Ok(view) => view,
            Err(error) => return Err(bit_storage::fault(error)),
        };
        tree_hash::hash_tree_root_progressive_bit_list_view(&view, None)
    }
}
