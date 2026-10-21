//! Canonical unbounded Progressive-list codecs and their owned failure state.

use crate::{
    codec::{decode_elements, validate_type, SequenceDecodeState, Ssz},
    collection_codec::{empty_failure, list_layout},
    collection_tree::root_progressive_sequence,
    collection_wire::encode_sequence,
    collections::{progressive_list, ProgressiveList},
    error::{CodecError, DecodeFailure},
    type_info::TypeDescriptor,
};

fn decode_progressive<T: Ssz>(
    input: &[u8],
) -> Result<ProgressiveList<T>, DecodeFailure<SequenceDecodeState<T>>> {
    if let Err(kind) = validate_type::<T>() {
        return Err(empty_failure::<T>(kind));
    }
    let view = match list_layout::<T>(input, None) {
        Ok(view) => view,
        Err(kind) => return Err(empty_failure::<T>(kind)),
    };
    let values = decode_elements::<T>(&view)?;
    Ok(progressive_list(values))
}

impl<T: Ssz> Ssz for ProgressiveList<T> {
    type DecodeState = SequenceDecodeState<T>;
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::ProgressiveList(T::TYPE, None);

    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        validate_type::<T>()?;
        encode_sequence(self.as_slice())
    }

    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>> {
        decode_progressive(bytes)
    }

    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        validate_type::<T>()?;
        root_progressive_sequence(self.as_slice())
    }
}
