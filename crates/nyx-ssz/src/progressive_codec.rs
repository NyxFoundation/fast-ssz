//! Progressive-list codecs with exact optional bounds and owned failure state.

use crate::{
    codec::{decode_elements, validate_type, SequenceDecodeState, Ssz},
    collection_codec::{empty_failure, list_layout, storage_failure},
    collection_tree::root_progressive_sequence,
    collections::{
        bounded_progressive_list, progressive_list, BoundedProgressiveList, ProgressiveList,
    },
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

fn decode_bounded_progressive<T: Ssz, const MAX: usize>(
    input: &[u8],
) -> Result<BoundedProgressiveList<T, MAX>, DecodeFailure<SequenceDecodeState<T>>> {
    if let Err(kind) = validate_type::<T>() {
        return Err(empty_failure::<T>(kind));
    }
    let view = match list_layout::<T>(input, Some(MAX)) {
        Ok(view) => view,
        Err(kind) => return Err(empty_failure::<T>(kind)),
    };
    let values = decode_elements::<T>(&view)?;
    match bounded_progressive_list(values) {
        Ok(value) => Ok(value),
        Err(error) => Err(storage_failure::<T>(error)),
    }
}

impl<T: Ssz, const MAX: usize> Ssz for BoundedProgressiveList<T, MAX> {
    type DecodeState = SequenceDecodeState<T>;
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::ProgressiveList(T::TYPE, Some(MAX));

    fn encoded_len(&self) -> Result<usize, CodecError> {
        validate_type::<T>()?;
        let values = self.as_slice();
        if values.len() > MAX {
            return Err(CodecError::OverLimit);
        }
        crate::encoding::sequence_len(values)
    }

    fn encode_into(&self, output: &mut [u8]) -> Result<(), CodecError> {
        crate::encoding::check_length(output, self.encoded_len()?)?;
        crate::encoding::write_sequence(self.as_slice(), output)
    }

    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>> {
        decode_bounded_progressive(bytes)
    }

    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        validate_type::<T>()?;
        // The pinned Progressive root ignores the context cap, even on private states.
        root_progressive_sequence(self.as_slice())
    }
}

impl<T: Ssz> Ssz for ProgressiveList<T> {
    type DecodeState = SequenceDecodeState<T>;
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::ProgressiveList(T::TYPE, None);

    fn encoded_len(&self) -> Result<usize, CodecError> {
        validate_type::<T>()?;
        crate::encoding::sequence_len(self.as_slice())
    }

    fn encode_into(&self, output: &mut [u8]) -> Result<(), CodecError> {
        crate::encoding::check_length(output, self.encoded_len()?)?;
        crate::encoding::write_sequence(self.as_slice(), output)
    }

    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>> {
        decode_progressive(bytes)
    }

    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        validate_type::<T>()?;
        root_progressive_sequence(self.as_slice())
    }
}
