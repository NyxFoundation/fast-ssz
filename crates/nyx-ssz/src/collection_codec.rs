//! Typed Vector/List codecs with owned partial decode state.

use crate::{
    codec::{decode_elements, fixed_size, validate_type, SequenceDecodeState, Ssz},
    collection_tree::root_sequence,
    collection_wire::encode_sequence,
    collections::{list, vector, LengthError, LengthErrorKind, List, Vector},
    error::{CodecError, DecodeFailure},
    sequence::{
        fixed_list_view, fixed_vector_view, variable_list_view, variable_vector_view, SequenceView,
    },
    type_info::TypeDescriptor,
};

pub(crate) fn empty_failure<T: Ssz>(kind: CodecError) -> DecodeFailure<SequenceDecodeState<T>> {
    DecodeFailure {
        kind,
        state: SequenceDecodeState {
            values: Vec::new(),
            child: None,
        },
    }
}

fn storage_failure<T: Ssz>(error: LengthError<T>) -> DecodeFailure<SequenceDecodeState<T>> {
    let kind = match error.kind {
        LengthErrorKind::EmptyVector => CodecError::EmptyVector,
        LengthErrorKind::InvalidLength => CodecError::InvalidLength,
        LengthErrorKind::OverLimit => CodecError::OverLimit,
    };
    DecodeFailure {
        kind,
        state: SequenceDecodeState {
            values: error.values,
            child: None,
        },
    }
}

fn vector_type<T: Ssz, const N: usize>() -> Result<(), CodecError> {
    if N == 0 {
        return Err(CodecError::EmptyVector);
    }
    validate_type::<T>()
}

fn vector_layout<T: Ssz>(input: &[u8], count: usize) -> Result<SequenceView<'_>, CodecError> {
    match fixed_size::<T>() {
        Ok(Some(width)) => fixed_vector_view(input, width, count),
        Ok(None) => variable_vector_view(input, count),
        Err(CodecError::SizeOverflow) => {
            if input.len() as u128 >= 4_294_967_296 {
                Err(CodecError::SizeOverflow)
            } else {
                Err(CodecError::InvalidLength)
            }
        }
        Err(error) => Err(error),
    }
}

pub(crate) fn list_layout<T: Ssz>(
    input: &[u8],
    limit: Option<usize>,
) -> Result<SequenceView<'_>, CodecError> {
    match fixed_size::<T>() {
        Ok(Some(width)) => fixed_list_view(input, width, limit),
        Ok(None) => variable_list_view(input, limit),
        Err(CodecError::SizeOverflow) => {
            if input.len() as u128 >= 4_294_967_296 {
                return Err(CodecError::SizeOverflow);
            }
            if input.is_empty() {
                Ok(SequenceView {
                    input,
                    ranges: Vec::new(),
                })
            } else {
                Err(CodecError::ScopeUndivided)
            }
        }
        Err(error) => Err(error),
    }
}

fn decode_vector<T: Ssz, const N: usize>(
    input: &[u8],
) -> Result<Vector<T, N>, DecodeFailure<SequenceDecodeState<T>>> {
    if let Err(kind) = vector_type::<T, N>() {
        return Err(empty_failure::<T>(kind));
    }
    let view = match vector_layout::<T>(input, N) {
        Ok(view) => view,
        Err(kind) => return Err(empty_failure::<T>(kind)),
    };
    let values = decode_elements::<T>(&view)?;
    match vector(values) {
        Ok(value) => Ok(value),
        Err(error) => Err(storage_failure::<T>(error)),
    }
}

fn decode_list<T: Ssz, const MAX: usize>(
    input: &[u8],
) -> Result<List<T, MAX>, DecodeFailure<SequenceDecodeState<T>>> {
    if let Err(kind) = validate_type::<T>() {
        return Err(empty_failure::<T>(kind));
    }
    let view = match list_layout::<T>(input, Some(MAX)) {
        Ok(view) => view,
        Err(kind) => return Err(empty_failure::<T>(kind)),
    };
    let values = decode_elements::<T>(&view)?;
    match list(values) {
        Ok(value) => Ok(value),
        Err(error) => Err(storage_failure::<T>(error)),
    }
}

impl<T: Ssz, const N: usize> Ssz for Vector<T, N> {
    type DecodeState = SequenceDecodeState<T>;
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::Vector(T::TYPE, N);

    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        vector_type::<T, N>()?;
        let values = self.as_slice();
        if values.len() != N {
            return Err(CodecError::InvalidLength);
        }
        encode_sequence(values)
    }

    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>> {
        decode_vector(bytes)
    }

    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        vector_type::<T, N>()?;
        let values = self.as_slice();
        if values.len() != N {
            return Err(CodecError::InvalidLength);
        }
        root_sequence(values, N, false)
    }
}

impl<T: Ssz, const MAX: usize> Ssz for List<T, MAX> {
    type DecodeState = SequenceDecodeState<T>;
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::List(T::TYPE, MAX);

    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        validate_type::<T>()?;
        let values = self.as_slice();
        if values.len() > MAX {
            return Err(CodecError::OverLimit);
        }
        encode_sequence(values)
    }

    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>> {
        decode_list(bytes)
    }

    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        validate_type::<T>()?;
        let values = self.as_slice();
        if values.len() > MAX {
            return Err(CodecError::OverLimit);
        }
        root_sequence(values, MAX, true)
    }
}
