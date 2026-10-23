//! Typed Vector/List codecs with owned partial decode state.

use crate::{
    codec::{decode_elements, decode_fixed, fixed_size, validate_type, SequenceDecodeState, Ssz},
    collection_tree::root_sequence,
    collections::{list, vector, LengthError, LengthErrorKind, List, Vector},
    error::{CodecError, DecodeFailure},
    sequence::{fixed_list_count, validate_fixed_vector, variable_list_view, variable_vector_view},
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

pub(crate) fn storage_failure<T: Ssz>(
    error: LengthError<T>,
) -> DecodeFailure<SequenceDecodeState<T>> {
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

fn decode_vector_values<T: Ssz>(
    input: &[u8],
    count: usize,
) -> Result<Vec<T>, DecodeFailure<SequenceDecodeState<T>>> {
    match fixed_size::<T>() {
        Ok(Some(width)) => {
            validate_fixed_vector(input.len(), width, count).map_err(empty_failure::<T>)?;
            decode_fixed(input, width, count)
        }
        Ok(None) => {
            let view = variable_vector_view(input, count).map_err(empty_failure::<T>)?;
            decode_elements(&view)
        }
        Err(CodecError::SizeOverflow) => {
            let kind = if input.len() as u128 >= 4_294_967_296 {
                CodecError::SizeOverflow
            } else {
                CodecError::InvalidLength
            };
            Err(empty_failure::<T>(kind))
        }
        Err(error) => Err(empty_failure::<T>(error)),
    }
}

pub(crate) fn decode_list_values<T: Ssz>(
    input: &[u8],
    limit: Option<usize>,
) -> Result<Vec<T>, DecodeFailure<SequenceDecodeState<T>>> {
    match fixed_size::<T>() {
        Ok(Some(width)) => {
            let count = fixed_list_count(input.len(), width, limit).map_err(empty_failure::<T>)?;
            decode_fixed(input, width, count)
        }
        Ok(None) => {
            let view = variable_list_view(input, limit).map_err(empty_failure::<T>)?;
            decode_elements(&view)
        }
        Err(CodecError::SizeOverflow) => {
            if input.len() as u128 >= 4_294_967_296 {
                return Err(empty_failure::<T>(CodecError::SizeOverflow));
            }
            if input.is_empty() {
                Ok(Vec::new())
            } else {
                Err(empty_failure::<T>(CodecError::ScopeUndivided))
            }
        }
        Err(error) => Err(empty_failure::<T>(error)),
    }
}

fn decode_vector<T: Ssz, const N: usize>(
    input: &[u8],
) -> Result<Vector<T, N>, DecodeFailure<SequenceDecodeState<T>>> {
    if let Err(kind) = vector_type::<T, N>() {
        return Err(empty_failure::<T>(kind));
    }
    let values = decode_vector_values::<T>(input, N)?;
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
    let values = decode_list_values::<T>(input, Some(MAX))?;
    match list(values) {
        Ok(value) => Ok(value),
        Err(error) => Err(storage_failure::<T>(error)),
    }
}

impl<T: Ssz, const N: usize> Ssz for Vector<T, N> {
    type DecodeState = SequenceDecodeState<T>;
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::Vector(T::TYPE, N);

    fn encoded_len(&self) -> Result<usize, CodecError> {
        vector_type::<T, N>()?;
        let values = self.as_slice();
        if values.len() != N {
            return Err(CodecError::InvalidLength);
        }
        crate::encoding::sequence_len(values)
    }

    fn encode_into(&self, output: &mut [u8]) -> Result<(), CodecError> {
        crate::encoding::check_length(output, self.encoded_len()?)?;
        crate::encoding::write_sequence(self.as_slice(), output)
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
