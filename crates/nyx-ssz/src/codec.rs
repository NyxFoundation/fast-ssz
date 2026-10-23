//! Typed SSZ codecs. External implementations require their own correctness proof.

use crate::{
    error::{CodecError, DecodeFailure},
    scalar, tree_hash,
    type_info::{self, TypeDescriptor},
    U256,
};

/// An owned SSZ type with canonical encoding, decoding and tree hashing.
///
/// Native conformance tests and formal proof coverage are tracked separately.
/// Implementing or deriving this trait does not automatically certify its laws.
pub trait Ssz: Sized {
    /// Owned partial values returned on failure; never discarded inside decode.
    type DecodeState;
    /// Immutable declaration used for type validation and layout metadata.
    const TYPE: &'static TypeDescriptor;
    /// Exact reference bytes, its protocol error, or `NativeOutputOverflow` iff
    /// successful natural reference bytes have length greater than `usize::MAX`.
    /// Representable successes cannot use the native refusal; protocol faults
    /// retain their distinct errors and precedence, including through parents.
    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        let mut output = vec![0; self.encoded_len()?];
        self.encode_into(&mut output)?;
        Ok(output)
    }
    /// Exact encoded size, including complete value validation and error precedence.
    /// Must agree with encode_into; native unrepresentability is not a protocol fault.
    fn encoded_len(&self) -> Result<usize, CodecError>;
    /// Write canonical bytes into an exactly sized destination without scratch allocation.
    /// Wrong destination length is rejected before writing. Other failures may leave
    /// partial writes; callers must discard the destination on error.
    fn encode_into(&self, output: &mut [u8]) -> Result<(), CodecError>;
    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>>;
    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError>;
}

/// Return a fixed width, variable layout (`Ok(None)`), or size overflow.
pub fn fixed_size<T: Ssz>() -> Result<Option<usize>, CodecError> {
    type_info::fixed_size(T::TYPE)
}

/// Whether declared values pack together before collection Merkleization.
pub fn is_basic<T: Ssz>() -> bool {
    type_info::is_basic(T::TYPE)
}

/// Compare declared Merkle layouts; compatibility does not imply type validity.
pub fn is_compatible<Left: Ssz, Right: Ssz>() -> bool {
    type_info::is_compatible(Left::TYPE, Right::TYPE)
}

/// Check a type declaration without invoking any value codec.
pub fn validate_type<T: Ssz>() -> Result<(), CodecError> {
    type_info::validate(T::TYPE)
}

/// Encode a typed value using its codec.
pub fn encode<T: Ssz>(value: &T) -> Result<Vec<u8>, CodecError> {
    value.encode()
}

/// Decode a typed value, returning ownership of partial state on failure.
pub fn decode<T: Ssz>(bytes: &[u8]) -> Result<T, DecodeFailure<T::DecodeState>> {
    T::decode(bytes)
}

/// Owned values retained when a sequence element refuses its byte range.
pub struct SequenceDecodeState<T: Ssz> {
    pub values: Vec<T>,
    pub child: Option<T::DecodeState>,
}

/// Decode validated body ranges, retaining every completed value on failure.
///
/// The view validates layout, not the element type declaration. Each element
/// codec validates its own value; an empty view invokes no element codecs.
pub fn decode_elements<T: Ssz>(
    view: &crate::sequence::SequenceView<'_>,
) -> Result<Vec<T>, DecodeFailure<SequenceDecodeState<T>>> {
    decode_ranges(view.input, &view.ranges)
}

fn decode_ranges<T: Ssz>(
    input: &[u8],
    ranges: &[crate::sequence::BodyRange],
) -> Result<Vec<T>, DecodeFailure<SequenceDecodeState<T>>> {
    let mut values = Vec::new();
    let mut index = 0;
    while index < ranges.len() {
        let range = &ranges[index];
        let value = match decode_range::<T>(input, range.start, range.end) {
            Ok(value) => value,
            Err(failure) => return Err(sequence_failure(values, failure)),
        };
        values.push(value);
        index += 1;
    }
    Ok(values)
}

/// Decode a prevalidated fixed layout without allocating an element-range table.
pub(crate) fn decode_fixed<T: Ssz>(
    input: &[u8],
    width: usize,
    count: usize,
) -> Result<Vec<T>, DecodeFailure<SequenceDecodeState<T>>> {
    let mut values = Vec::new();
    for index in 0..count {
        let start = index * width;
        let value = match decode_range::<T>(input, start, start + width) {
            Ok(value) => value,
            Err(failure) => return Err(sequence_failure(values, failure)),
        };
        // Capacity is only a hint: a larger Rust representation must not make
        // an early child error panic by reserving the entire potential result.
        // Never allocate before first-child success or restrict the decode count.
        if index == 0 {
            let capacity = count.min(input.len() / core::mem::size_of::<T>().max(1));
            values.reserve_exact(capacity);
        }
        values.push(value);
    }
    Ok(values)
}

fn sequence_failure<T: Ssz>(
    values: Vec<T>,
    failure: DecodeFailure<T::DecodeState>,
) -> DecodeFailure<SequenceDecodeState<T>> {
    DecodeFailure {
        kind: failure.kind,
        state: SequenceDecodeState {
            values,
            child: Some(failure.state),
        },
    }
}

fn decode_range<T: Ssz>(
    input: &[u8],
    start: usize,
    end: usize,
) -> Result<T, DecodeFailure<T::DecodeState>> {
    T::decode(&input[start..end])
}

/// Compute a typed value's SSZ root using its codec.
pub fn hash_tree_root<T: Ssz>(value: &T) -> Result<[u8; 32], CodecError> {
    value.hash_tree_root()
}

fn scalar_error(error: scalar::ScalarError) -> CodecError {
    match error {
        scalar::ScalarError::InvalidLength => CodecError::InvalidLength,
        scalar::ScalarError::InvalidBoolean => CodecError::InvalidBoolean,
    }
}

macro_rules! basic_codec {
    ($type:ty, $declaration:expr, $encode:ident, $decode:ident, $root:ident) => {
        impl Ssz for $type {
            type DecodeState = ();
            const TYPE: &'static TypeDescriptor = &$declaration;

            fn encoded_len(&self) -> Result<usize, CodecError> {
                Ok(core::mem::size_of::<$type>())
            }

            fn encode_into(&self, output: &mut [u8]) -> Result<(), CodecError> {
                crate::encoding::copy(output, &scalar::$encode(*self))
            }

            fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>> {
                match scalar::$decode(bytes) {
                    Ok(value) => Ok(value),
                    Err(error) => Err(DecodeFailure {
                        kind: scalar_error(error),
                        state: (),
                    }),
                }
            }

            fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
                Ok(tree_hash::$root(*self))
            }
        }
    };
}

basic_codec!(
    bool,
    TypeDescriptor::Boolean,
    encode_bool,
    decode_bool,
    hash_tree_root_bool
);
basic_codec!(
    u8,
    TypeDescriptor::Uint(1),
    encode_u8,
    decode_u8,
    hash_tree_root_u8
);
basic_codec!(
    u16,
    TypeDescriptor::Uint(2),
    encode_u16,
    decode_u16,
    hash_tree_root_u16
);
basic_codec!(
    u32,
    TypeDescriptor::Uint(4),
    encode_u32,
    decode_u32,
    hash_tree_root_u32
);
basic_codec!(
    u64,
    TypeDescriptor::Uint(8),
    encode_u64,
    decode_u64,
    hash_tree_root_u64
);
basic_codec!(
    u128,
    TypeDescriptor::Uint(16),
    encode_u128,
    decode_u128,
    hash_tree_root_u128
);

impl Ssz for U256 {
    type DecodeState = ();
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::Uint(32);

    fn encoded_len(&self) -> Result<usize, CodecError> {
        Ok(32)
    }

    fn encode_into(&self, output: &mut [u8]) -> Result<(), CodecError> {
        crate::encoding::copy(output, &scalar::encode_u256(self))
    }

    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>> {
        match scalar::decode_u256(bytes) {
            Ok(value) => Ok(value),
            Err(error) => Err(DecodeFailure {
                kind: scalar_error(error),
                state: (),
            }),
        }
    }

    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
        Ok(tree_hash::hash_tree_root_u256(self))
    }
}
