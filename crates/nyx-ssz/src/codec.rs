//! Typed SSZ codecs. External implementations require their own correctness proof.

use crate::{
    error::{CodecError, DecodeFailure},
    scalar, tree_hash, U256,
};

/// An owned SSZ type with canonical encoding, decoding and tree hashing.
///
/// The library proves its own implementations. Implementing this trait outside
/// this crate does not automatically establish SSZ conformance.
pub trait Ssz: Sized {
    /// Owned partial values returned on failure; never discarded inside decode.
    type DecodeState;
    /// A fixed width, variable layout (`Ok(None)`), or an unrepresentable width.
    const FIXED_SIZE: Result<Option<usize>, CodecError>;
    /// Basic values pack together before collection Merkleization.
    const IS_BASIC: bool;
    fn encode(&self) -> Result<Vec<u8>, CodecError>;
    fn decode(bytes: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>>;
    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError>;
}

/// Encode a typed value using its codec.
pub fn encode<T: Ssz>(value: &T) -> Result<Vec<u8>, CodecError> {
    value.encode()
}

/// Decode a typed value, returning ownership of partial state on failure.
pub fn decode<T: Ssz>(bytes: &[u8]) -> Result<T, DecodeFailure<T::DecodeState>> {
    T::decode(bytes)
}

/// Compute a typed value's SSZ root using its codec.
pub fn hash_tree_root<T: Ssz>(value: &T) -> Result<[u8; 32], CodecError> {
    value.hash_tree_root()
}

fn fixed_bytes<const N: usize>(input: [u8; N]) -> Vec<u8> {
    let mut output = Vec::new();
    let mut index = 0;
    while index < N {
        output.push(input[index]);
        index += 1;
    }
    output
}

fn scalar_error(error: scalar::ScalarError) -> CodecError {
    match error {
        scalar::ScalarError::InvalidLength => CodecError::InvalidLength,
        scalar::ScalarError::InvalidBoolean => CodecError::InvalidBoolean,
    }
}

macro_rules! basic_codec {
    ($type:ty, $size:literal, $encode:ident, $decode:ident, $root:ident) => {
        impl Ssz for $type {
            type DecodeState = ();
            const FIXED_SIZE: Result<Option<usize>, CodecError> = Ok(Some($size));
            const IS_BASIC: bool = true;

            fn encode(&self) -> Result<Vec<u8>, CodecError> {
                Ok(fixed_bytes(scalar::$encode(*self)))
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

basic_codec!(bool, 1, encode_bool, decode_bool, hash_tree_root_bool);
basic_codec!(u8, 1, encode_u8, decode_u8, hash_tree_root_u8);
basic_codec!(u16, 2, encode_u16, decode_u16, hash_tree_root_u16);
basic_codec!(u32, 4, encode_u32, decode_u32, hash_tree_root_u32);
basic_codec!(u64, 8, encode_u64, decode_u64, hash_tree_root_u64);
basic_codec!(u128, 16, encode_u128, decode_u128, hash_tree_root_u128);

impl Ssz for U256 {
    type DecodeState = ();
    const FIXED_SIZE: Result<Option<usize>, CodecError> = Ok(Some(32));
    const IS_BASIC: bool = true;

    fn encode(&self) -> Result<Vec<u8>, CodecError> {
        Ok(fixed_bytes(scalar::encode_u256(self)))
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
