//! Owned opaque SSZ byte arrays, distinct from generic uint8 sequences.
//!
//! Constructors retain accepted allocations. Private storage prevents resizing;
//! the unit-array markers preserve const bounds during generic extraction only.

use crate::{
    bytes::{self, ByteError},
    codec::Ssz,
    error::{CodecError, DecodeFailure},
    tree_hash,
    type_info::TypeDescriptor,
};

/// Exactly `N` bytes; zero-length vector declarations are invalid.
pub struct ByteVector<const N: usize> {
    bytes: Vec<u8>,
    _bound: [(); N],
}

/// At most `MAX` bytes, including empty values and zero capacity.
pub struct ByteList<const MAX: usize> {
    bytes: Vec<u8>,
    _bound: [(); MAX],
}

fn byte_error(error: ByteError) -> CodecError {
    match error {
        ByteError::EmptyVector => CodecError::EmptyVector,
        ByteError::InvalidLength => CodecError::InvalidLength,
        ByteError::OverLimit => CodecError::OverLimit,
        ByteError::OffsetOverflow => CodecError::SizeOverflow,
    }
}

fn copy_bytes(bytes: &[u8]) -> Vec<u8> {
    bytes.to_vec()
}

impl<const N: usize> ByteVector<N> {
    /// Validate the declaration and exact length, moving accepted storage unchanged.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn from_bytes(bytes: Vec<u8>) -> Result<Self, CodecError> {
        match bytes::encode_byte_vector(&bytes, N) {
            Ok(_) => Ok(Self {
                bytes,
                _bound: [(); N],
            }),
            Err(error) => Err(byte_error(error)),
        }
    }

    /// Borrow every byte in its original order without changing the allocation.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

impl<const MAX: usize> ByteList<MAX> {
    /// Validate the upper bound, moving accepted storage unchanged.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn from_bytes(bytes: Vec<u8>) -> Result<Self, CodecError> {
        match bytes::encode_byte_list(&bytes, MAX) {
            Ok(_) => Ok(Self {
                bytes,
                _bound: [(); MAX],
            }),
            Err(error) => Err(byte_error(error)),
        }
    }

    /// Borrow every byte in its original order without changing the allocation.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

// Do not format the zero-sized marker: its logical length can be usize::MAX.
impl<const N: usize> std::fmt::Debug for ByteVector<N> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ByteVector")
            .field("bytes", &self.bytes)
            .finish()
    }
}

impl<const MAX: usize> std::fmt::Debug for ByteList<MAX> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ByteList")
            .field("bytes", &self.bytes)
            .finish()
    }
}

mod ssz {
    use super::*;

    impl<const N: usize> Ssz for ByteVector<N> {
        type DecodeState = ();
        const TYPE: &'static TypeDescriptor = &TypeDescriptor::ByteVector(N);

        fn encoded_len(&self) -> Result<usize, CodecError> {
            bytes::encode_byte_vector(self.as_bytes(), N)
                .map(|bytes| bytes.len())
                .map_err(byte_error)
        }
        fn encode_into(&self, output: &mut [u8]) -> Result<(), CodecError> {
            let bytes = bytes::encode_byte_vector(self.as_bytes(), N).map_err(byte_error)?;
            crate::encoding::copy(output, bytes)
        }

        fn decode(input: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>> {
            match bytes::decode_byte_vector(input, N) {
                Ok(bytes) => Ok(Self {
                    bytes: copy_bytes(bytes),
                    _bound: [(); N],
                }),
                Err(error) => Err(DecodeFailure {
                    kind: byte_error(error),
                    state: (),
                }),
            }
        }

        fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
            tree_hash::hash_tree_root_byte_vector(self.as_bytes(), N)
        }
    }

    impl<const MAX: usize> Ssz for ByteList<MAX> {
        type DecodeState = ();
        const TYPE: &'static TypeDescriptor = &TypeDescriptor::ByteList(MAX);

        fn encoded_len(&self) -> Result<usize, CodecError> {
            bytes::encode_byte_list(self.as_bytes(), MAX)
                .map(|bytes| bytes.len())
                .map_err(byte_error)
        }
        fn encode_into(&self, output: &mut [u8]) -> Result<(), CodecError> {
            let bytes = bytes::encode_byte_list(self.as_bytes(), MAX).map_err(byte_error)?;
            crate::encoding::copy(output, bytes)
        }

        fn decode(input: &[u8]) -> Result<Self, DecodeFailure<Self::DecodeState>> {
            match bytes::decode_byte_list(input, MAX) {
                Ok(bytes) => Ok(Self {
                    bytes: copy_bytes(bytes),
                    _bound: [(); MAX],
                }),
                Err(error) => Err(DecodeFailure {
                    kind: byte_error(error),
                    state: (),
                }),
            }
        }

        fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> {
            tree_hash::hash_tree_root_byte_list(self.as_bytes(), MAX)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn codecs_defensively_check_private_storage_and_declarations() {
        let zero = ByteVector::<0> {
            bytes: vec![],
            _bound: [],
        };
        assert_eq!(zero.encode(), Err(CodecError::EmptyVector));
        assert_eq!(zero.hash_tree_root(), Err(CodecError::EmptyVector));
        let short = ByteVector::<2> {
            bytes: vec![1],
            _bound: [(); 2],
        };
        assert_eq!(short.encode(), Err(CodecError::InvalidLength));
        assert_eq!(short.hash_tree_root(), Err(CodecError::InvalidLength));
        let over = ByteList::<0> {
            bytes: vec![1],
            _bound: [],
        };
        assert_eq!(over.encode(), Err(CodecError::OverLimit));
        assert_eq!(over.hash_tree_root(), Err(CodecError::OverLimit));
        assert_eq!(
            byte_error(ByteError::OffsetOverflow),
            CodecError::SizeOverflow
        );
    }

    #[test]
    fn formatting_never_expands_machine_maximum_markers() {
        let value = ByteVector::<{ usize::MAX }> {
            bytes: vec![],
            _bound: [(); usize::MAX],
        };
        assert_eq!(format!("{value:?}"), "ByteVector { bytes: [] }");
        assert_eq!(
            format!(
                "{:?}",
                ByteList::<{ usize::MAX }>::from_bytes(vec![]).unwrap()
            ),
            "ByteList { bytes: [] }"
        );
    }
}
