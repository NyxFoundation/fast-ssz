//! Immutable owned SSZ bitfields backed by canonical packed byte allocations.
//!
//! Constructors validate wire bytes without expanding them into Boolean arrays.
//! Progressive bit counts use u128 so packed byte counts are never narrowed.

use crate::{bit_storage, bitfield, error::CodecError};

/// Exactly `N > 0` bits in low-bit-first canonical bytes.
pub struct BitVector<const N: usize> {
    encoded: Vec<u8>,
    _bound: [(); N],
}

impl<const N: usize> BitVector<N> {
    /// Move a canonical encoding into owned storage without copying its allocation.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn from_ssz_bytes(encoded: Vec<u8>) -> Result<Self, CodecError> {
        bit_storage::validate_vector(&encoded, N)?;
        Ok(Self {
            encoded,
            _bound: [(); N],
        })
    }

    /// Pack exactly N logical bits and validate the declaration.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn from_bits(bits: &[bool]) -> Result<Self, CodecError> {
        let encoded = bitfield::encode_bit_vector(bits, N).map_err(bit_storage::fault)?;
        Self::from_ssz_bytes(encoded)
    }

    /// Borrow the canonical encoding without expanding the logical bits.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn as_ssz_bytes(&self) -> &[u8] {
        &self.encoded
    }

    /// Return the bit count fixed by the type declaration.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn len_bits(&self) -> u128 {
        N as u128
    }

    /// Read one logical bit; padding and out-of-range indices are not elements.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn get(&self, index: u128) -> Option<bool> {
        if index >= N as u128 {
            return None;
        }
        bit_storage::get_bit(&self.encoded, index)
    }
}

/// At most MAX logical bits, with a delimiter retained in the owned encoding.
pub struct BitList<const MAX: usize> {
    encoded: Vec<u8>,
    _bound: [(); MAX],
}

impl<const MAX: usize> BitList<MAX> {
    /// Move a canonical delimited encoding into storage, checking its capacity.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn from_ssz_bytes(encoded: Vec<u8>) -> Result<Self, CodecError> {
        bit_storage::validate_list(&encoded, Some(MAX))?;
        Ok(Self {
            encoded,
            _bound: [(); MAX],
        })
    }

    /// Pack logical bits and append their mandatory delimiter.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn from_bits(bits: &[bool]) -> Result<Self, CodecError> {
        let encoded = bitfield::encode_bit_list(bits, MAX).map_err(bit_storage::fault)?;
        Self::from_ssz_bytes(encoded)
    }

    /// Borrow the canonical encoding, including the delimiter.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn as_ssz_bytes(&self) -> &[u8] {
        &self.encoded
    }

    /// Return the logical count, excluding the delimiter.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn len_bits(&self) -> u128 {
        bit_storage::delimited_len(&self.encoded)
    }

    /// Read one logical bit, never its delimiter or padding.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn get(&self, index: u128) -> Option<bool> {
        bit_storage::get_list_bit(&self.encoded, index)
    }
}

/// An unbounded Progressive bitlist retaining its packed, delimited encoding.
pub struct ProgressiveBitList {
    encoded: Vec<u8>,
}

impl ProgressiveBitList {
    /// Move canonical bytes into storage without a Boolean expansion or bound.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn from_ssz_bytes(encoded: Vec<u8>) -> Result<Self, CodecError> {
        bit_storage::validate_list(&encoded, None)?;
        Ok(Self { encoded })
    }

    /// Pack logical bits using the canonical unbounded declaration.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn from_bits(bits: &[bool]) -> Result<Self, CodecError> {
        let encoded =
            bitfield::encode_progressive_bit_list(bits, None).map_err(bit_storage::fault)?;
        Self::from_ssz_bytes(encoded)
    }

    /// Borrow canonical bytes, retaining the delimiter without copying.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn as_ssz_bytes(&self) -> &[u8] {
        &self.encoded
    }

    /// Return the complete logical count, which can exceed usize::MAX.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn len_bits(&self) -> u128 {
        bit_storage::delimited_len(&self.encoded)
    }

    /// Read a logical bit without narrowing a wide index before its bounds check.
    #[cfg_attr(feature = "verification", verify::start_from)]
    pub fn get(&self, index: u128) -> Option<bool> {
        bit_storage::get_list_bit(&self.encoded, index)
    }
}

impl<const N: usize> std::fmt::Debug for BitVector<N> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("BitVector")
            .field("encoded", &self.encoded)
            .finish()
    }
}

impl<const MAX: usize> std::fmt::Debug for BitList<MAX> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("BitList")
            .field("encoded", &self.encoded)
            .finish()
    }
}

impl std::fmt::Debug for ProgressiveBitList {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ProgressiveBitList")
            .field("encoded", &self.encoded)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{codec::Ssz, tree_hash};

    #[test]
    fn should_preserve_type_and_count_faults_when_symbolic_storage_violates_its_declaration() {
        let empty = BitVector::<0> {
            encoded: vec![],
            _bound: [],
        };
        assert_eq!(empty.encode(), Err(CodecError::EmptyVector));
        assert_eq!(empty.hash_tree_root(), Err(CodecError::EmptyVector));
        let wrong = BitVector::<9> {
            encoded: vec![],
            _bound: [(); 9],
        };
        assert_eq!(wrong.encode(), Err(CodecError::InvalidLength));
        assert_eq!(wrong.hash_tree_root(), Err(CodecError::InvalidLength));
        assert_eq!(wrong.get(0), None);
        let excessive = BitList::<7> {
            encoded: vec![255, 1],
            _bound: [(); 7],
        };
        assert_eq!(excessive.encode(), Err(CodecError::OverLimit));
        assert_eq!(excessive.hash_tree_root(), Err(CodecError::OverLimit));
        let unbounded = ProgressiveBitList { encoded: vec![] };
        assert_eq!(unbounded.encode(), Ok(vec![1]));
        assert_eq!(
            unbounded.hash_tree_root(),
            tree_hash::hash_tree_root_progressive_bit_list(&[], None)
        );
    }

    #[test]
    fn should_encode_logical_values_when_symbolic_private_storage_is_not_canonical() {
        let vector = BitVector::<3> {
            encoded: vec![255],
            _bound: [(); 3],
        };
        assert_eq!(vector.encode(), Ok(vec![7]));
        assert_eq!(
            vector.hash_tree_root(),
            tree_hash::hash_tree_root_bit_vector(&[true; 3], 3)
        );
        let empty = BitList::<8> {
            encoded: vec![],
            _bound: [(); 8],
        };
        assert_eq!(empty.encode(), Ok(vec![1]));
        assert_eq!(
            empty.hash_tree_root(),
            tree_hash::hash_tree_root_bit_list(&[], 8)
        );
        let bounded = BitList::<8> {
            encoded: vec![255, 0],
            _bound: [(); 8],
        };
        assert_eq!(bounded.encode(), Ok(vec![255, 1]));
        assert_eq!(
            bounded.hash_tree_root(),
            tree_hash::hash_tree_root_bit_list(&[true; 8], 8)
        );
        let progressive = ProgressiveBitList {
            encoded: vec![255, 0],
        };
        assert_eq!(progressive.encode(), Ok(vec![255, 1]));
        assert_eq!(
            progressive.hash_tree_root(),
            tree_hash::hash_tree_root_progressive_bit_list(&[true; 8], None)
        );
    }
}
