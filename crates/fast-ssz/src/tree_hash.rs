//! SSZ tree roots of basic values, with canonical little-endian zero padding.

fn scalar_chunk<const N: usize>(encoded: [u8; N]) -> [u8; 32] {
    let mut root = [0; 32];
    root[..N].copy_from_slice(&encoded);
    root
}

/// Compute an SSZ boolean's root: its encoding followed by 31 zero bytes.
pub fn hash_tree_root_bool(value: bool) -> [u8; 32] {
    scalar_chunk(crate::scalar::encode_bool(value))
}

macro_rules! integer_root {
    ($ty:ty, $function:ident, $encode:ident) => {
        #[doc = concat!("Compute an SSZ `", stringify!($ty), "` root with little-endian zero padding.")]
        pub fn $function(value: $ty) -> [u8; 32] {
            scalar_chunk(crate::scalar::$encode(value))
        }
    };
}

integer_root!(u8, hash_tree_root_u8, encode_u8);
integer_root!(u16, hash_tree_root_u16, encode_u16);
integer_root!(u32, hash_tree_root_u32, encode_u32);
integer_root!(u64, hash_tree_root_u64, encode_u64);
integer_root!(u128, hash_tree_root_u128, encode_u128);

/// Compute an SSZ uint256's root: exactly its 32-byte little-endian encoding.
pub fn hash_tree_root_u256(value: &crate::U256) -> [u8; 32] {
    crate::scalar::encode_u256(value)
}
