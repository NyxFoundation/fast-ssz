use nyx_ssz::{tree_hash, U256};

#[test]
fn should_store_a_boolean_in_the_first_byte_when_hashing_its_tree_root() {
    assert_eq!(tree_hash::hash_tree_root_bool(false), [0; 32]);
    let mut one = [0; 32];
    one[0] = 1;
    assert_eq!(tree_hash::hash_tree_root_bool(true), one);
}

macro_rules! check_unsigned_root {
    ($test:ident, $function:ident, $ty:ty, $width:literal) => {
        #[test]
        fn $test() {
            for value in [0 as $ty, 1, <$ty>::MAX / 3, <$ty>::MAX] {
                let root = tree_hash::$function(value);
                assert_eq!(&root[..$width], &value.to_le_bytes());
                assert!(root[$width..].iter().all(|byte| *byte == 0));
            }
        }
    };
}

check_unsigned_root!(should_zero_extend_uint8_roots, hash_tree_root_u8, u8, 1);
check_unsigned_root!(should_zero_extend_uint16_roots, hash_tree_root_u16, u16, 2);
check_unsigned_root!(should_zero_extend_uint32_roots, hash_tree_root_u32, u32, 4);
check_unsigned_root!(should_zero_extend_uint64_roots, hash_tree_root_u64, u64, 8);
check_unsigned_root!(
    should_zero_extend_uint128_roots,
    hash_tree_root_u128,
    u128,
    16
);

#[test]
fn should_preserve_little_endian_order_when_hashing_mixed_uint64_bits() {
    let root = tree_hash::hash_tree_root_u64(0x0807_0605_0403_0201);
    assert_eq!(&root[..8], &[1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(&root[8..], &[0; 24]);
}

#[test]
fn should_use_every_byte_of_a_uint256_as_its_tree_root() {
    let value = U256::from_limbs([
        0x0807_0605_0403_0201,
        0x100f_0e0d_0c0b_0a09,
        0x1817_1615_1413_1211,
        0x201f_1e1d_1c1b_1a19,
    ]);
    let expected: Vec<u8> = (1..=32).collect();
    assert_eq!(tree_hash::hash_tree_root_u256(&value).as_slice(), expected);
    assert_eq!(tree_hash::hash_tree_root_u256(&U256::ZERO), [0; 32]);
    assert_eq!(tree_hash::hash_tree_root_u256(&U256::MAX), [255; 32]);
}
