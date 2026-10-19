use fast_ssz::scalar::*;

macro_rules! integer_cases {
    ($test:ident, $ty:ty, $size:literal, $encode:ident, $decode:ident, $value:expr, $bytes:expr) => {
        #[test]
        fn $test() {
            let value: $ty = $value;
            let expected: [u8; $size] = $bytes;
            assert_eq!($encode(value), expected);
            assert_eq!($decode(&expected), Ok(value));
            assert_eq!($encode(0), [0; $size]);
            assert_eq!($encode(<$ty>::MAX), [0xff; $size]);
            assert_eq!($decode(&[0; $size]), Ok(0));
            assert_eq!($decode(&[0xff; $size]), Ok(<$ty>::MAX));
            for length in 0..=($size + 2) {
                if length == $size {
                    continue;
                }
                assert_eq!($decode(&vec![0; length]), Err(ScalarError::InvalidLength));
            }
        }
    };
}

integer_cases!(
    should_encode_and_decode_uint8_in_little_endian_order,
    u8,
    1,
    encode_u8,
    decode_u8,
    0xab,
    [0xab]
);
integer_cases!(
    should_encode_and_decode_uint16_in_little_endian_order,
    u16,
    2,
    encode_u16,
    decode_u16,
    0x0201,
    [1, 2]
);
integer_cases!(
    should_encode_and_decode_uint32_in_little_endian_order,
    u32,
    4,
    encode_u32,
    decode_u32,
    0x0403_0201,
    [1, 2, 3, 4]
);
integer_cases!(
    should_encode_and_decode_uint64_in_little_endian_order,
    u64,
    8,
    encode_u64,
    decode_u64,
    0x0807_0605_0403_0201,
    [1, 2, 3, 4, 5, 6, 7, 8]
);
integer_cases!(
    should_encode_and_decode_uint128_in_little_endian_order,
    u128,
    16,
    encode_u128,
    decode_u128,
    0x100f_0e0d_0c0b_0a09_0807_0605_0403_0201,
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
);
