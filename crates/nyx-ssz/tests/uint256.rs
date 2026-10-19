use nyx_ssz::{
    scalar::{decode_u256, encode_u256, ScalarError},
    U256,
};

#[test]
fn should_preserve_all_limbs_when_encoding_uint256_in_little_endian_order() {
    let limbs = [
        0x0807_0605_0403_0201,
        0x100f_0e0d_0c0b_0a09,
        0x1817_1615_1413_1211,
        0x201f_1e1d_1c1b_1a19,
    ];
    let value = U256::from_limbs(limbs);
    let expected = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 30, 31, 32,
    ];
    assert_eq!(encode_u256(&value), expected);
    assert_eq!(decode_u256(&expected), Ok(value));
    assert_eq!(value.as_limbs(), &limbs);
}

#[test]
fn should_preserve_the_extreme_uint256_values_when_round_tripping() {
    assert_eq!(encode_u256(&U256::ZERO), [0; 32]);
    assert_eq!(encode_u256(&U256::MAX), [0xff; 32]);
    assert_eq!(decode_u256(&[0; 32]), Ok(U256::ZERO));
    assert_eq!(decode_u256(&[0xff; 32]), Ok(U256::MAX));
    let highest_bit = U256::from_limbs([0, 0, 0, 1 << 63]);
    let mut expected = [0; 32];
    expected[31] = 0x80;
    assert_eq!(encode_u256(&highest_bit), expected);
    assert_eq!(decode_u256(&expected), Ok(highest_bit));
}

#[test]
fn should_reject_uint256_when_the_input_has_any_other_length() {
    for length in (0..=33).chain([64, 128, 256]) {
        if length == 32 {
            continue;
        }
        assert_eq!(
            decode_u256(&vec![0; length]),
            Err(ScalarError::InvalidLength)
        );
    }
}
