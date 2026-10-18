use fast_ssz::scalar::{decode_bool, encode_bool, ScalarError};

#[test]
fn should_encode_boolean_using_exactly_one_canonical_byte() {
    assert_eq!(encode_bool(false), [0]);
    assert_eq!(encode_bool(true), [1]);
}

#[test]
fn should_accept_only_canonical_boolean_bytes() {
    for byte in 0..=u8::MAX {
        let expected = match byte {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(ScalarError::InvalidBoolean),
        };
        assert_eq!(decode_bool(&[byte]), expected);
    }
}

#[test]
fn should_reject_boolean_encodings_of_the_wrong_length() {
    assert_eq!(decode_bool(&[]), Err(ScalarError::InvalidLength));
    assert_eq!(decode_bool(&[0, 0]), Err(ScalarError::InvalidLength));
    assert_eq!(decode_bool(&[1, 0]), Err(ScalarError::InvalidLength));
}
