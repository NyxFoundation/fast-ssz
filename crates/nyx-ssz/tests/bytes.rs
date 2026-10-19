use nyx_ssz::bytes::{
    decode_byte_list, decode_byte_vector, encode_byte_list, encode_byte_vector, ByteError,
};

#[test]
fn should_accept_exact_vector_lengths_without_copying() {
    for length in 1..128 {
        let data = vec![0xab; length];
        for result in [
            encode_byte_vector(&data, length),
            decode_byte_vector(&data, length),
        ] {
            let encoded = result.unwrap();
            assert_eq!(encoded, data);
            assert_eq!(encoded.as_ptr(), data.as_ptr());
        }
    }
}

#[test]
fn should_reject_empty_vector_declarations() {
    assert_eq!(encode_byte_vector(&[], 0), Err(ByteError::EmptyVector));
    assert_eq!(decode_byte_vector(&[1], 0), Err(ByteError::EmptyVector));
}

#[test]
fn should_reject_every_nonmatching_vector_length() {
    for actual in 0..16 {
        let data = vec![0; actual];
        for expected in 1..16 {
            if actual == expected {
                continue;
            }
            assert_eq!(
                decode_byte_vector(&data, expected),
                Err(ByteError::InvalidLength)
            );
            assert_eq!(
                encode_byte_vector(&data, expected),
                Err(ByteError::InvalidLength)
            );
        }
    }
}

#[test]
fn should_accept_byte_lists_up_to_and_including_the_limit() {
    for actual in 0..16 {
        let data = vec![0xff; actual];
        for limit in 0..16 {
            let expected = if actual <= limit {
                Ok(data.as_slice())
            } else {
                Err(ByteError::OverLimit)
            };
            assert_eq!(decode_byte_list(&data, limit), expected);
            assert_eq!(encode_byte_list(&data, limit), expected);
        }
    }
}

#[test]
fn should_handle_machine_size_limits_without_overflow() {
    assert_eq!(decode_byte_list(&[], usize::MAX), Ok([].as_slice()));
    assert_eq!(
        decode_byte_vector(&[], usize::MAX),
        Err(ByteError::InvalidLength)
    );
}
