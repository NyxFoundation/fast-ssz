use nyx_ssz::bytes::{decode_progressive_byte_list, encode_progressive_byte_list, ByteError};

#[test]
fn should_borrow_every_byte_when_no_capacity_is_declared() {
    let bytes: Vec<u8> = (u8::MIN..=u8::MAX).collect();
    for result in [
        encode_progressive_byte_list(&bytes, None),
        decode_progressive_byte_list(&bytes, None),
    ] {
        let output = result.unwrap();
        assert_eq!(output, bytes);
        assert_eq!(output.as_ptr(), bytes.as_ptr());
    }
}

#[test]
fn should_accept_an_empty_progressive_list_when_the_capacity_is_zero_or_absent() {
    for limit in [None, Some(0), Some(usize::MAX)] {
        assert_eq!(encode_progressive_byte_list(&[], limit), Ok([].as_slice()));
        assert_eq!(decode_progressive_byte_list(&[], limit), Ok([].as_slice()));
    }
}

#[test]
fn should_enforce_declared_capacities_when_a_progressive_byte_list_is_bounded() {
    for count in 0..16 {
        let bytes = vec![0xab; count];
        for limit in 0..16 {
            let expected = if count <= limit {
                Ok(bytes.as_slice())
            } else {
                Err(ByteError::OverLimit)
            };
            assert_eq!(encode_progressive_byte_list(&bytes, Some(limit)), expected);
            assert_eq!(decode_progressive_byte_list(&bytes, Some(limit)), expected);
        }
    }
}

#[test]
fn should_accept_small_values_when_the_declared_capacity_is_the_machine_maximum() {
    let bytes = [0, 1, 127, 128, 255];
    assert_eq!(
        encode_progressive_byte_list(&bytes, Some(usize::MAX)),
        Ok(bytes.as_slice())
    );
    assert_eq!(
        decode_progressive_byte_list(&bytes, Some(usize::MAX)),
        Ok(bytes.as_slice())
    );
}
