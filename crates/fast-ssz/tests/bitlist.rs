use fast_ssz::bitfield::{decode_bit_list, encode_bit_list, BitfieldError};

#[test]
fn should_keep_the_delimiter_when_the_bitlist_is_empty() {
    assert_eq!(encode_bit_list(&[], 0), Ok(vec![1]));
    assert_eq!(decode_bit_list(&[1], 0), Ok(vec![]));
}

#[test]
fn should_place_the_delimiter_immediately_after_the_last_data_bit() {
    let bits = [true, false, true];
    assert_eq!(encode_bit_list(&bits, 3), Ok(vec![0x0d]));
    assert_eq!(decode_bit_list(&[0x0d], 3), Ok(bits.to_vec()));
    let full_byte = [true; 8];
    assert_eq!(encode_bit_list(&full_byte, 8), Ok(vec![0xff, 1]));
    assert_eq!(decode_bit_list(&[0xff, 1], 8), Ok(full_byte.to_vec()));
}

#[test]
fn should_distinguish_missing_delimiters_from_trailing_zero_bytes() {
    assert_eq!(decode_bit_list(&[], 8), Err(BitfieldError::EmptyEncoding));
    assert_eq!(decode_bit_list(&[0], 8), Err(BitfieldError::NoDelimiter));
    assert_eq!(decode_bit_list(&[0, 0], 8), Err(BitfieldError::NoDelimiter));
    assert_eq!(
        decode_bit_list(&[1, 0], 8),
        Err(BitfieldError::TrailingZeros)
    );
    assert_eq!(
        decode_bit_list(&[0, 1, 0], 8),
        Err(BitfieldError::TrailingZeros)
    );
}

#[test]
fn should_enforce_the_capacity_when_encoding_or_decoding_a_bitlist() {
    assert_eq!(encode_bit_list(&[false], 0), Err(BitfieldError::OverLimit));
    assert_eq!(decode_bit_list(&[2], 0), Err(BitfieldError::OverLimit));
    assert_eq!(decode_bit_list(&[0xff], 6), Err(BitfieldError::OverLimit));
    assert_eq!(
        decode_bit_list(&[0xff, 1], 7),
        Err(BitfieldError::OverLimit)
    );
}

#[test]
fn should_accept_every_nonzero_final_byte_as_a_unique_delimited_bitlist() {
    for byte in 1..=u8::MAX {
        let count = 7 - byte.leading_zeros() as usize;
        let bits: Vec<bool> = (0..count).map(|index| byte & (1 << index) != 0).collect();
        assert_eq!(decode_bit_list(&[byte], count), Ok(bits.clone()));
        assert_eq!(encode_bit_list(&bits, count), Ok(vec![byte]));
    }
}

#[test]
fn should_round_trip_bitlists_when_the_delimiter_crosses_a_byte_boundary() {
    for length in [0usize, 1, 7, 8, 9, 15, 16, 17, 255, 256, 257, 1024] {
        let bits: Vec<bool> = (0..length).map(|index| index % 3 == 0).collect();
        let encoded = encode_bit_list(&bits, usize::MAX).unwrap();
        assert_eq!(encoded.len(), length / 8 + 1);
        assert_eq!(decode_bit_list(&encoded, length), Ok(bits));
    }
}
