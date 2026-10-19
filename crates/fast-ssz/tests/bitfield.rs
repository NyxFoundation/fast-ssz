use fast_ssz::bitfield::{decode_bit_vector, encode_bit_vector, BitfieldError};

#[test]
fn should_pack_bits_lowest_first_when_the_vector_has_partial_final_bytes() {
    let bits = [true, false, true, true, false, false, false, true, true];
    assert_eq!(encode_bit_vector(&bits, 9), Ok(vec![0x8d, 0x01]));
    assert_eq!(decode_bit_vector(&[0x8d, 0x01], 9), Ok(bits.to_vec()));
}

#[test]
fn should_preserve_every_byte_when_the_vector_has_no_padding() {
    for byte in 0..=u8::MAX {
        let expected: Vec<bool> = (0..8).map(|index| byte & (1 << index) != 0).collect();
        assert_eq!(decode_bit_vector(&[byte], 8), Ok(expected.clone()));
        assert_eq!(encode_bit_vector(&expected, 8), Ok(vec![byte]));
    }
}

#[test]
fn should_reject_only_high_padding_bits_when_a_vector_is_not_byte_aligned() {
    for length in 1..8 {
        for byte in 0..=u8::MAX {
            let actual = decode_bit_vector(&[byte], length);
            if (byte as usize) >= 1 << length {
                assert_eq!(actual, Err(BitfieldError::PaddingBits));
                continue;
            }
            let bits: Vec<bool> = (0..length).map(|index| byte & (1 << index) != 0).collect();
            assert_eq!(actual, Ok(bits.clone()));
            assert_eq!(encode_bit_vector(&bits, length), Ok(vec![byte]));
        }
    }
}

#[test]
fn should_reject_empty_bitvector_declarations_before_reading_the_value() {
    assert_eq!(encode_bit_vector(&[], 0), Err(BitfieldError::EmptyVector));
    assert_eq!(
        encode_bit_vector(&[true], 0),
        Err(BitfieldError::EmptyVector)
    );
    assert_eq!(decode_bit_vector(&[], 0), Err(BitfieldError::EmptyVector));
    assert_eq!(decode_bit_vector(&[0], 0), Err(BitfieldError::EmptyVector));
}

#[test]
fn should_reject_wrong_bitvector_lengths_without_overflowing_machine_counts() {
    assert_eq!(
        encode_bit_vector(&[true], 2),
        Err(BitfieldError::InvalidLength)
    );
    assert_eq!(decode_bit_vector(&[], 1), Err(BitfieldError::InvalidLength));
    assert_eq!(
        decode_bit_vector(&[0, 0], 8),
        Err(BitfieldError::InvalidLength)
    );
    assert_eq!(
        decode_bit_vector(&[0], 9),
        Err(BitfieldError::InvalidLength)
    );
    assert_eq!(
        encode_bit_vector(&[], usize::MAX),
        Err(BitfieldError::InvalidLength)
    );
    assert_eq!(
        decode_bit_vector(&[], usize::MAX),
        Err(BitfieldError::InvalidLength)
    );
}

#[test]
fn should_round_trip_long_vectors_when_the_bit_count_crosses_chunk_boundaries() {
    for length in [7, 8, 9, 15, 16, 17, 255, 256, 257, 1024, 1025] {
        let bits: Vec<bool> = (0..length).map(|index| index % 3 != 0).collect();
        let encoded = encode_bit_vector(&bits, length).unwrap();
        assert_eq!(encoded.len(), length.div_ceil(8));
        assert_eq!(decode_bit_vector(&encoded, length), Ok(bits));
    }
}
