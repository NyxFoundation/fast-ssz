use nyx_ssz::bitfield::{decode_progressive_bit_list, encode_progressive_bit_list, BitfieldError};

#[test]
fn should_borrow_canonical_bytes_when_decoding_a_progressive_bitlist() {
    let bytes = [0x0d];
    let view = decode_progressive_bit_list(&bytes, None).unwrap();
    assert_eq!(view.len_bits(), 3);
    assert_eq!(view.as_ssz_bytes(), bytes);
    assert_eq!(view.as_ssz_bytes().as_ptr(), bytes.as_ptr());
}

#[test]
fn should_preserve_the_delimiter_when_the_progressive_bitlist_is_empty() {
    for limit in [None, Some(0), Some(usize::MAX)] {
        let encoded = encode_progressive_bit_list(&[], limit).unwrap();
        assert_eq!(encoded, [1]);
        let view = decode_progressive_bit_list(&encoded, limit).unwrap();
        assert_eq!(view.len_bits(), 0);
        assert_eq!(view.as_ssz_bytes(), &[1]);
    }
}

#[test]
fn should_reject_missing_delimiters_before_checking_a_progressive_capacity() {
    for limit in [None, Some(0)] {
        assert_eq!(
            decode_progressive_bit_list(&[], limit),
            Err(BitfieldError::EmptyEncoding)
        );
        assert_eq!(
            decode_progressive_bit_list(&[0], limit),
            Err(BitfieldError::NoDelimiter)
        );
        assert_eq!(
            decode_progressive_bit_list(&[0, 0], limit),
            Err(BitfieldError::NoDelimiter)
        );
        assert_eq!(
            decode_progressive_bit_list(&[1, 0], limit),
            Err(BitfieldError::TrailingZeros)
        );
    }
}

#[test]
fn should_enforce_an_optional_progressive_capacity_when_it_is_declared() {
    assert_eq!(
        encode_progressive_bit_list(&[true], Some(0)),
        Err(BitfieldError::OverLimit)
    );
    assert_eq!(
        decode_progressive_bit_list(&[2], Some(0)),
        Err(BitfieldError::OverLimit)
    );
    assert_eq!(
        decode_progressive_bit_list(&[0xff, 1], Some(7)),
        Err(BitfieldError::OverLimit)
    );
    assert_eq!(
        decode_progressive_bit_list(&[0xff, 1], Some(8))
            .unwrap()
            .len_bits(),
        8
    );
}

#[test]
fn should_recover_every_final_byte_pattern_when_a_progressive_bitlist_is_unbounded() {
    for final_byte in 1..=u8::MAX {
        let bytes = [0xaf, final_byte];
        let view = decode_progressive_bit_list(&bytes, None).unwrap();
        assert_eq!(
            view.len_bits(),
            8 + (7 - final_byte.leading_zeros()) as u128
        );
        assert_eq!(view.as_ssz_bytes(), &bytes);
    }
}

#[test]
fn should_round_trip_values_when_progressive_bit_counts_cross_byte_boundaries() {
    for length in [0usize, 1, 7, 8, 9, 15, 16, 17, 255, 256, 257, 1024] {
        let bits: Vec<bool> = (0..length).map(|index| index % 3 == 0).collect();
        for limit in [None, Some(length), Some(usize::MAX)] {
            let encoded = encode_progressive_bit_list(&bits, limit).unwrap();
            let view = decode_progressive_bit_list(&encoded, limit).unwrap();
            assert_eq!(view.len_bits(), length as u128);
            for (index, bit) in bits.iter().enumerate() {
                assert_eq!(
                    view.as_ssz_bytes()[index / 8] & (1 << (index % 8)) != 0,
                    *bit
                );
            }
        }
    }
}
