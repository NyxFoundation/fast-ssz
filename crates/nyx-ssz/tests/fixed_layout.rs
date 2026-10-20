use nyx_ssz::{
    codec::decode_elements,
    error::CodecError,
    sequence::{fixed_list_view, fixed_vector_view},
};

#[test]
fn should_borrow_and_decode_fixed_elements_without_copying_the_input() {
    let bytes = [1, 0, 2, 0, 3, 0];
    let view = fixed_vector_view(&bytes, 2, 3).unwrap();
    assert_eq!(view.len(), 3);
    assert_eq!(view.get(1), Some(&bytes[2..4]));
    assert_eq!(view.get(1).unwrap().as_ptr(), bytes[2..4].as_ptr());
    assert_eq!(view.get(3), None);
    assert_eq!(decode_elements::<u16>(&view).unwrap(), [1, 2, 3]);
}

#[test]
fn should_preserve_internal_zero_width_and_zero_count_slicing_rules() {
    let empty = fixed_vector_view(&[], usize::MAX, 0).unwrap();
    assert!(empty.is_empty());
    let widthless = fixed_vector_view(&[], 0, 3).unwrap();
    assert_eq!(widthless.len(), 3);
    assert_eq!(widthless.get(2), Some(&[][..]));
}

#[test]
fn should_reject_wrong_or_unrepresentable_fixed_vector_lengths() {
    assert_eq!(
        fixed_vector_view(&[1], 2, 2).unwrap_err(),
        CodecError::InvalidLength
    );
    assert_eq!(
        fixed_vector_view(&[], usize::MAX, 2).unwrap_err(),
        CodecError::InvalidLength
    );
    assert_eq!(
        fixed_vector_view(&[1], 0, usize::MAX).unwrap_err(),
        CodecError::InvalidLength
    );
    assert_eq!(
        fixed_vector_view(&[1], usize::MAX, 0).unwrap_err(),
        CodecError::InvalidLength
    );
}

#[test]
fn should_infer_fixed_list_counts_and_enforce_optional_capacities() {
    let bytes = [1, 0, 2, 0];
    for limit in [None, Some(2), Some(usize::MAX)] {
        let view = fixed_list_view(&bytes, 2, limit).unwrap();
        assert_eq!(decode_elements::<u16>(&view).unwrap(), [1, 2]);
    }
    assert_eq!(
        fixed_list_view(&bytes, 2, Some(1)).unwrap_err(),
        CodecError::OverLimit
    );
    assert!(fixed_list_view(&[], 0, Some(0)).unwrap().is_empty());
}

#[test]
fn should_validate_fixed_list_width_and_divisibility_before_capacity() {
    assert_eq!(
        fixed_list_view(&[1], 0, Some(0)).unwrap_err(),
        CodecError::ScopeWidthless
    );
    assert_eq!(
        fixed_list_view(&[1, 2, 3], 2, Some(0)).unwrap_err(),
        CodecError::ScopeUndivided
    );
    assert_eq!(
        fixed_list_view(&[1], usize::MAX, None).unwrap_err(),
        CodecError::ScopeUndivided
    );
    assert_eq!(
        CodecError::ScopeWidthless.to_string(),
        "SSZ nonempty input cannot use zero-width elements"
    );
    assert_eq!(
        CodecError::ScopeUndivided.to_string(),
        "SSZ input does not divide into complete elements"
    );
}

#[test]
fn should_match_fixed_vector_slicing_when_small_layouts_are_exhausted() {
    let source: Vec<u8> = (0..24).collect();
    for width in 0..=8 {
        for count in 0..=6 {
            for length in 0..=source.len() {
                let bytes = &source[..length];
                let result = fixed_vector_view(bytes, width, count);
                if length != width * count {
                    assert_eq!(result.unwrap_err(), CodecError::InvalidLength);
                    continue;
                }
                let view = result.unwrap();
                let expected: Vec<_> = (0..count)
                    .map(|index| Some(&bytes[index * width..(index + 1) * width]))
                    .collect();
                assert_eq!(view.len(), count);
                assert_eq!(
                    (0..count).map(|index| view.get(index)).collect::<Vec<_>>(),
                    expected
                );
                assert_eq!(view.get(count), None);
            }
        }
    }
}

#[test]
fn should_match_fixed_list_error_precedence_when_small_layouts_are_exhausted() {
    let source: Vec<u8> = (0..24).collect();
    for width in 0..=8 {
        for length in 0..=source.len() {
            for limit in [None, Some(0), Some(1), Some(3), Some(usize::MAX)] {
                let bytes = &source[..length];
                let count = length.checked_div(width).unwrap_or(0);
                let reason = if length == 0 {
                    None
                } else if width == 0 {
                    Some(CodecError::ScopeWidthless)
                } else if !length.is_multiple_of(width) {
                    Some(CodecError::ScopeUndivided)
                } else if limit.is_some_and(|capacity| count > capacity) {
                    Some(CodecError::OverLimit)
                } else {
                    None
                };
                let result = fixed_list_view(bytes, width, limit);
                if let Some(error) = reason {
                    assert_eq!(result.unwrap_err(), error);
                    continue;
                }
                let view = result.unwrap();
                assert_eq!(view.len(), count);
                assert_eq!(view.get(count), None);
            }
        }
    }
}
