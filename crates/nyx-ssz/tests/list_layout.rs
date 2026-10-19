use nyx_ssz::{error::CodecError, sequence::variable_list_view};

#[test]
fn should_infer_element_count_when_the_first_offset_is_canonical() {
    let bytes = [8, 0, 0, 0, 10, 0, 0, 0, 42, 43, 44];
    for limit in [None, Some(2), Some(usize::MAX)] {
        let view = variable_list_view(&bytes, limit).unwrap();
        assert_eq!(view.len(), 2);
        assert_eq!(view.get(0), Some(&bytes[8..10]));
        assert_eq!(view.get(1), Some(&bytes[10..11]));
        assert_eq!(view.get(0).unwrap().as_ptr(), bytes[8..].as_ptr());
    }
    assert_eq!(
        variable_list_view(&bytes, Some(1)),
        Err(CodecError::OverLimit)
    );
}

#[test]
fn should_accept_empty_input_when_capacity_is_zero_or_unbounded() {
    for limit in [None, Some(0), Some(usize::MAX)] {
        let view = variable_list_view(&[], limit).unwrap();
        assert!(view.is_empty());
        assert_eq!(view.get(0), None);
    }
}

#[test]
fn should_refuse_nonempty_truncated_headers_when_fewer_than_four_bytes_remain() {
    for count in 1..4 {
        assert_eq!(
            variable_list_view(&[0; 3][..count], None),
            Err(CodecError::ScopeTooSmall)
        );
    }
}

#[test]
fn should_check_first_offset_shape_before_scope_and_capacity() {
    for first in 0..4 {
        assert_eq!(
            variable_list_view(&[first, 0, 0, 0], Some(0)),
            Err(CodecError::OffsetBelowTable)
        );
    }
    for first in [5, 6, 7] {
        assert_eq!(
            variable_list_view(&[first, 0, 0, 0], Some(0)),
            Err(CodecError::OffsetUnaligned)
        );
    }
    assert_eq!(
        variable_list_view(&[8, 0, 0, 0], Some(0)),
        Err(CodecError::OffsetPastScope)
    );
    assert_eq!(
        variable_list_view(&[255; 4], None),
        Err(CodecError::OffsetUnaligned)
    );
}

#[test]
fn should_check_capacity_before_later_offset_order() {
    let bytes = [8, 0, 0, 0, 7, 0, 0, 0];
    assert_eq!(
        variable_list_view(&bytes, Some(1)),
        Err(CodecError::OverLimit)
    );
    assert_eq!(
        variable_list_view(&bytes, None),
        Err(CodecError::OffsetUnordered)
    );
    let empty_body = variable_list_view(&[4, 0, 0, 0], Some(1)).unwrap();
    assert_eq!(empty_body.len(), 1);
    assert_eq!(empty_body.get(0), Some(&[][..]));
}

#[test]
fn should_format_list_layout_faults_without_internal_details() {
    for (error, message) in [
        (
            CodecError::OffsetBelowTable,
            "SSZ first offset is below its table width",
        ),
        (
            CodecError::OffsetUnaligned,
            "SSZ first offset is not aligned to its table width",
        ),
        (
            CodecError::OverLimit,
            "SSZ element count exceeds its declared capacity",
        ),
    ] {
        assert_eq!(error.to_string(), message);
    }
}
