use nyx_ssz::{container::container_view, error::CodecError, sequence::SequenceView};

fn bodies<'a>(view: &SequenceView<'a>) -> Vec<&'a [u8]> {
    (0..view.len()).map(|i| view.get(i).unwrap()).collect()
}

#[test]
fn mixed_fields_keep_field_order_and_borrow_input() {
    let input = [42, 11, 0, 0, 0, 43, 44, 11, 0, 0, 0, 99];
    let widths = [Ok(Some(1)), Ok(None), Ok(Some(2)), Ok(None)];
    let view = container_view(&input, &widths).unwrap();
    assert_eq!(
        bodies(&view),
        [&input[..1], &input[11..11], &input[5..7], &input[11..]]
    );
    assert_eq!(view.get(2).unwrap().as_ptr(), input[5..].as_ptr());
    assert_eq!(view.get(3).unwrap().as_ptr(), input[11..].as_ptr());
    assert_eq!(view.get(4), None);
}

#[test]
fn zero_fields_and_widths_follow_internal_slicing() {
    assert!(container_view(&[], &[]).unwrap().is_empty());
    assert_eq!(container_view(&[1], &[]), Err(CodecError::InvalidLength));
    let widths = [Ok(Some(0)), Ok(Some(2)), Ok(Some(0))];
    let input = [1, 2];
    assert_eq!(
        bodies(&container_view(&input, &widths).unwrap()),
        [&input[..0], &input[..], &input[2..]]
    );
    assert_eq!(container_view(&[], &widths), Err(CodecError::InvalidLength));
    assert_eq!(
        container_view(&[0; 3], &widths),
        Err(CodecError::InvalidLength)
    );
}

#[test]
fn repeated_offsets_allow_empty_bodies_and_zero_fixed_fields() {
    let input = [8, 0, 0, 0, 8, 0, 0, 0];
    let widths = [Ok(None), Ok(Some(0)), Ok(None)];
    assert_eq!(
        bodies(&container_view(&input, &widths).unwrap()),
        [&[][..]; 3]
    );
}

#[test]
fn header_budget_precedes_offsets() {
    let widths = [Ok(None), Ok(Some(2)), Ok(None)];
    for len in 0..10 {
        assert_eq!(
            container_view(&vec![0; len], &widths),
            Err(CodecError::ScopeTooSmall)
        );
    }
    assert_eq!(
        container_view(&[0; 10], &widths),
        Err(CodecError::FirstOffset)
    );
}

#[test]
fn offsets_check_first_then_order_then_final_scope() {
    let widths = [Ok(None), Ok(Some(1)), Ok(None), Ok(None)];
    for (offsets, expected) in [
        ([0, 99, 98], CodecError::FirstOffset),
        ([u32::MAX, 13, 13], CodecError::FirstOffset),
        ([13, 99, 98], CodecError::OffsetUnordered),
        ([13, 12, 99], CodecError::OffsetUnordered),
        ([13, 99, 99], CodecError::OffsetPastScope),
        ([13, 13, u32::MAX], CodecError::OffsetPastScope),
    ] {
        let mut input = vec![];
        input.extend(offsets[0].to_le_bytes());
        input.push(42);
        input.extend(offsets[1].to_le_bytes());
        input.extend(offsets[2].to_le_bytes());
        assert_eq!(container_view(&input, &widths), Err(expected));
    }
}

#[test]
fn unrepresentable_widths_and_header_sums_keep_budget_faults() {
    let huge = Err(CodecError::SizeOverflow);
    for widths in [
        vec![huge],
        vec![Ok(Some(usize::MAX))],
        vec![Ok(Some(usize::MAX)), Ok(Some(1))],
    ] {
        assert_eq!(container_view(&[], &widths), Err(CodecError::InvalidLength));
        let mut mixed = widths;
        mixed.push(Ok(None));
        assert_eq!(container_view(&[], &mixed), Err(CodecError::ScopeTooSmall));
        mixed.reverse();
        assert_eq!(
            container_view(&[0; 4], &mixed),
            Err(CodecError::ScopeTooSmall)
        );
    }
    assert_eq!(
        container_view(&[], &[Err(CodecError::InvalidIntegerWidth)]),
        Err(CodecError::InvalidIntegerWidth)
    );
}
