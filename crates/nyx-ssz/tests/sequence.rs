use nyx_ssz::{error::CodecError, sequence::offset_spans};

#[test]
fn should_compute_ordered_spans_including_empty_bodies_and_empty_tables() {
    assert_eq!(offset_spans(&[], usize::MAX), Ok(vec![]));
    assert_eq!(offset_spans(&[0], 0), Ok(vec![0]));
    assert_eq!(offset_spans(&[0], 5), Ok(vec![5]));
    assert_eq!(offset_spans(&[5], 5), Ok(vec![0]));
    assert_eq!(offset_spans(&[12, 17, 17, 20], 27), Ok(vec![5, 0, 3, 7]));
}

#[test]
fn should_preserve_reference_error_precedence_for_order_and_scope() {
    assert_eq!(offset_spans(&[5], 4), Err(CodecError::OffsetPastScope));
    assert_eq!(
        offset_spans(&[8, 4, 20], 0),
        Err(CodecError::OffsetUnordered)
    );
    assert_eq!(
        offset_spans(&[0, 8, 9], 8),
        Err(CodecError::OffsetPastScope)
    );
    assert_eq!(
        offset_spans(&[usize::MAX, 0], 0),
        Err(CodecError::OffsetUnordered)
    );
}

#[test]
fn should_subtract_machine_maximum_offsets_without_overflow() {
    assert_eq!(
        offset_spans(&[usize::MAX - 1, usize::MAX], usize::MAX),
        Ok(vec![1, 0])
    );
    assert_eq!(offset_spans(&[usize::MAX], usize::MAX), Ok(vec![0]));
}

#[test]
fn should_explain_layout_faults_without_exposing_internal_details() {
    assert_eq!(
        CodecError::OffsetUnordered.to_string(),
        "SSZ offsets must be nondecreasing"
    );
    assert_eq!(
        CodecError::OffsetPastScope.to_string(),
        "SSZ offset exceeds its input scope"
    );
}

fn reference(offsets: &[usize], scope: usize) -> Result<Vec<usize>, CodecError> {
    let mut spans = Vec::new();
    for pair in offsets.windows(2) {
        if pair[1] < pair[0] {
            return Err(CodecError::OffsetUnordered);
        }
        spans.push(pair[1] - pair[0]);
    }
    if let Some(last) = offsets.last() {
        if *last > scope {
            return Err(CodecError::OffsetPastScope);
        }
        spans.push(scope - last);
    }
    Ok(spans)
}

#[test]
fn should_match_a_separate_oracle_for_short_tables() {
    for count in 0..=4 {
        for pattern in 0..6usize.pow(count) {
            let mut remaining = pattern;
            let offsets: Vec<usize> = (0..count)
                .map(|_| {
                    let value = remaining % 6;
                    remaining /= 6;
                    value
                })
                .collect();
            for scope in 0..8 {
                assert_eq!(offset_spans(&offsets, scope), reference(&offsets, scope));
            }
        }
    }
}
