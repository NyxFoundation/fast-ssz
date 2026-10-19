use nyx_ssz::{
    error::CodecError,
    sequence::{variable_vector_view, SequenceView},
};

fn bodies<'a>(view: &SequenceView<'a>) -> Vec<&'a [u8]> {
    (0..view.len())
        .map(|index| view.get(index).unwrap())
        .collect()
}

#[test]
fn should_return_borrowed_bodies_when_offsets_are_canonical() {
    let bytes = [8, 0, 0, 0, 10, 0, 0, 0, 42, 43, 44];
    let view = variable_vector_view(&bytes, 2).unwrap();
    assert_eq!(view.len(), 2);
    assert!(!view.is_empty());
    assert_eq!(bodies(&view), [&bytes[8..10], &bytes[10..11]]);
    assert_eq!(view.get(0).unwrap().as_ptr(), bytes[8..].as_ptr());
    assert_eq!(view.get(1).unwrap().as_ptr(), bytes[10..].as_ptr());
    assert_eq!(view.get(2), None);
    assert_eq!(view.get(usize::MAX), None);
}

#[test]
fn should_preserve_empty_bodies_when_offsets_repeat_or_end_at_scope() {
    let bytes = [12, 0, 0, 0, 12, 0, 0, 0, 13, 0, 0, 0, 99];
    let view = variable_vector_view(&bytes, 3).unwrap();
    assert_eq!(
        bodies(&view),
        [&bytes[12..12], &bytes[12..13], &bytes[13..13]]
    );
    let empty_body = variable_vector_view(&[4, 0, 0, 0], 1).unwrap();
    assert_eq!(bodies(&empty_body), [&[][..]]);
    assert!(!empty_body.is_empty());
}

#[test]
fn should_match_internal_zero_count_layout_without_validating_the_type() {
    for bytes in [&[][..], &[9][..]] {
        let view = variable_vector_view(bytes, 0).unwrap();
        assert_eq!(view.len(), 0);
        assert!(view.is_empty());
        assert_eq!(view.get(0), None);
        assert_eq!(view.get(usize::MAX), None);
    }
}

#[test]
fn should_refuse_undersized_headers_without_machine_arithmetic_overflow() {
    assert_eq!(variable_vector_view(&[], 1), Err(CodecError::ScopeTooSmall));
    assert_eq!(
        variable_vector_view(&[0; 7], 2),
        Err(CodecError::ScopeTooSmall)
    );
    assert_eq!(
        variable_vector_view(&[], usize::MAX),
        Err(CodecError::ScopeTooSmall)
    );
}

#[test]
fn should_preserve_first_offset_order_and_scope_error_precedence() {
    assert_eq!(
        variable_vector_view(&[0; 8], 2),
        Err(CodecError::FirstOffset)
    );
    assert_eq!(
        variable_vector_view(&[8, 0, 0, 0, 7, 0, 0, 0], 2),
        Err(CodecError::OffsetUnordered)
    );
    assert_eq!(
        variable_vector_view(&[8, 0, 0, 0, 9, 0, 0, 0], 2),
        Err(CodecError::OffsetPastScope)
    );
}

fn reference(input: &[u8], count: usize) -> Result<Vec<&[u8]>, CodecError> {
    if input.len() as u128 >= 4_294_967_296 {
        return Err(CodecError::SizeOverflow);
    }
    let header = count.checked_mul(4).ok_or(CodecError::ScopeTooSmall)?;
    if input.len() < header {
        return Err(CodecError::ScopeTooSmall);
    }
    if count == 0 {
        return Ok(vec![]);
    }
    let offsets: Vec<usize> = input[..header]
        .as_chunks::<4>()
        .0
        .iter()
        .map(|chunk| u32::from_le_bytes(*chunk) as usize)
        .collect();
    if offsets[0] != header {
        return Err(CodecError::FirstOffset);
    }
    if offsets.windows(2).any(|pair| pair[1] < pair[0]) {
        return Err(CodecError::OffsetUnordered);
    }
    if offsets.last().unwrap() > &input.len() {
        return Err(CodecError::OffsetPastScope);
    }
    Ok(offsets
        .iter()
        .zip(offsets.iter().copied().skip(1).chain([input.len()]))
        .map(|(start, end)| &input[*start..end])
        .collect())
}

fn short_table(count: usize, payload: usize, mut pattern: usize) -> Vec<u8> {
    let header = count * 4;
    let mut input: Vec<u8> = (0..header + payload).map(|value| value as u8).collect();
    input[..4].copy_from_slice(&(header as u32).to_le_bytes());
    for slot in 1..count {
        let offset = pattern % (input.len() + 3);
        pattern /= input.len() + 3;
        input[slot * 4..slot * 4 + 4].copy_from_slice(&(offset as u32).to_le_bytes());
    }
    input
}

#[test]
fn should_match_reference_layout_when_tables_are_short() {
    for count in 1usize..=3 {
        for payload in 0..=4 {
            for pattern in 0..(count * 4 + payload + 3).pow(count as u32 - 1) {
                let input = short_table(count, payload, pattern);
                let actual = variable_vector_view(&input, count).map(|view| bodies(&view));
                assert_eq!(actual, reference(&input, count));
            }
        }
    }
}

#[test]
fn should_format_header_faults_without_internal_details() {
    assert_eq!(
        CodecError::ScopeTooSmall.to_string(),
        "SSZ input is smaller than its header"
    );
    assert_eq!(
        CodecError::FirstOffset.to_string(),
        "SSZ first offset must follow its header"
    );
}
