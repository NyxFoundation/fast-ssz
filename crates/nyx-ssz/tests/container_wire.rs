use nyx_ssz::container_wire::assemble;

#[test]
fn should_concatenate_inline_parts_when_no_field_requires_an_offset() {
    let slots = [(true, vec![1, 2]), (true, vec![]), (true, vec![3, 4, 5])];
    assert_eq!(assemble(&slots), Ok(vec![1, 2, 3, 4, 5]));
    assert_eq!(assemble(&[]), Ok(vec![]));
}

#[test]
fn should_leave_offsets_in_the_header_when_fixed_and_variable_fields_are_interspersed() {
    let slots = [
        (true, vec![170, 187]),
        (false, vec![1, 2, 3]),
        (true, vec![204]),
        (false, vec![]),
    ];
    let expected = [170, 187, 11, 0, 0, 0, 204, 14, 0, 0, 0, 1, 2, 3];
    assert_eq!(assemble(&slots), Ok(expected.to_vec()));
    assert_eq!(slots[1].1, [1, 2, 3]);
}

#[test]
fn should_repeat_offsets_when_variable_bodies_are_empty() {
    let slots = [(false, vec![]), (false, vec![7]), (false, vec![])];
    assert_eq!(
        assemble(&slots),
        Ok(vec![12, 0, 0, 0, 12, 0, 0, 0, 13, 0, 0, 0, 7])
    );
}

fn reference(slots: &[(bool, Vec<u8>)]) -> Vec<u8> {
    let leading: usize = slots
        .iter()
        .map(|(fixed, bytes)| if *fixed { bytes.len() } else { 4 })
        .sum();
    let mut head = Vec::new();
    let mut body = Vec::new();
    for (fixed, bytes) in slots {
        if *fixed {
            head.extend_from_slice(bytes);
        } else {
            head.extend_from_slice(&((leading + body.len()) as u32).to_le_bytes());
            body.extend_from_slice(bytes);
        }
    }
    head.extend_from_slice(&body);
    head
}

#[test]
fn should_match_independent_mixed_layouts_when_small_field_patterns_are_exhausted() {
    for count in 0..=5 {
        for flags in 0..(1 << count) {
            for rotation in 0..4 {
                let slots: Vec<_> = (0..count)
                    .map(|index| {
                        (
                            flags & (1 << index) != 0,
                            vec![index as u8 + 1; (index + rotation) % 4],
                        )
                    })
                    .collect();
                assert_eq!(assemble(&slots), Ok(reference(&slots)));
            }
        }
    }
}
