use super::*;

#[test]
fn every_shape_has_its_reference_width_and_classification() {
    let cases = [
        (D::Boolean, Some(1)),
        (D::Uint(usize::MAX), Some(usize::MAX)),
        (D::ByteVector(usize::MAX), Some(usize::MAX)),
        (D::ByteList(usize::MAX), None),
        (D::BitVector(usize::MAX), Some(usize::MAX / 8 + 1)),
        (D::BitList(usize::MAX), None),
        (D::ProgressiveBitList(Some(usize::MAX)), None),
        (D::Vector(&BYTE, usize::MAX), Some(usize::MAX)),
        (D::List(&BYTE, usize::MAX), None),
        (D::ProgressiveList(&BYTE, Some(usize::MAX)), None),
        (D::Container(&["字段"], &[&BYTE]), Some(1)),
        (
            D::ProgressiveContainer(&[false, true], &["🦀"], &[&BYTE]),
            Some(1),
        ),
        (D::CompatibleUnion(&[1], &[&BYTE]), None),
    ];
    for (declaration, expected) in cases {
        assert_eq!(fixed_size(&declaration), Ok(expected));
        assert_eq!(
            is_basic(&declaration),
            matches!(declaration, D::Boolean | D::Uint(_))
        );
    }
}

#[test]
fn bitvector_rounding_never_adds_seven_to_a_native_maximum() {
    for count in [0, 1, 7, 8, 9, 15, 16, 17, usize::MAX - 7, usize::MAX] {
        let expected = (count as u128).div_ceil(8);
        assert_eq!(
            fixed_size(&D::BitVector(count)),
            Ok(Some(expected as usize))
        );
    }
}

#[test]
fn empty_internal_fields_have_zero_width_even_when_the_declaration_is_invalid() {
    for declaration in [
        D::Container(&["ignored"], &[]),
        D::ProgressiveContainer(&[], &[], &[]),
    ] {
        assert_eq!(fixed_size(&declaration), Ok(Some(0)));
    }
    assert_eq!(fixed_size(&D::ByteVector(0)), Ok(Some(0)));
    assert_eq!(fixed_size(&D::BitVector(0)), Ok(Some(0)));
    assert_eq!(fixed_size(&D::Uint(0)), Ok(Some(0)));
}

#[test]
fn vector_zero_cancels_fixed_overflow_but_not_variable_width() {
    assert_eq!(fixed_size(&OVERFLOW), Err(E::SizeOverflow));
    assert_eq!(fixed_size(&D::Vector(&OVERFLOW, 0)), Ok(Some(0)));
    assert_eq!(fixed_size(&D::Vector(&VARIABLE, 0)), Ok(None));
    assert_eq!(fixed_size(&D::Vector(&D::Uint(0), usize::MAX)), Ok(Some(0)));
    assert_eq!(fixed_size(&D::Vector(&OVERFLOW, 1)), Err(E::SizeOverflow));
}

#[test]
fn container_addition_and_nested_multiplication_report_only_real_overflow() {
    assert_eq!(
        fixed_size(&D::Container(&[], &[&D::Uint(usize::MAX), &D::Uint(0)])),
        Ok(Some(usize::MAX))
    );
    assert_eq!(
        fixed_size(&D::Container(&[], &[&D::Uint(usize::MAX), &BYTE])),
        Err(E::SizeOverflow)
    );
    assert_eq!(
        fixed_size(&D::Container(&[], &[&OVERFLOW])),
        Err(E::SizeOverflow)
    );
    assert_eq!(
        fixed_size(&D::ProgressiveContainer(&[false, true], &[], &[&OVERFLOW])),
        Err(E::SizeOverflow)
    );
    assert_eq!(
        fixed_size(&D::Container(&[], &[&D::Container(&[], &[]), &BYTE])),
        Ok(Some(1))
    );
}

#[test]
fn variable_fields_cancel_both_prior_and_later_overflows() {
    let fields: &[&'static [&'static D]] = &[
        &[&OVERFLOW, &VARIABLE],
        &[&VARIABLE, &OVERFLOW],
        &[&D::Uint(usize::MAX), &BYTE, &VARIABLE],
        &[&VARIABLE, &D::Uint(usize::MAX), &BYTE],
        &[&D::Container(&[], &[&OVERFLOW]), &D::List(&BAD, 0)],
        &[&D::CompatibleUnion(&[], &[]), &OVERFLOW],
    ];
    for &types in fields {
        assert_eq!(fixed_size(&D::Container(&[], types)), Ok(None));
        assert_eq!(
            fixed_size(&D::ProgressiveContainer(&[], &[], types)),
            Ok(None)
        );
    }
}

#[test]
fn progressive_gaps_and_declaration_counts_add_no_wire_bytes() {
    let declaration = D::ProgressiveContainer(&[false, false, true], &["only"], &[&D::Uint(2)]);
    assert_eq!(fixed_size(&declaration), Ok(Some(2)));
    assert_eq!(
        fixed_size(&D::Container(&[], &[&D::Uint(2), &BYTE])),
        Ok(Some(3))
    );
    assert_eq!(
        fixed_size(&D::Container(&["extra", "names"], &[&VARIABLE])),
        Ok(None)
    );
}
