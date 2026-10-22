use super::*;

#[test]
fn bounds_and_unsupported_widths_do_not_change_the_reference_rules() {
    for bound in [0, 1, 127, 128, 256, usize::MAX] {
        for declaration in [
            D::ByteList(bound),
            D::BitList(bound),
            D::ProgressiveBitList(Some(bound)),
        ] {
            assert_eq!(validate(&declaration), Ok(()));
        }
        assert_eq!(
            validate(&D::ByteVector(bound)),
            if bound == 0 {
                Err(E::EmptyVector)
            } else {
                Ok(())
            }
        );
        assert_eq!(
            validate(&D::BitVector(bound)),
            if bound == 0 {
                Err(E::EmptyVector)
            } else {
                Ok(())
            }
        );
    }
    assert_eq!(validate(&D::ProgressiveBitList(None)), Ok(()));
    for width in [0, 3, 5, 31, 33, usize::MAX] {
        assert_eq!(validate(&D::Uint(width)), Err(E::InvalidIntegerWidth));
    }
    for width in [1, 2, 4, 8, 16, 32] {
        assert_eq!(validate(&D::Uint(width)), Ok(()));
    }
}

#[test]
fn generic_sequences_keep_original_child_and_empty_vector_precedence() {
    assert_eq!(validate(&D::Vector(&BAD, 0)), Err(E::EmptyVector));
    assert_eq!(validate(&D::Vector(&BAD, 1)), Err(E::InvalidIntegerWidth));
    assert_eq!(validate(&D::List(&BAD, 0)), Err(E::InvalidIntegerWidth));
    assert_eq!(
        validate(&D::ProgressiveList(&BAD, None)),
        Err(E::InvalidIntegerWidth)
    );
    assert_eq!(
        validate(&D::ProgressiveList(&BAD, Some(0))),
        Err(E::InvalidIntegerWidth)
    );
}

#[test]
fn container_checks_empty_then_counts_then_duplicate_names_then_children() {
    let cases = [
        (D::Container(&["same", "same"], &[]), E::EmptyContainer),
        (
            D::Container(&["same", "same"], &[&BAD]),
            E::LayoutFieldCount,
        ),
        (
            D::Container(&["same", "same"], &[&BAD, &BAD]),
            E::BadDeclaration,
        ),
        (
            D::Container(&["one", "two"], &[&BAD, &D::ByteVector(0)]),
            E::InvalidIntegerWidth,
        ),
        (
            D::Container(&["one", "two"], &[&D::ByteVector(0), &BAD]),
            E::EmptyVector,
        ),
    ];
    for (declaration, error) in cases {
        assert_eq!(validate(&declaration), Err(error));
    }
}

#[test]
fn duplicate_names_preserve_full_utf8_without_normalization_or_nul_truncation() {
    assert_eq!(
        validate(&D::Container(&["字段🦀", "字段🦀"], &[&BYTE, &BYTE])),
        Err(E::BadDeclaration)
    );
    assert_eq!(
        validate(&D::Container(&["é", "e\u{301}"], &[&BYTE, &BYTE])),
        Ok(())
    );
    assert_eq!(
        validate(&D::Container(&["a\0b", "a\0c"], &[&BYTE, &BYTE])),
        Ok(())
    );
    assert_eq!(
        validate(&D::Container(&["", ""], &[&BYTE, &BYTE])),
        Err(E::BadDeclaration)
    );
    assert_eq!(
        validate(&D::Container(&["字段🦀", "字段🦁"], &[&BYTE, &BYTE])),
        Ok(())
    );
    assert_eq!(
        validate(&D::Container(
            &["", "é", "", "other"],
            &[&BYTE, &BYTE, &BYTE, &BYTE]
        )),
        Err(E::BadDeclaration)
    );
}

#[test]
fn progressive_layout_checks_mask_rules_before_field_rules() {
    const WIDE_GAP: [bool; 257] = [false; 257];
    const WIDE_SET: [bool; 257] = [true; 257];
    let cases = [
        (D::ProgressiveContainer(&[], &[], &[]), E::LayoutWidth),
        (
            D::ProgressiveContainer(&WIDE_GAP, &[], &[]),
            E::LayoutTrailingGap,
        ),
        (
            D::ProgressiveContainer(&WIDE_SET, &[], &[]),
            E::LayoutTooWide,
        ),
        (
            D::ProgressiveContainer(&[true], &["extra"], &[]),
            E::EmptyContainer,
        ),
        (
            D::ProgressiveContainer(&[true, true], &[], &[&BAD]),
            E::LayoutFieldCount,
        ),
        (
            D::ProgressiveContainer(&[true], &[], &[&BAD]),
            E::LayoutFieldCount,
        ),
        (
            D::ProgressiveContainer(&[true, true], &["x", "x"], &[&BAD, &BAD]),
            E::BadDeclaration,
        ),
        (
            D::ProgressiveContainer(&[false, true], &["x"], &[&BAD]),
            E::InvalidIntegerWidth,
        ),
    ];
    for (declaration, error) in cases {
        assert_eq!(validate(&declaration), Err(error));
    }
}

#[test]
fn maximum_progressive_width_and_leading_gaps_are_legal() {
    const LAST_ONLY: [bool; 256] = {
        let mut mask = [false; 256];
        mask[255] = true;
        mask
    };
    assert_eq!(
        validate(&D::ProgressiveContainer(&LAST_ONLY, &["字段"], &[&BYTE])),
        Ok(())
    );
    assert_eq!(
        validate(&D::ProgressiveContainer(
            &[false, true, false, true],
            &["a", "b"],
            &[&BYTE, &BOOL]
        )),
        Ok(())
    );
    assert_eq!(
        validate(&D::ProgressiveContainer(&[true, false], &["a"], &[&BYTE])),
        Err(E::LayoutTrailingGap)
    );
    assert_eq!(
        validate(&D::ProgressiveContainer(&[false, false], &["a"], &[&BYTE])),
        Err(E::LayoutTrailingGap)
    );
}

#[test]
fn unions_check_empty_then_counts_then_duplicates_then_ranges_then_children() {
    let cases = [
        (D::CompatibleUnion(&[], &[&BAD]), E::EmptyUnion),
        (D::CompatibleUnion(&[0, 0], &[]), E::EmptyUnion),
        (D::CompatibleUnion(&[0, 0], &[&BAD]), E::BadDeclaration),
        (
            D::CompatibleUnion(&[0, 0], &[&BAD, &BOOL]),
            E::UnionSelectorRepeated,
        ),
        (
            D::CompatibleUnion(&[0, 128], &[&BAD, &BOOL]),
            E::UnionSelectorRange,
        ),
        (
            D::CompatibleUnion(&[1, usize::MAX], &[&BAD, &BOOL]),
            E::UnionSelectorRange,
        ),
        (
            D::CompatibleUnion(&[1, 127], &[&BAD, &BOOL]),
            E::InvalidIntegerWidth,
        ),
        (
            D::CompatibleUnion(&[1, 127], &[&BYTE, &BOOL]),
            E::UnionIncompatible,
        ),
    ];
    for (declaration, error) in cases {
        assert_eq!(validate(&declaration), Err(error));
    }
}

#[test]
fn selectors_one_through_127_are_the_exact_valid_range() {
    for selector in 0..=128 {
        let selectors = Box::leak(Box::new([selector]));
        let expected = if (1..=127).contains(&selector) {
            Ok(())
        } else {
            Err(E::UnionSelectorRange)
        };
        assert_eq!(validate(&D::CompatibleUnion(selectors, &[&BYTE])), expected);
    }
    assert_eq!(
        validate(&D::CompatibleUnion(&[usize::MAX], &[&BYTE])),
        Err(E::UnionSelectorRange)
    );
    assert_eq!(
        validate(&D::CompatibleUnion(&[1, 127], &[&BYTE, &BYTE])),
        Ok(())
    );
    assert_eq!(
        validate(&D::CompatibleUnion(&[127, 1], &[&BYTE, &BYTE])),
        Ok(())
    );
}

#[test]
fn union_child_validation_finishes_before_any_option_compatibility_check() {
    assert_eq!(
        validate(&D::CompatibleUnion(&[1, 2, 3], &[&BYTE, &BOOL, &BAD])),
        Err(E::InvalidIntegerWidth)
    );
    assert_eq!(
        validate(&D::CompatibleUnion(
            &[1, 2, 3],
            &[&BYTE, &D::ByteVector(0), &BAD]
        )),
        Err(E::EmptyVector)
    );
    assert_eq!(
        validate(&D::CompatibleUnion(
            &[1, 2, 3],
            &[&BYTE, &BOOL, &D::ByteVector(0)]
        )),
        Err(E::EmptyVector)
    );
}

#[test]
fn union_validation_checks_later_pairs_not_only_the_first_option() {
    const A: D = D::ProgressiveContainer(&[true], &["a"], &[&BYTE]);
    const B: D = D::ProgressiveContainer(&[false, true], &["b"], &[&BYTE]);
    const C: D = D::ProgressiveContainer(&[false, true], &["c"], &[&BYTE]);
    compatible(&A, &B, true);
    compatible(&A, &C, true);
    compatible(&B, &C, false);
    assert_eq!(
        validate(&D::CompatibleUnion(&[1, 2, 3], &[&A, &B, &C])),
        Err(E::UnionIncompatible)
    );
    assert_eq!(validate(&D::CompatibleUnion(&[1, 2], &[&A, &B])), Ok(()));
}
