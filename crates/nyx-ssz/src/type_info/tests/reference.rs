use super::{
    reference_cases::{CASES, COMPATIBLE},
    *,
};

#[test]
fn widths_validity_and_classification_match_the_actual_pinned_lean_executable() {
    for (declaration, width, basic, validity) in &CASES {
        assert_eq!(fixed_size(declaration), Ok(*width), "{declaration:?}");
        assert_eq!(is_basic(declaration), *basic, "{declaration:?}");
        assert_eq!(validate(declaration), *validity, "{declaration:?}");
    }
}

#[test]
fn every_ordered_pair_matches_the_actual_pinned_lean_executable() {
    for (row, (left, ..)) in CASES.iter().enumerate() {
        for (column, (right, ..)) in CASES.iter().enumerate() {
            let expected = COMPATIBLE[row].as_bytes()[column] == b'1';
            assert_eq!(
                is_compatible(left, right),
                expected,
                "pair ({row}, {column})"
            );
            assert_eq!(
                super::super::declaration_equal(left, right),
                left == right,
                "complete structural equality at ({row}, {column})"
            );
        }
    }
}

#[test]
fn all_four_implementations_are_const_evaluable_with_full_utf8_metadata() {
    const SHAPE: D = D::Container(&["字段🦀", "é\0"], &[&D::BitVector(9), &BYTE]);
    const ALIAS: D = D::Container(&["字段🦀", "é\0"], &[&D::BitVector(9), &BYTE]);
    const WIDTH: Result<Option<usize>, E> = fixed_size(&SHAPE);
    const BASIC: bool = is_basic(&SHAPE);
    const VALID: Result<(), E> = validate(&SHAPE);
    const COMPATIBLE: bool = is_compatible(&SHAPE, &ALIAS);
    const CANCELLATION: Result<Option<usize>, E> =
        fixed_size(&D::Container(&[], &[&OVERFLOW, &VARIABLE]));
    assert_eq!(WIDTH, Ok(Some(3)));
    assert!(!std::hint::black_box(BASIC));
    assert_eq!(VALID, Ok(()));
    assert!(std::hint::black_box(COMPATIBLE));
    assert_eq!(CANCELLATION, Ok(None));
}

#[test]
fn new_error_categories_have_distinct_specific_standard_error_messages() {
    let errors = [
        (
            E::EmptyContainer,
            "SSZ container declarations must contain at least one field",
        ),
        (
            E::BadDeclaration,
            "SSZ declaration has duplicate names or mismatched selector counts",
        ),
        (
            E::LayoutWidth,
            "SSZ progressive layouts must contain at least one position",
        ),
        (
            E::LayoutTrailingGap,
            "SSZ progressive layouts must end on an active position",
        ),
        (
            E::LayoutTooWide,
            "SSZ progressive layouts must not exceed 256 positions",
        ),
        (
            E::LayoutFieldCount,
            "SSZ field names and active positions must match declared fields",
        ),
        (
            E::EmptyUnion,
            "SSZ compatible unions must declare selectors and options",
        ),
        (
            E::UnionSelectorRepeated,
            "SSZ compatible union selectors must be distinct",
        ),
        (
            E::UnionSelectorRange,
            "SSZ compatible union selectors must be between 1 and 127",
        ),
        (
            E::UnionIncompatible,
            "SSZ compatible union options must have pairwise compatible layouts",
        ),
    ];
    for (error, expected) in errors {
        let standard_error: &dyn std::error::Error = &error;
        assert_eq!(standard_error.to_string(), expected);
    }
}
