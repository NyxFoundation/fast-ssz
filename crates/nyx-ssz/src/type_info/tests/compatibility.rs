use super::*;

#[test]
fn byte_shapes_alias_only_exact_uint8_vectors_and_lists() {
    for bound in [0, 1, usize::MAX] {
        compatible(&D::ByteVector(bound), &D::Vector(&BYTE, bound), true);
        compatible(&D::ByteList(bound), &D::List(&BYTE, bound), true);
        compatible(&D::ByteVector(bound), &D::Vector(&BOOL, bound), false);
        compatible(&D::ByteList(bound), &D::List(&D::Uint(2), bound), false);
        compatible(&D::ByteList(bound), &D::ByteVector(bound), false);
        compatible(
            &D::ByteList(bound),
            &D::ProgressiveList(&BYTE, Some(bound)),
            false,
        );
    }
    compatible(&D::ByteVector(1), &D::Vector(&BYTE, 2), false);
    compatible(&D::ByteList(1), &D::List(&BYTE, 2), false);
    compatible(&D::Vector(&BYTE, 1), &D::Vector(&D::Uint(2), 1), false);
}

#[test]
fn progressive_bounds_are_observed_by_equality_but_ignored_by_compatibility() {
    let variants = [
        D::ProgressiveBitList(None),
        D::ProgressiveBitList(Some(0)),
        D::ProgressiveBitList(Some(usize::MAX)),
    ];
    for (i, left) in variants.iter().enumerate() {
        for (j, right) in variants.iter().enumerate() {
            assert_eq!(left == right, i == j);
            compatible(left, right, true);
        }
    }
    compatible(
        &D::ProgressiveList(&BYTE, None),
        &D::ProgressiveList(&BYTE, Some(0)),
        true,
    );
    compatible(
        &D::ProgressiveList(&BYTE, None),
        &D::ProgressiveList(&BOOL, None),
        false,
    );
    compatible(
        &D::ProgressiveList(&D::ByteVector(1), None),
        &D::ProgressiveList(&D::Vector(&BYTE, 1), Some(0)),
        true,
    );
}

#[test]
fn all_bit_shapes_are_distinct_and_ordinary_bit_bounds_remain_significant() {
    let shapes = [
        D::Boolean,
        D::Uint(1),
        D::ByteVector(1),
        D::ByteList(1),
        D::BitVector(1),
        D::BitList(1),
        D::ProgressiveBitList(None),
    ];
    for (i, left) in shapes.iter().enumerate() {
        for (j, right) in shapes.iter().enumerate() {
            compatible(left, right, i == j);
        }
    }
    compatible(&D::BitVector(1), &D::BitVector(2), false);
    compatible(&D::BitList(1), &D::BitList(2), false);
    compatible(&D::BitVector(0), &D::BitVector(0), true);
    compatible(&BAD, &BAD, true);
}

#[test]
fn ordinary_containers_preserve_names_order_counts_and_recursive_layouts() {
    compatible(
        &D::Container(&["é"], &[&D::ByteVector(2)]),
        &D::Container(&["é"], &[&D::Vector(&BYTE, 2)]),
        true,
    );
    compatible(
        &D::Container(&["é"], &[&BYTE]),
        &D::Container(&["e\u{301}"], &[&BYTE]),
        false,
    );
    compatible(
        &D::Container(&["a", "b"], &[&BYTE, &BOOL]),
        &D::Container(&["b", "a"], &[&BYTE, &BOOL]),
        false,
    );
    compatible(&D::Container(&[], &[&BYTE]), &D::Container(&[], &[]), false);
    compatible(
        &D::Container(&["ignored"], &[]),
        &D::Container(&[], &[]),
        false,
    );
    compatible(
        &D::Container(&["x", "x"], &[&BYTE]),
        &D::Container(&["x", "x"], &[&BYTE]),
        true,
    );
    compatible(
        &D::Container(&["x"], &[&BYTE]),
        &D::ProgressiveContainer(&[true], &["x"], &[&BYTE]),
        false,
    );
}

#[test]
fn progressive_shared_positions_require_equal_names_and_compatible_children() {
    const LEFT: D = D::ProgressiveContainer(&[true], &["字段🦀"], &[&D::ByteVector(2)]);
    compatible(
        &LEFT,
        &D::ProgressiveContainer(&[true, false], &["字段🦀"], &[&D::Vector(&BYTE, 2)]),
        true,
    );
    compatible(
        &LEFT,
        &D::ProgressiveContainer(&[true], &["字段🦁"], &[&D::ByteVector(2)]),
        false,
    );
    compatible(
        &LEFT,
        &D::ProgressiveContainer(&[true], &["字段🦀"], &[&BOOL]),
        false,
    );
    compatible(
        &LEFT,
        &D::ProgressiveContainer(&[true], &["字段🦀"], &[]),
        false,
    );
    compatible(
        &LEFT,
        &D::ProgressiveContainer(
            &[true, true],
            &["字段🦀", "new"],
            &[&D::ByteVector(2), &BOOL],
        ),
        true,
    );
}

#[test]
fn progressive_distinct_positions_require_distinct_names() {
    const LEFT: D = D::ProgressiveContainer(&[true], &["same"], &[&BYTE]);
    compatible(
        &LEFT,
        &D::ProgressiveContainer(&[false, true], &["same"], &[&BYTE]),
        false,
    );
    compatible(
        &LEFT,
        &D::ProgressiveContainer(&[false, true], &["other"], &[&BOOL]),
        true,
    );
    compatible(
        &D::ProgressiveContainer(&[true], &["a\0b"], &[&BYTE]),
        &D::ProgressiveContainer(&[false, true], &["a\0c"], &[&BYTE]),
        true,
    );
}

#[test]
fn malformed_progressive_layouts_follow_zip_truncation_not_validation_assumptions() {
    const EMPTY: D = D::ProgressiveContainer(&[], &[], &[]);
    compatible(
        &EMPTY,
        &D::ProgressiveContainer(&[true], &[], &[&BAD]),
        true,
    );
    compatible(
        &EMPTY,
        &D::ProgressiveContainer(&[], &["ignored"], &[&BAD]),
        true,
    );
    compatible(
        &D::ProgressiveContainer(&[true], &["a", "ignored"], &[&BYTE, &BOOL]),
        &D::ProgressiveContainer(&[true], &["a"], &[&BYTE]),
        true,
    );
    compatible(
        &D::ProgressiveContainer(&[false, true], &["a"], &[]),
        &D::ProgressiveContainer(&[true], &["b"], &[]),
        true,
    );
    compatible(
        &D::ProgressiveContainer(&[true], &["a"], &[]),
        &D::ProgressiveContainer(&[true, false], &["a"], &[]),
        false,
    );
    // Equality short-circuits even though the shared position has no type.
    compatible(
        &D::ProgressiveContainer(&[true], &["a"], &[]),
        &D::ProgressiveContainer(&[true], &["a"], &[]),
        true,
    );
}

#[test]
fn compatibility_is_not_transitive() {
    const A: D = D::ProgressiveContainer(&[true], &["a"], &[&BYTE]);
    const B: D = D::ProgressiveContainer(&[false, true], &["b"], &[&BYTE]);
    const C: D = D::ProgressiveContainer(&[true], &["c"], &[&BYTE]);
    compatible(&A, &B, true);
    compatible(&B, &C, true);
    compatible(&A, &C, false);
}

#[test]
fn union_comparison_checks_every_cross_pair_and_ignores_selectors() {
    const A: D = D::ProgressiveContainer(&[true], &["a"], &[&BYTE]);
    const B: D = D::ProgressiveContainer(&[false, true], &["b"], &[&BYTE]);
    const C: D = D::ProgressiveContainer(&[true], &["c"], &[&BYTE]);
    compatible(
        &D::CompatibleUnion(&[1], &[&B]),
        &D::CompatibleUnion(&[0, usize::MAX], &[&A, &C]),
        true,
    );
    compatible(
        &D::CompatibleUnion(&[1, 2], &[&A, &B]),
        &D::CompatibleUnion(&[3, 4], &[&B, &C]),
        false,
    );
    compatible(
        &D::CompatibleUnion(&[], &[]),
        &D::CompatibleUnion(&[0], &[&BAD]),
        true,
    );
    compatible(
        &D::CompatibleUnion(&[1], &[&BYTE]),
        &D::CompatibleUnion(&[127], &[&BYTE]),
        true,
    );
    compatible(
        &D::CompatibleUnion(&[1], &[&BYTE]),
        &D::CompatibleUnion(&[1], &[&BOOL]),
        false,
    );
}

#[test]
fn union_structural_equality_shortcuts_even_incompatible_options() {
    const INVALID: D = D::CompatibleUnion(&[0, 0], &[&BYTE, &BOOL]);
    compatible(&INVALID, &INVALID, true);
    compatible(
        &INVALID,
        &D::CompatibleUnion(&[0, 1], &[&BYTE, &BOOL]),
        false,
    );
    assert_eq!(validate(&INVALID), Err(E::UnionSelectorRepeated));
    assert_ne!(
        D::CompatibleUnion(&[1], &[&BYTE]),
        D::CompatibleUnion(&[2], &[&BYTE])
    );
}

#[test]
fn nested_collections_do_not_replace_child_compatibility_with_equality() {
    compatible(
        &D::Vector(&D::ByteList(0), 2),
        &D::Vector(&D::List(&BYTE, 0), 2),
        true,
    );
    compatible(
        &D::List(&D::ProgressiveBitList(None), usize::MAX),
        &D::List(&D::ProgressiveBitList(Some(0)), usize::MAX),
        true,
    );
    compatible(&D::Vector(&BYTE, 2), &D::Vector(&BYTE, 3), false);
    compatible(&D::List(&BOOL, 2), &D::List(&BOOL, 3), false);
    compatible(&D::Vector(&BOOL, 2), &D::Vector(&BYTE, 2), false);
}
