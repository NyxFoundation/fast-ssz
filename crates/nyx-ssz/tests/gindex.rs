use nyx_ssz::{gindex, merkle::ProofError};

#[test]
fn should_distinguish_depth_from_branch_length_when_the_index_is_root_or_zero() {
    assert_eq!(gindex::depth(0), Err(ProofError::InvalidIndex));
    assert_eq!(gindex::depth(1), Ok(0));
    assert_eq!(gindex::length(0), Err(ProofError::InvalidIndex));
    assert_eq!(gindex::length(1), Err(ProofError::RootHasNoBranch));
    assert_eq!(gindex::depth(u128::MAX), Ok(127));
    assert_eq!(gindex::length(u128::MAX), Ok(127));
    for index in 2..=4096 {
        assert_eq!(gindex::depth(index), Ok(index.ilog2()));
        assert_eq!(gindex::length(index), Ok(index.ilog2()));
    }
}

#[test]
fn should_preserve_raw_tree_operations_when_zero_or_root_are_supplied() {
    assert_eq!(gindex::sibling(0), 1);
    assert_eq!(gindex::sibling(1), 0);
    assert_eq!(gindex::parent(0), 0);
    assert_eq!(gindex::child(0, false), Ok(0));
    assert_eq!(gindex::child(0, true), Ok(1));
    for index in 0..=4096 {
        assert_eq!(gindex::parent(index), index / 2);
        assert_eq!(gindex::sibling(index), index ^ 1);
        assert_eq!(gindex::child(index, false), Ok(index * 2));
        assert_eq!(gindex::child(index, true), Ok(index * 2 + 1));
    }
}

#[test]
fn should_reject_unrepresentable_children_when_the_top_bit_is_set() {
    assert_eq!(
        gindex::child(u128::MAX, false),
        Err(ProofError::IndexOverflow)
    );
    assert_eq!(
        gindex::child(u128::MAX, true),
        Err(ProofError::IndexOverflow)
    );
    assert_eq!(gindex::child(u128::MAX / 2, true), Ok(u128::MAX));
    assert_eq!(
        gindex::child(1 << 127, false),
        Err(ProofError::IndexOverflow)
    );
}

#[test]
fn should_zero_extend_bit_queries_and_truncation_when_depth_exceeds_the_word() {
    for position in [0, 1, 63, 64, 126, 127, 128, 129, u32::MAX] {
        assert_eq!(gindex::bit(u128::MAX, position), position < 128);
        assert!(!gindex::bit(0, position));
        assert_eq!(
            gindex::below(u128::MAX, position),
            1_u128
                .checked_shl(position)
                .map_or(u128::MAX, |base| base - 1)
        );
    }
    assert_eq!(gindex::below(40, 4), 8);
    assert_eq!(gindex::below(40, 0), 0);
}

#[test]
fn should_splice_paths_instead_of_multiplying_when_indices_are_concatenated() {
    assert_eq!(gindex::concat(2, 24), Ok(40));
    assert_eq!(gindex::concat(1, u128::MAX), Ok(u128::MAX));
    assert_eq!(gindex::concat(u128::MAX, 1), Ok(u128::MAX));
    assert_eq!(gindex::concat(0, 24), Err(ProofError::InvalidIndex));
    assert_eq!(gindex::concat(2, 0), Err(ProofError::InvalidIndex));
    assert_eq!(gindex::concat(2, 1 << 127), Err(ProofError::IndexOverflow));
    assert_eq!(gindex::concat(u128::MAX, 3), Err(ProofError::IndexOverflow));
}

#[test]
fn should_rebase_subtree_paths_when_the_result_fits_the_word() {
    assert_eq!(gindex::rebase(40, 4), Ok(24));
    assert_eq!(gindex::rebase(u128::MAX, 127), Ok(u128::MAX));
    assert_eq!(gindex::rebase(u128::MAX, 0), Ok(1));
    assert_eq!(gindex::rebase(0, 127), Ok(1 << 127));
    assert_eq!(gindex::rebase(0, 128), Err(ProofError::IndexOverflow));
    assert_eq!(gindex::rebase(1, u32::MAX), Err(ProofError::IndexOverflow));
}

#[test]
fn should_recover_inner_paths_when_small_indices_are_spliced_and_rebased() {
    for outer in 1..=63 {
        for inner in 1_u128..=128 {
            let depth = inner.ilog2();
            let base = 1_u128 << depth;
            let joined = gindex::concat(outer, inner).unwrap();
            assert_eq!(joined, outer * base + inner - base);
            assert_eq!(gindex::rebase(joined, depth), Ok(inner));
        }
    }
}

#[test]
fn should_return_bottom_up_paths_and_siblings_when_a_branch_exists() {
    assert_eq!(gindex::path_indices(24), Ok(vec![24, 12, 6, 3]));
    assert_eq!(gindex::branch_indices(24), Ok(vec![25, 13, 7, 2]));
    assert_eq!(gindex::path_indices(0), Err(ProofError::InvalidIndex));
    assert_eq!(gindex::branch_indices(1), Err(ProofError::RootHasNoBranch));
    let longest = gindex::path_indices(u128::MAX).unwrap();
    assert_eq!(longest.len(), 127);
    assert_eq!(longest[0], u128::MAX);
    assert_eq!(longest[126], 3);
}
