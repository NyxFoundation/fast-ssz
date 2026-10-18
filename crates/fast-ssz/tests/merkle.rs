use fast_ssz::{
    merkle::{calculate_merkle_root, verify_merkle_proof, ProofError},
    sha256::hash_pair,
};
use sha2::{Digest, Sha256};

fn reference_parent(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut digest = Sha256::new();
    digest.update(left);
    digest.update(right);
    digest.finalize().into()
}

#[test]
fn should_verify_both_children_with_bottom_up_branches() {
    let left = [0x11; 32];
    let right = [0x22; 32];
    let root = hash_pair(&left, &right);
    assert_eq!(calculate_merkle_root(&left, &[right], 2), Ok(root));
    assert_eq!(calculate_merkle_root(&right, &[left], 3), Ok(root));
    assert_eq!(verify_merkle_proof(&left, &[right], 2, &root), Ok(true));
    assert_eq!(verify_merkle_proof(&right, &[left], 3, &root), Ok(true));
}

#[test]
fn should_verify_every_leaf_of_a_two_level_tree() {
    let leaves = [[0x10; 32], [0x20; 32], [0x30; 32], [0x40; 32]];
    let parents = [
        hash_pair(&leaves[0], &leaves[1]),
        hash_pair(&leaves[2], &leaves[3]),
    ];
    let root = hash_pair(&parents[0], &parents[1]);
    for (position, leaf) in leaves.iter().enumerate() {
        let branch = [leaves[position ^ 1], parents[(position / 2) ^ 1]];
        assert_eq!(
            calculate_merkle_root(leaf, &branch, 4 + position as u128),
            Ok(root)
        );
        assert_eq!(
            verify_merkle_proof(leaf, &branch, 4 + position as u128, &root),
            Ok(true)
        );
    }
}

#[test]
fn should_return_false_for_wrong_roots_leaves_or_branch_order() {
    let leaf = [1; 32];
    let branch = [[2; 32], [3; 32]];
    let root = reference_parent(&reference_parent(&leaf, &branch[0]), &branch[1]);
    assert_eq!(verify_merkle_proof(&leaf, &branch, 4, &root), Ok(true));
    assert_eq!(verify_merkle_proof(&[9; 32], &branch, 4, &root), Ok(false));
    assert_eq!(verify_merkle_proof(&leaf, &branch, 4, &[9; 32]), Ok(false));
    assert_eq!(
        verify_merkle_proof(&leaf, &[branch[1], branch[0]], 4, &root),
        Ok(false)
    );
}

#[test]
fn should_reject_zero_and_the_root_as_branch_indices() {
    for proof in [vec![], vec![[1; 32]]] {
        assert_eq!(
            calculate_merkle_root(&[0; 32], &proof, 0),
            Err(ProofError::InvalidIndex)
        );
        assert_eq!(
            calculate_merkle_root(&[0; 32], &proof, 1),
            Err(ProofError::RootHasNoBranch)
        );
        assert_eq!(
            verify_merkle_proof(&[0; 32], &proof, 0, &[0; 32]),
            Err(ProofError::InvalidIndex)
        );
    }
}

#[test]
fn should_reject_missing_extra_and_overlong_siblings_without_panicking() {
    for length in [0, 1, 3, 127, 128, 129] {
        let proof = vec![[0; 32]; length];
        assert_eq!(
            calculate_merkle_root(&[0; 32], &proof, 4),
            Err(ProofError::InvalidBranchLength)
        );
        assert_eq!(
            verify_merkle_proof(&[0; 32], &proof, 4, &[0; 32]),
            Err(ProofError::InvalidBranchLength)
        );
    }
}

#[test]
fn should_support_the_full_128_bit_generalized_index_domain() {
    let leaf = [0x5a; 32];
    let proof = [[0; 32]; 127];
    for index in [1u128 << 127, u128::MAX] {
        let mut expected = leaf;
        let mut remaining = index;
        for sibling in &proof {
            expected = if remaining & 1 == 1 {
                reference_parent(sibling, &expected)
            } else {
                reference_parent(&expected, sibling)
            };
            remaining >>= 1;
        }
        assert_eq!(calculate_merkle_root(&leaf, &proof, index), Ok(expected));
        assert_eq!(
            verify_merkle_proof(&leaf, &proof, index, &expected),
            Ok(true)
        );
    }
}
