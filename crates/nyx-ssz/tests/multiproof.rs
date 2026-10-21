use nyx_ssz::{gindex, merkle::Node, merkle::ProofError, multiproof, sha256::hash_pair};

fn tree() -> Vec<Node> {
    let mut nodes = vec![[0; 32]; 16];
    for (i, node) in nodes.iter_mut().enumerate().skip(8) {
        *node = [i as u8; 32];
    }
    for i in (1..8).rev() {
        nodes[i] = hash_pair(&nodes[2 * i], &nodes[2 * i + 1]);
    }
    nodes
}

#[test]
fn siblings_need_no_helpers() {
    let nodes = tree();
    assert_eq!(multiproof::helper_indices(&[2, 3]), Ok(vec![]));
    assert_eq!(
        multiproof::calculate_merkle_root(&[nodes[3], nodes[2]], &[], &[3, 2]),
        Ok(nodes[1])
    );
}

#[test]
fn independent_explicit_tree_and_shared_helpers() {
    let nodes = tree();
    assert_eq!(
        multiproof::helper_indices(&[8, 10, 14]),
        Ok(vec![15, 11, 9, 6])
    );
    let leaves = [nodes[8], nodes[10], nodes[14]];
    let proof = [nodes[15], nodes[11], nodes[9], nodes[6]];
    assert_eq!(
        multiproof::calculate_merkle_root(&leaves, &proof, &[8, 10, 14]),
        Ok(nodes[1])
    );
    assert_eq!(
        multiproof::verify_merkle_proof(&leaves, &proof, &[8, 10, 14], &nodes[1]),
        Ok(true)
    );
    let mut wrong = proof;
    wrong.swap(0, 1);
    assert_eq!(
        multiproof::verify_merkle_proof(&leaves, &wrong, &[8, 10, 14], &nodes[1]),
        Ok(false)
    );
    wrong = proof;
    wrong[2][0] ^= 1;
    assert_eq!(
        multiproof::verify_merkle_proof(&leaves, &wrong, &[8, 10, 14], &nodes[1]),
        Ok(false)
    );
    assert_eq!(
        multiproof::verify_merkle_proof(&leaves, &proof, &[8, 10, 14], &[0; 32]),
        Ok(false)
    );
}

#[test]
fn partial_helper_collection_refuses_exact_proof_length() {
    let nodes = tree();
    let indices = [8, 10, 14];
    let leaves = [nodes[8], nodes[10], nodes[14]];
    for count in [0, 1, 2, 3, 5] {
        let proof = vec![[0; 32]; count];
        assert_eq!(
            multiproof::calculate_merkle_root(&leaves, &proof, &indices),
            Err(ProofError::InvalidProofLength)
        );
    }
}

#[test]
fn complete_frontiers_in_every_order() {
    let nodes = tree();
    for mask in 1u16..256 {
        let indices: Vec<_> = (8..16)
            .rev()
            .filter(|i| mask & (1 << (i - 8)) != 0)
            .collect();
        let helpers = multiproof::helper_indices(&indices).unwrap();
        assert!(helpers.windows(2).all(|pair| pair[0] > pair[1]));
        let leaves: Vec<_> = indices.iter().map(|i| nodes[*i as usize]).collect();
        let proof: Vec<_> = helpers.iter().map(|i| nodes[*i as usize]).collect();
        assert_eq!(
            multiproof::calculate_merkle_root(&leaves, &proof, &indices),
            Ok(nodes[1])
        );
    }
    assert_eq!(multiproof::helper_indices(&[4, 5, 3]), Ok(vec![]));
    assert_eq!(
        multiproof::calculate_merkle_root(&[nodes[4], nodes[5], nodes[3]], &[], &[4, 5, 3]),
        Ok(nodes[1])
    );
}

#[test]
fn validation_and_error_precedence() {
    use ProofError::*;
    assert_eq!(multiproof::helper_indices(&[]), Err(EmptyRequest));
    assert_eq!(multiproof::helper_indices(&[0, 0]), Err(RepeatedIndex));
    assert_eq!(multiproof::helper_indices(&[1, 1]), Err(RepeatedIndex));
    assert_eq!(multiproof::helper_indices(&[0, 1]), Err(InvalidIndex));
    assert_eq!(multiproof::helper_indices(&[1, 0]), Err(RootHasNoBranch));
    assert_eq!(multiproof::helper_indices(&[4, 2, 0]), Err(NestedIndex));
    assert_eq!(multiproof::helper_indices(&[0, 4, 2]), Err(InvalidIndex));
    assert_eq!(multiproof::helper_indices(&[2, 4]), Err(NestedIndex));
    assert_eq!(multiproof::helper_indices(&[4, 1]), Err(RootHasNoBranch));
    assert_eq!(
        multiproof::calculate_merkle_root(&[], &[], &[0, 0]),
        Err(InvalidLeafCount)
    );
    assert_eq!(
        multiproof::calculate_merkle_root(&[], &[], &[]),
        Err(EmptyRequest)
    );
    assert_eq!(
        multiproof::calculate_merkle_root(&[[0; 32]], &[], &[2]),
        Err(InvalidProofLength)
    );
    assert_eq!(
        multiproof::calculate_merkle_root(&[[0; 32]; 2], &[[0; 32]], &[2, 3]),
        Err(InvalidProofLength)
    );
}

#[test]
fn verification_preserves_all_validation_errors_before_proof_length() {
    use ProofError::*;
    let cases: &[(&[u128], ProofError)] = &[
        (&[], EmptyRequest),
        (&[0, 0], RepeatedIndex),
        (&[1], RootHasNoBranch),
        (&[2, 0], InvalidIndex),
        (&[4, 2, 0], NestedIndex),
        (&[0, 4, 2], InvalidIndex),
        (&[2], InvalidProofLength),
    ];
    for &(indices, error) in cases {
        let leaves = vec![[0; 32]; indices.len()];
        assert_eq!(
            multiproof::calculate_merkle_root(&leaves, &[], indices),
            Err(error)
        );
        assert_eq!(
            multiproof::verify_merkle_proof(&leaves, &[], indices, &[0; 32]),
            Err(error)
        );
    }
    assert_eq!(
        multiproof::verify_merkle_proof(&[], &[], &[0, 0], &[0; 32]),
        Err(InvalidLeafCount)
    );
}

#[test]
fn all_u128_depths_and_top_bit_siblings() {
    let mut indices = vec![2, 3, 1 << 127, u128::MAX, (1 << 127) + 12345];
    indices.extend((1..128).map(|depth| 1u128 << depth));
    for index in indices {
        let helpers = multiproof::helper_indices(&[index]).unwrap();
        let mut branch = gindex::branch_indices(index).unwrap();
        branch.sort_unstable_by(|a, b| b.cmp(a));
        assert_eq!(helpers, branch);
        let proof = vec![[17; 32]; helpers.len()];
        let expected = nyx_ssz::merkle::calculate_merkle_root(&[42; 32], &proof, index);
        assert_eq!(
            multiproof::calculate_merkle_root(&[[42; 32]], &proof, &[index]),
            expected
        );
    }
    let indices = [u128::MAX, u128::MAX - 1];
    let helpers = multiproof::helper_indices(&indices).unwrap();
    assert_eq!(helpers.len(), 126);
    let expected = nyx_ssz::merkle::calculate_merkle_root(
        &hash_pair(&[1; 32], &[2; 32]),
        &vec![[3; 32]; 126],
        u128::MAX / 2,
    );
    assert_eq!(
        multiproof::calculate_merkle_root(&[[2; 32], [1; 32]], &vec![[3; 32]; 126], &indices),
        expected
    );
}
