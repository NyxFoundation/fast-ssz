//! Fixed-width SSZ branch verification. Generalized indices use the full u128 range.

use crate::sha256::hash_pair;

/// One complete SSZ Merkle node.
pub type Node = [u8; 32];

/// A malformed branch request, distinct from a well-formed proof that does not match.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofError {
    InvalidIndex,
    RootHasNoBranch,
    InvalidBranchLength,
}

fn climb(current: Node, proof: &[Node], index: u128) -> Node {
    if proof.is_empty() {
        return current;
    }
    let sibling = proof[0];
    let parent = if index % 2 == 1 {
        hash_pair(&sibling, &current)
    } else {
        hash_pair(&current, &sibling)
    };
    climb(parent, &proof[1..], index >> 1u32)
}

/// Reconstruct a root from a leaf and its bottom-up branch.
///
/// Index zero is invalid; the root itself (index one) has no branch in the
/// reference specification. The branch must contain exactly floor(log2(index))
/// siblings. All node widths are enforced by the array types.
pub fn calculate_merkle_root(leaf: &Node, proof: &[Node], index: u128) -> Result<Node, ProofError> {
    if index == 0 {
        return Err(ProofError::InvalidIndex);
    }
    if index == 1 {
        return Err(ProofError::RootHasNoBranch);
    }
    let depth = proof.len();
    if depth >= 128 {
        return Err(ProofError::InvalidBranchLength);
    }
    if index >> depth != 1 {
        return Err(ProofError::InvalidBranchLength);
    }
    Ok(climb(*leaf, proof, index))
}

/// Verify a branch; malformed requests are errors and mismatched roots are false.
pub fn verify_merkle_proof(
    leaf: &Node,
    proof: &[Node],
    index: u128,
    root: &Node,
) -> Result<bool, ProofError> {
    match calculate_merkle_root(leaf, proof, index) {
        Ok(actual) => Ok(actual == *root),
        Err(error) => Err(error),
    }
}
