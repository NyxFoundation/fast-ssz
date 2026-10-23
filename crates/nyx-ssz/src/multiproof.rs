//! SSZ multiproof verification over the full u128 generalized-index range.
//!
//! Allocation failure is a resource boundary, not a mathematical refusal.
//! Helpers are selected directly in descending order without storing claim
//! paths. Reconstruction borrows the two original frontiers separately and
//! uses at most 128 recursive frames, never a combined-frontier vector.

use crate::gindex;
use crate::merkle::{Node, ProofError};
use crate::sha256::hash_pair;

mod helpers;
use helpers::collect_helpers;
pub use helpers::helper_indices;

fn node_at(indices: &[u128], nodes: &[Node], index: u128) -> Option<Node> {
    let mut offset = 0;
    while offset < indices.len() {
        if indices[offset] == index {
            return Some(nodes[offset]);
        }
        offset += 1;
    }
    None
}

fn rebuild(
    leaves: &[Node],
    proof: &[Node],
    indices: &[u128],
    helpers: &[u128],
    index: u128,
    remaining: u32,
) -> Result<Node, ProofError> {
    if let Some(node) = node_at(indices, leaves, index) {
        return Ok(node);
    }
    if let Some(node) = node_at(helpers, proof, index) {
        return Ok(node);
    }
    // This bottom default agrees with the reference's finite frontier tree.
    // Complete helper frontiers always supply a node before this default.
    if remaining == 0 {
        return Ok([0; 32]);
    }
    let left_index = gindex::child(index, false)?;
    let right_index = gindex::child(index, true)?;
    let left = rebuild(leaves, proof, indices, helpers, left_index, remaining - 1)?;
    let right = rebuild(leaves, proof, indices, helpers, right_index, remaining - 1)?;
    Ok(hash_pair(&left, &right))
}

/// Reconstruct the complete root, with count errors preceding helper validation.
///
/// A proof cannot contain more than `usize::MAX` nodes. Selecting just one
/// helper beyond its length therefore establishes exact proof-length refusal,
/// including when the mathematical helper list exceeds the native size range.
pub fn calculate_merkle_root(
    leaves: &[Node],
    proof: &[Node],
    indices: &[u128],
) -> Result<Node, ProofError> {
    if leaves.len() != indices.len() {
        return Err(ProofError::InvalidLeafCount);
    }
    let helpers = collect_helpers(indices, proof.len(), ProofError::InvalidProofLength)?;
    if proof.len() != helpers.len() {
        return Err(ProofError::InvalidProofLength);
    }
    rebuild(leaves, proof, indices, &helpers, 1, 127)
}

/// Malformed requests are errors; well-formed root mismatches are false.
pub fn verify_merkle_proof(
    leaves: &[Node],
    proof: &[Node],
    indices: &[u128],
    root: &Node,
) -> Result<bool, ProofError> {
    match calculate_merkle_root(leaves, proof, indices) {
        Ok(actual) => Ok(actual == *root),
        Err(error) => Err(error),
    }
}
