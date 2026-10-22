//! SSZ multiproof verification over the full u128 generalized-index range.
//!
//! Allocation failure is a resource boundary, not a mathematical refusal.
//! Helpers are selected directly in descending order without storing claim
//! paths. Reconstruction borrows the two original frontiers separately and
//! uses at most 128 recursive frames, never a combined-frontier vector.

use crate::gindex;
use crate::merkle::{Node, ProofError};
use crate::sha256::hash_pair;

fn reject_repeated(indices: &[u128]) -> Result<(), ProofError> {
    let mut offset = 0;
    while offset < indices.len() {
        if indices[..offset].contains(&indices[offset]) {
            return Err(ProofError::RepeatedIndex);
        }
        offset += 1;
    }
    Ok(())
}

fn validate_claim(indices: &[u128], index: u128) -> Result<(), ProofError> {
    gindex::length(index)?;
    let mut ancestor = gindex::parent(index);
    while ancestor > 1 {
        if indices.contains(&ancestor) {
            return Err(ProofError::NestedIndex);
        }
        ancestor = gindex::parent(ancestor);
    }
    Ok(())
}

fn validate(indices: &[u128]) -> Result<(), ProofError> {
    if indices.is_empty() {
        return Err(ProofError::EmptyRequest);
    }
    reject_repeated(indices)?;
    for &index in indices {
        validate_claim(indices, index)?;
    }
    Ok(())
}

fn claim_path(mut node: u128, candidate: u128) -> bool {
    while node > 1 {
        if node == candidate {
            return true;
        }
        node = gindex::parent(node);
    }
    false
}

fn on_path(indices: &[u128], candidate: u128) -> bool {
    for &index in indices {
        if claim_path(index, candidate) {
            return true;
        }
    }
    false
}

fn next_helper(indices: &[u128], upper: u128) -> u128 {
    let mut best = 0;
    for &index in indices {
        let mut node = index;
        while node > 1 {
            let sibling = gindex::sibling(node);
            if sibling <= upper && sibling > best && !on_path(indices, sibling) {
                best = sibling;
            }
            node = gindex::parent(node);
        }
    }
    best
}

fn collect_helpers(
    indices: &[u128],
    capacity: usize,
    overflow: ProofError,
) -> Result<Vec<u128>, ProofError> {
    validate(indices)?;
    let mut helpers = Vec::new();
    let mut upper = u128::MAX;
    loop {
        let next = next_helper(indices, upper);
        if next == 0 {
            return Ok(helpers);
        }
        if helpers.len() == capacity {
            return Err(overflow);
        }
        helpers.push(next);
        upper = next - 1;
    }
}

/// Exact descending helpers, refusing malformed requests in specification order.
///
/// `SizeOverflow` means precisely that the natural-number reference helper
/// list has more than `usize::MAX` entries. No path or working-set budget is
/// imposed. The full request is validated before any size refusal.
pub fn helper_indices(indices: &[u128]) -> Result<Vec<u128>, ProofError> {
    collect_helpers(indices, usize::MAX, ProofError::SizeOverflow)
}

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
