//! Hash-independent generalized-index helper selection.
use crate::{gindex, merkle::ProofError};

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

pub(super) fn collect_helpers(
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
