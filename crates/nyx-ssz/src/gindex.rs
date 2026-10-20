//! Generalized-index arithmetic over the full u128 representation.
//!
//! Tree primitives preserve the reference's raw zero/root behavior. Operations
//! that require a branch reject zero and the root explicitly. Unrepresentable
//! mathematical results return `IndexOverflow`, never truncated indices.

use crate::merkle::ProofError;

/// Return floor(log2(index)); the root has depth zero and index zero is invalid.
pub fn depth(index: u128) -> Result<u32, ProofError> {
    if index == 0 {
        return Err(ProofError::InvalidIndex);
    }
    Ok(127 - index.leading_zeros())
}

/// Return a branch's sibling count, rejecting the root's nonexistent branch.
pub fn length(index: u128) -> Result<u32, ProofError> {
    if index == 1 {
        return Err(ProofError::RootHasNoBranch);
    }
    depth(index)
}

/// Read a turn bit from the leaf; positions beyond the word are false.
#[must_use]
pub fn bit(index: u128, position: u32) -> bool {
    if position >= 128 {
        return false;
    }
    (index >> position) & 1 == 1
}

/// Keep the bottom `depth` turns, with zero extension beyond the word width.
#[must_use]
pub fn below(index: u128, depth: u32) -> u128 {
    if depth >= 128 {
        return index;
    }
    index % (1_u128 << depth)
}

/// Return the neighboring index, including the reference's zero/root behavior.
#[must_use]
pub fn sibling(index: u128) -> u128 {
    index ^ 1
}

/// Return one child, or reject a mathematical result beyond u128.
pub fn child(index: u128, right_side: bool) -> Result<u128, ProofError> {
    let doubled = match index.checked_mul(2) {
        Some(value) => value,
        None => return Err(ProofError::IndexOverflow),
    };
    let turn = if right_side { 1 } else { 0 };
    match doubled.checked_add(turn) {
        Some(value) => Ok(value),
        None => Err(ProofError::IndexOverflow),
    }
}

/// Return the parent; zero and the root both have raw parent zero.
#[must_use]
pub fn parent(index: u128) -> u128 {
    index / 2
}

/// Splice an inner path onto an outer index, dropping the inner leading bit.
pub fn concat(outer: u128, inner: u128) -> Result<u128, ProofError> {
    depth(outer)?;
    let inner_depth = depth(inner)?;
    let base = 1_u128 << inner_depth;
    let prefix = match outer.checked_mul(base) {
        Some(value) => value,
        None => return Err(ProofError::IndexOverflow),
    };
    match prefix.checked_add(inner - base) {
        Some(value) => Ok(value),
        None => Err(ProofError::IndexOverflow),
    }
}

/// Read the bottom turns as a subtree index, or reject an unrepresentable depth.
pub fn rebase(index: u128, depth: u32) -> Result<u128, ProofError> {
    if depth >= 128 {
        return Err(ProofError::IndexOverflow);
    }
    Ok((1_u128 << depth) + below(index, depth))
}

/// Return a bottom-up path excluding the root, refusing nonexistent branches.
pub fn path_indices(index: u128) -> Result<Vec<u128>, ProofError> {
    let count = length(index)?;
    let mut path = Vec::new();
    let mut level = 0;
    while level < count {
        path.push(index >> level);
        level += 1;
    }
    Ok(path)
}

/// Return bottom-up sibling indices in the exact order a branch proof uses.
pub fn branch_indices(index: u128) -> Result<Vec<u128>, ProofError> {
    let count = length(index)?;
    let mut siblings = Vec::new();
    let mut level = 0;
    while level < count {
        siblings.push((index >> level) ^ 1);
        level += 1;
    }
    Ok(siblings)
}
