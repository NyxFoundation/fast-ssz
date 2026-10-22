//! Proof construction. Verification remains in merkle and multiproof.
use crate::{
    codec::Ssz,
    gindex,
    merkle::Node,
    multiproof, node,
    path::{self, AccessError, Step},
};

#[derive(Debug, Eq, PartialEq)]
pub struct Branch {
    pub index: u128,
    pub leaf: Node,
    pub siblings: Vec<Node>,
    pub root: Node,
}

#[derive(Debug, Eq, PartialEq)]
pub struct MultiProof {
    pub indices: Vec<u128>,
    pub leaves: Vec<Node>,
    pub helpers: Vec<Node>,
    pub root: Node,
}

/// Construct a bottom-up branch, rejecting root and zero requests.
pub fn create<T: Ssz>(value: &T, index: u128) -> Result<Branch, AccessError> {
    let indices = gindex::branch_indices(index)?;
    let tree = node::build(value)?;
    let leaf = tree.get(index)?;
    let siblings = indices
        .iter()
        .map(|&i| tree.get(i))
        .collect::<Result<_, _>>()?;
    Ok(Branch {
        index,
        leaf,
        siblings,
        root: tree.root(),
    })
}

pub fn at_path<T: Ssz>(value: &T, steps: &[Step<'_>]) -> Result<Branch, AccessError> {
    create(value, path::resolve::<T>(steps)?.generalized_index)
}

/// Preserve claim order; helpers use the verifier's canonical descending order.
pub fn create_multi<T: Ssz>(value: &T, indices: &[u128]) -> Result<MultiProof, AccessError> {
    let helpers = multiproof::helper_indices(indices)?;
    let tree = node::build(value)?;
    let leaves = indices
        .iter()
        .map(|&i| tree.get(i))
        .collect::<Result<_, _>>()?;
    let helpers = helpers
        .iter()
        .map(|&i| tree.get(i))
        .collect::<Result<_, _>>()?;
    Ok(MultiProof {
        indices: indices.to_vec(),
        leaves,
        helpers,
        root: tree.root(),
    })
}
