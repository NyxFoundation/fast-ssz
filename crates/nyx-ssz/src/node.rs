//! Sparse tree access from canonical typed encodings. Padding is never allocated.
use crate::{
    codec::Ssz,
    gindex,
    merkle::{Node, ProofError},
    path::{AccessError, Step},
    sha256::hash_pair,
    type_info::{self, TypeDescriptor as D},
};
mod layout;

pub(crate) enum Tree {
    Leaf(Node),
    Zero(u32),
    Branch(Node, Box<Tree>, Box<Tree>),
}

impl Tree {
    fn branch(left: Self, right: Self) -> Self {
        Self::Branch(
            hash_pair(&left.root(), &right.root()),
            Box::new(left),
            Box::new(right),
        )
    }
    pub(crate) fn root(&self) -> Node {
        match self {
            Self::Leaf(node) | Self::Branch(node, _, _) => *node,
            Self::Zero(depth) => zero_root(*depth),
        }
    }
    pub(crate) fn get(&self, index: u128) -> Result<Node, AccessError> {
        let depth = gindex::depth(index)?;
        self.descend(index, depth)
    }
    fn descend(&self, index: u128, remaining: u32) -> Result<Node, AccessError> {
        if remaining == 0 {
            return Ok(self.root());
        }
        match self {
            Self::Branch(_, left, right) => if gindex::bit(index, remaining - 1) {
                right
            } else {
                left
            }
            .descend(index, remaining - 1),
            Self::Zero(depth) if remaining <= *depth => Ok(zero_root(*depth - remaining)),
            _ => Err(ProofError::InvalidIndex.into()),
        }
    }
}

fn zero_root(depth: u32) -> Node {
    let mut node = [0; 32];
    for _ in 0..depth {
        node = hash_pair(&node, &node);
    }
    node
}

fn bounded(leaves: &[Tree], capacity: usize) -> Result<Tree, AccessError> {
    if leaves.len() > capacity {
        return Err(ProofError::InvalidLeafCount.into());
    }
    let depth = if capacity <= 1 {
        0
    } else {
        usize::BITS - (capacity - 1).leading_zeros()
    };
    Ok(subtree(leaves, depth))
}

fn subtree(leaves: &[Tree], depth: u32) -> Tree {
    if leaves.is_empty() {
        return Tree::Zero(depth);
    }
    if depth == 0 {
        return clone_tree(&leaves[0]);
    }
    let half = 1usize << (depth - 1);
    let split = leaves.len().min(half);
    Tree::branch(
        subtree(&leaves[..split], depth - 1),
        subtree(&leaves[split..], depth - 1),
    )
}

fn clone_tree(tree: &Tree) -> Tree {
    match tree {
        Tree::Leaf(node) => Tree::Leaf(*node),
        Tree::Zero(depth) => Tree::Zero(*depth),
        Tree::Branch(root, left, right) => Tree::Branch(
            *root,
            Box::new(clone_tree(left)),
            Box::new(clone_tree(right)),
        ),
    }
}

fn progressive(leaves: &[Tree], depth: u32) -> Tree {
    if leaves.is_empty() {
        return Tree::Leaf([0; 32]);
    }
    let width = 1u128 << depth;
    let split = leaves.len().min(width.min(usize::MAX as u128) as usize);
    Tree::branch(
        subtree(&leaves[..split], depth),
        progressive(&leaves[split..], depth + 2),
    )
}

fn packed(bytes: &[u8], capacity: Option<usize>, word: Option<Node>) -> Result<Tree, AccessError> {
    let leaves: Vec<_> = bytes
        .chunks(32)
        .map(|bytes| {
            let mut node = [0; 32];
            node[..bytes.len()].copy_from_slice(bytes);
            Tree::Leaf(node)
        })
        .collect();
    let tree = match capacity {
        Some(limit) => bounded(&leaves, limit)?,
        None => progressive(&leaves, 0),
    };
    Ok(match word {
        Some(word) => Tree::branch(tree, Tree::Leaf(word)),
        None => tree,
    })
}

fn length_word(count: u128) -> Node {
    let mut word = [0; 32];
    word[..16].copy_from_slice(&count.to_le_bytes());
    word
}

pub(crate) fn build<T: Ssz>(value: &T) -> Result<Tree, AccessError> {
    type_info::validate(T::TYPE)?;
    layout::from_bytes(T::TYPE, &value.encode()?)
}

/// Read any existing node, including the root at index one.
pub fn get<T: Ssz>(value: &T, index: u128) -> Result<Node, AccessError> {
    build(value)?.get(index)
}

/// Resolve a declared type path, then read its node (packed elements share nodes).
pub fn at_path<T: Ssz>(value: &T, steps: &[Step<'_>]) -> Result<Node, AccessError> {
    get(value, crate::path::resolve::<T>(steps)?.generalized_index)
}
