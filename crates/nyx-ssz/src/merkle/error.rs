//! Hash-independent proof request errors, re-exported by the public merkle module.

/// Proof-request errors, distinct from well-formed root mismatches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofError {
    InvalidIndex,
    RootHasNoBranch,
    InvalidBranchLength,
    IndexOverflow,
    EmptyRequest,
    RepeatedIndex,
    NestedIndex,
    InvalidLeafCount,
    InvalidProofLength,
    SizeOverflow,
}
