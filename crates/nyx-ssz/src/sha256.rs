//! SSZ Merkle-parent hashing through RustCrypto's standard SHA-256 backend.
use sha2::{Digest, Sha256};

/// Hash exactly two 32-byte nodes in left/right order without heap allocation.
///
/// RustCrypto selects its supported CPU backend. No local SHA implementation,
/// custom fallback, or runtime proof evaluation is used.
#[inline]
pub fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut input = [0; 64];
    input[..32].copy_from_slice(left);
    input[32..].copy_from_slice(right);
    Sha256::digest(input).into()
}
