//! Identical deterministic SSZ schemas for cross-library measurements.
pub mod nyx;
pub mod reference;

use libssz::{SszDecode, SszEncode};
use libssz_merkle::{HashTreeRoot, Sha2Hasher};
use nyx_ssz::codec::Ssz;
use sha2::{Digest, Sha256};

pub fn root_bytes(seed: u8) -> [u8; 32] {
    std::array::from_fn(|i| seed.wrapping_add(i as u8))
}

/// Refuse measurements unless both Rust implementations agree exactly.
pub fn checked_fixture<N, L>(name: &str, nyx: N, reference: L) -> serde_json::Value
where
    N: Ssz,
    L: SszEncode + SszDecode + HashTreeRoot,
{
    let bytes = nyx.encode().unwrap();
    let root = nyx.hash_tree_root().unwrap();
    assert_eq!(bytes, reference.to_ssz(), "encoding disagreement");
    assert_eq!(
        root,
        reference.hash_tree_root(&Sha2Hasher),
        "root disagreement"
    );
    assert_eq!(N::decode(&bytes).unwrap().encode().unwrap(), bytes);
    assert_eq!(L::from_ssz_bytes(&bytes).unwrap().to_ssz(), bytes);
    serde_json::json!({ "name": name, "bytes": bytes.len(), "wire": hex::encode(&bytes),
        "root": hex::encode(root), "sha256": hex::encode(Sha256::digest(&bytes)) })
}

pub fn fixtures() -> serde_json::Value {
    serde_json::json!([
        checked_fixture("header", nyx::header(), reference::header()),
        checked_fixture("mixed", nyx::mixed(), reference::mixed())
    ])
}

#[cfg(test)]
mod tests {
    #[test]
    fn should_match_canonical_wire_and_roots_when_shared_fixtures_are_constructed() {
        let fixtures = super::fixtures();
        assert_eq!(fixtures[0]["bytes"], 112);
        assert_eq!(fixtures[1]["bytes"], 12304);
        let bytes = hex::decode(fixtures[1]["wire"].as_str().unwrap()).unwrap();
        assert_eq!(
            &bytes[..16],
            &[42, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 16, 16, 0, 0]
        );
    }
}
