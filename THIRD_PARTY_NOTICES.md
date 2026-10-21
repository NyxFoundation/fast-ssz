# Third-party notices

The axiom audit adapts [ethereum/ssz-specs](https://github.com/ethereum/ssz-specs)
(MIT); its copyright/permission notice is in LICENSE. Source pins are in sources.lock.
The SHA-256 implementation follows FIPS 180-4 and the pinned SSZ model, with
RustCrypto sha2 0.10.9's portable compression implementation consulted under MIT.
Its copyright/permission notice is preserved in LICENSE. The sha2 crate itself
is a dev-only differential-test oracle.
The production `U256` type uses ruint 1.20.1 (MIT). Extracted reachable definitions
include ruint's limb access/construction and Rust's `usize::div_ceil`; their
copyright/permission notices are preserved in LICENSE. Cargo.lock pins ruint and
its compile-time ruint-macro dependency. Other ruint APIs are not part of these proofs.
Fetched SSZ/Aeneas/Lean dependencies retain upstream licenses.
Official test data is fetched, not vendored, from the pinned ethereum/consensus-spec-tests
repository (MIT). The sparse checkout retains its upstream LICENSE. The separate test-only
runner uses yaml_serde, snap and hex under their upstream licenses; its Cargo.lock pins them.
