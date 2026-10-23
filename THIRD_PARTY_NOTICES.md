# Third-party notices

The axiom audit adapts [ethereum/ssz-specs](https://github.com/ethereum/ssz-specs)
(MIT); its copyright/permission notice is in LICENSE. Source pins are in sources.lock.
The multiproof frontier, antichain, fold and finite-tree compatibility proofs also
adapt lemmas from that pinned source under the project's Lean toolchain.
Runtime SHA-256 uses RustCrypto sha2 0.10.9 under MIT OR Apache-2.0,
including its standard CPU-dispatched backend. Its MIT copyright/permission notice
is preserved in LICENSE. No local scalar SHA implementation or custom fallback remains.
Older generated Lean hash models are historical artifacts, not proof of RustCrypto.
The production `U256` type uses ruint 1.20.1 (MIT). Extracted reachable definitions
include ruint's limb access/construction and Rust's `usize::div_ceil`; their
copyright/permission notices are preserved in LICENSE. Cargo.lock pins ruint and
its compile-time ruint-macro dependency. Other ruint APIs are not part of these proofs.
Fetched SSZ/Aeneas/Lean dependencies retain upstream licenses.
Official test data is fetched, not vendored, from the pinned ethereum/consensus-spec-tests
repository (MIT). The sparse checkout retains its upstream LICENSE. The separate test-only
runner uses yaml_serde, snap and hex under their upstream licenses; its Cargo.lock pins them.
Current-version Progressive root expectations use a separately fetched, SHA-256-authenticated
ethereum/remerkleable source revision (MIT), pinned in sources.lock. Its archive retains LICENSE;
no reference source is vendored into the SSZ runtime.
