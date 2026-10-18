# fast-ssz

Rust SSZ: Aeneas/Lean proofs before optimization.
**Initial codec slice, not a complete SSZ library or production release.**
Publishing is disabled; no performance superiority is claimed.

Boolean and borrowed ByteVector/ByteList encode/decode are implemented and proved,
including malformed inputs and illegal zero-length vector declarations.
See [verification scope and trust](docs/verification.md).

Integers, bitfields, generic collections, containers, Progressive types,
CompatibleUnion, derive, SHA-256, roots, indices, Merkle proofs, official vectors
and benchmarks remain unfinished. The agreed release condition is not met.

## Example

```rust
use fast_ssz::scalar::{decode_bool, encode_bool};
assert_eq!(encode_bool(true), [1]);
assert_eq!(decode_bool(&[1]), Ok(true));
assert!(decode_bool(&[2]).is_err());
```

Add `fast-ssz = { path = "../fast-ssz/crates/fast-ssz" }` to Cargo's
`[dependencies]`, adjusting the checkout path.

## Reproduce

Requires Linux x86_64, Git, Python 3.11+, Rustup/Cargo, Elan and network access.
Proof dependencies are large.

```sh
cargo test --workspace
cargo install cargo-hax --version 0.4.0 --locked
python3 scripts/verify.py bootstrap
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py check
```

After Rust edits, run `python3 scripts/verify.py extract`, review the generated diff,
update proofs, then rerun `check`. Never hand-edit `verification/FastSszRust.lean`.
Success covers the implemented slice only.

MIT; see [third-party notices](THIRD_PARTY_NOTICES.md).
