# fast-ssz

A specification-first Rust SSZ project. The long-term goal is the fastest Rust SSZ
library, with implementation/specification correspondence maintained through Aeneas and Lean.

**This is an initial verified codec slice, not the requested complete SSZ library
or a production release.** Publishing is disabled. There is no fastest-library claim.

## Implemented and proved

- Boolean encode/decode, including every malformed input slice.
- Borrowed ByteVector and ByteList encode/decode, including invalid lengths,
  over-limit inputs, empty values, and illegal zero-length vector declarations.
- Six codec functions are extracted from the actual Rust source by Charon/Aeneas.
  Lean theorems relate their results to the pinned upstream specification.
  Every implemented codec terminates successfully in the extracted model, returning
  either a value or a corresponding SSZ error rather than a Rust panic.

Unsigned integers, bitfields, generic collections, containers, Progressive types,
CompatibleUnion, derive, SHA-256, hash-tree roots, indices, and Merkle proofs are
**not implemented yet**. Official vector replay and performance comparisons are also outstanding.
See [verification scope and trust boundary](docs/verification.md).

## Use the current slice

```rust
use fast_ssz::{bytes::decode_byte_list, scalar::{decode_bool, encode_bool}};

assert_eq!(encode_bool(true), [1]);
assert_eq!(decode_bool(&[1]), Ok(true));
assert!(decode_bool(&[2]).is_err());

let encoded = [0xde, 0xad];
let decoded = decode_byte_list(&encoded, 32).unwrap();
assert_eq!(decoded, encoded); // Borrows the input; no copy.
```

From another local Cargo project, add a path dependency:

```toml
[dependencies]
fast-ssz = { path = "../fast-ssz/crates/fast-ssz" }
```

The path must point to this checkout's `crates/fast-ssz` directory.

## Reproduce the checks

Prerequisites: Linux x86_64 for the tested extraction tools, Git, Python 3.11+,
Rustup/Cargo, Elan/Lean, and network access for the pinned dependencies.
The Rust and Lean toolchains are pinned in `rust-toolchain.toml` and
`verification/lean-toolchain`. A first setup downloads substantial proof dependencies.

```sh
cargo test --workspace
cargo install cargo-hax --version 0.4.0 --locked
python3 scripts/verify.py bootstrap
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py check
```

`check` reruns Rust tests, formatting and Clippy, discovers public codec functions
through rustdoc, regenerates Lean from Rust, rejects extraction drift, checks the
audited import closure, builds the proofs, checks dependency revisions/cleanliness,
and checks that each registered theorem mentions its extracted function. Negative
fixtures verify that custom/native-evaluation axioms and unrelated proofs are rejected.

After an intentional Rust edit, run `python3 scripts/verify.py extract`, inspect the
generated diff, update the proofs, then rerun `check`. Never edit
`verification/FastSszRust.lean` manually. A successful check covers only the six
implemented functions, not the outstanding SSZ features above.

## License

MIT. See [third-party notices](THIRD_PARTY_NOTICES.md) for the upstream specification.
