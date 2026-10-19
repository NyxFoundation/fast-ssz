# nyx-ssz

Rust SSZ: Aeneas/Lean proofs before optimization.
**Verified baseline, not a complete SSZ library or production release.**
Crate publishing is disabled; no performance superiority is claimed.

Boolean, all six unsigned integer widths, Bitvector/Bitlist/ProgressiveBitlist and
borrowed ByteVector/ByteList/ProgressiveByteList codecs are implemented and proved,
including malformed inputs and illegal zero-length vector declarations.
ProgressiveBitlist decoding returns a validated zero-copy `BitListView`, exposing
its canonical SSZ bytes and a widened bit count without Boolean expansion.
All seven basic types also have proved `hash_tree_root` operations.
SHA-256 Merkle-parent hashing is also implemented and proved for every pair of
32-byte nodes. Generic node Merkleization supports optional capacities and zero padding
without allocating a padded tree. Single-branch root reconstruction and verification are implemented
and proved across the full `u128` index domain, including malformed requests.
RustCrypto `sha2` is a test oracle only, not a runtime dependency.
`U256` uses pinned `ruint` 1.20.1; its reachable getters/constructor are extracted
and proved, not assumed correct. Other `ruint` operations are outside these proofs.
See [verification scope and trust](docs/verification.md).

Owned `collections::Vector<T, N>` and `collections::List<T, MAX>` now enforce
exact/nonzero vector lengths and list capacities. Constructors and immutable projections
are proved for arbitrary element types; rejected inputs return their original storage.
This is a storage contract, not a generic element-codec or wire-layout proof.

The `codec::Ssz` trait provides a uniform interface for Boolean and all six unsigned
widths. Its seven library implementations have proved size metadata, basic/composite
classification, encoding, decoding and roots. External implementations are not
implicitly certified; generic dispatcher proofs require an explicit `CodecLaw`.
The shared numeric offset-span validator is also proved, including empty bodies,
ordering/scope errors and machine-maximum values. This is not a complete offset-table parser.

Generic collection codecs, collection trait implementations, containers, remaining Progressive types,
CompatibleUnion, derive, composite hash-tree roots, index/path APIs, multiproofs, official vectors
and benchmarks remain unfinished. The agreed release condition is not met.

## Example

```rust
use nyx_ssz::scalar::{decode_bool, encode_bool};
assert_eq!(encode_bool(true), [1]);
assert_eq!(decode_bool(&[1]), Ok(true));
assert!(decode_bool(&[2]).is_err());
let parent = nyx_ssz::sha256::hash_pair(&[0; 32], &[0; 32]);
assert_eq!(parent[0], 0xf5);
assert_eq!(
    nyx_ssz::merkle::verify_merkle_proof(&[0; 32], &[[0; 32]], 2, &parent),
    Ok(true),
);
```

Add this Git dependency to Cargo's `[dependencies]` (the crate is not published):

```toml
nyx-ssz = { git = "https://github.com/NyxFoundation/nyx-ssz" }
```

## Typed codecs

```rust
use nyx_ssz::codec::{decode, encode, hash_tree_root, Ssz};
let value = 0x1234u16;
let bytes = encode(&value).unwrap();
assert_eq!(bytes, [0x34, 0x12]);
assert_eq!(decode::<u16>(&bytes), Ok(value));
assert_eq!(u16::FIXED_SIZE, Ok(Some(2)));
let root = hash_tree_root(&value).unwrap();
assert_eq!(&root[..2], bytes.as_slice());
```

`FIXED_SIZE` distinguishes fixed widths, variable layouts (`Ok(None)`) and an
unrepresentable width (`Err(SizeOverflow)`). `IS_BASIC` controls packing before
collection Merkleization. `CodecError` implements the standard error interfaces.
Only the seven basic-type implementations are currently included; storage collections
below do not implement `Ssz` yet. Borrowed byte/bit codecs remain separate APIs.

## Typed storage

```rust
use nyx_ssz::collections::{list, vector, List, Vector};
let pair: Vector<u64, 2> = vector(vec![10, 20]).unwrap();
let values: List<_, 4> = list(vec![pair]).unwrap();
assert_eq!(values.as_slice()[0].as_slice(), &[10, 20]);
let rejected = list::<_, 0>(vec![7u8]).unwrap_err();
assert_eq!(rejected.values, vec![7]);
```

Fields are private and projections are immutable, so safe callers cannot resize the
collections. Arbitrary nested/non-`Copy` elements are supported, but collection
`Ssz` implementations and generic collection serializers are not provided yet. Allocation identity and absence of
element drops inside constructors are checked by Rust tests, not runtime-cost theorems.

## Reproduce

Requires Linux x86_64, Git, Python 3.11+, Rustup/Cargo, Elan and network access.
The pinned Rust toolchain includes Miri and rust-src. Extraction requires their prepared
standard-library MIR and fails if it is unavailable; generated function bodies are not rewritten.
Proof dependencies are large.

```sh
git clone https://github.com/NyxFoundation/nyx-ssz.git
cd nyx-ssz
cargo test --workspace
cargo install cargo-hax --version 0.4.0 --locked
python3 scripts/verify.py bootstrap
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py check
```

After Rust edits, run `python3 scripts/verify.py extract`, review the generated diff,
update proofs, then rerun `check`. Never hand-edit `verification/NyxSszRust.lean`
or the generated `verification/NyxSszRust/` modules.
Success covers the implemented slice only.

MIT; see [third-party notices](THIRD_PARTY_NOTICES.md).
