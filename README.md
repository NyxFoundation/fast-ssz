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
The `gindex` module also provides proved raw tree arithmetic, depth/branch lengths,
path concatenation/rebasing and bottom-up path/sibling indices over the full `u128`
domain. Unrepresentable natural-number results return `ProofError::IndexOverflow`;
bit queries and truncation explicitly handle positions beyond the word width.
These numeric helpers do not yet resolve typed field/element paths.
RustCrypto `sha2` is a test oracle only, not a runtime dependency.
`U256` uses pinned `ruint` 1.20.1; its reachable getters/constructor are extracted
and proved, not assumed correct. Other `ruint` operations are outside these proofs.
See [verification scope and trust](docs/verification.md).

Owned `collections::Vector<T, N>` and `collections::List<T, MAX>` now enforce
exact/nonzero vector lengths and list capacities. Constructors and immutable projections
are proved for arbitrary element types; rejected inputs return their original storage.
Their `Ssz` implementations additionally compose encoding, decoding and roots with
any explicitly lawful child codec, including nested fixed- and variable-width collections.

The `codec::Ssz` trait provides a uniform interface for Boolean, all six unsigned
widths, generic Vector and List. Its nine library implementations have proved declaration
metadata, encoding, decoding and roots. External implementations are not
implicitly certified; generic dispatcher proofs require an explicit `CodecLaw`.
Decoding returns `DecodeFailure<T::DecodeState>` on error, retaining ownership of
partial values. Basic codecs use `DecodeState = ()`; encode/root errors remain `CodecError`.
The shared offset-span validator and fixed- or inferred-count layout parsers for
both fixed- and variable-width elements are also proved. The parser returns an immutable zero-copy `SequenceView`, with checked
headers, four-byte size envelope and body ranges. It does not decode element values.
`codec::decode_elements` decodes those bodies in order. Its proof covers exact successful
values, fault classes, and retention of both the completed prefix and nested failure state.

Containers, remaining Progressive value codecs, CompatibleUnion, derive, borrowed byte/bit
roots, typed index/path APIs, multiproofs, the complete official corpus and benchmarks
remain unfinished. The agreed release condition is not met.

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
use nyx_ssz::codec::{decode, encode, fixed_size, hash_tree_root, is_compatible, validate_type};
let value = 0x1234u16;
let bytes = encode(&value).unwrap();
assert_eq!(bytes, [0x34, 0x12]);
assert_eq!(decode::<u16>(&bytes), Ok(value));
assert_eq!(fixed_size::<u16>(), Ok(Some(2)));
assert_eq!(validate_type::<u16>(), Ok(()));
assert!(!is_compatible::<bool, u8>());
let root = hash_tree_root(&value).unwrap();
assert_eq!(&root[..2], bytes.as_slice());
```

`Ssz::TYPE` is an immutable static declaration. `codec::fixed_size` derives fixed
widths, variable layouts (`Ok(None)`) or unrepresentable widths (`Err(SizeOverflow)`).
`codec::is_basic` derives packing classification; `codec::validate_type` checks the
declaration without invoking a value codec. `codec::is_compatible` compares declared
Merkle layouts but does not imply type validity. These are not independently overridable
metadata constants. The descriptor covers Boolean, unsigned integers, and recursively
nested Vector/List/ProgressiveList declarations. Vector widths use checked multiplication;
an outer zero count cancels even an unrepresentable fixed child width, whereas a variable
child stays variable. ProgressiveList declaration support is not yet a value codec.
`CodecError` implements the standard error interfaces. The seven basic implementations
and generic Vector/List implementations are certified; borrowed byte/bit codecs remain separate APIs.

```rust
use nyx_ssz::{codec::decode, error::CodecError};
let failure = decode::<u16>(&[0]).unwrap_err();
assert_eq!(failure.kind, CodecError::InvalidLength);
assert_eq!(failure.state, ());
```

External implementations declare their own `DecodeState`. Error state is returned
unchanged by the dispatcher; callers decide when to inspect or drop it. Formatting
reports only the error kind and does not require or reveal the state. There is no
legacy state-discarding decoder wrapper.

## Borrowed sequence layout

```rust
use nyx_ssz::sequence::variable_vector_view;
let bytes = [8, 0, 0, 0, 10, 0, 0, 0, 42, 43, 44];
let view = variable_vector_view(&bytes, 2).unwrap();
assert_eq!(view.len(), 2);
assert_eq!(view.get(0), Some(&bytes[8..10]));
assert_eq!(view.get(2), None);
```

This is an internal-layout API, not a complete typed Vector codec. Its caller
validates the type declaration; count zero follows the reference's internal slicing
rule. No element's value or declared limit is checked by this layout-only API.
`nyx_ssz::sequence::variable_list_view(&bytes, Some(capacity))` infers the count from
the first offset and checks that element-count capacity; `None` imposes no declared capacity.
It validates layout only, not each element's own bounds or containing type declaration.

For fixed-width bodies, use `fixed_vector_view(&bytes, width, count)` or
`fixed_list_view(&bytes, width, optional_capacity)`. Both enforce the same composite
size envelope. Vectors require the exact byte budget, including checked multiplication;
lists infer their count and reject widthless nonempty input or incomplete elements
before checking capacity. An empty fixed list has zero elements, even at zero width.
These are layout helpers, not complete typed collection codecs.

## Typed element decoding

Decode already-sliced bodies, retaining ownership on the first element failure:

```rust
use nyx_ssz::{codec::decode_elements, error::CodecError, sequence::fixed_vector_view};
let view = fixed_vector_view(&[0, 2], 1, 2).unwrap();
let failure = decode_elements::<bool>(&view).unwrap_err();
assert_eq!(failure.kind, CodecError::InvalidBoolean);
assert_eq!(failure.state.values, [false]);
assert_eq!(failure.state.child, Some(()));
```

This lower-level helper does not choose or validate a containing sequence's type declaration;
the caller selects its layout before decoding elements. An empty view invokes no element decoder.
`SequenceDecodeState` returns every completed element and the failing child's exact state.
The input/view remains borrowed and reusable; no element bytes are copied by the traversal.
Typed Vector/List decoding selects and validates the containing layout before reusing this
traversal; separate parent theorems preserve its exact typed prefix and child state.

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
collections. Arbitrary nested/non-`Copy` elements are supported. When `T: Ssz`, both collections
also implement `Ssz`; their formal codec guarantees require the actual child's `CodecLaw`.
Serialization writes fixed values inline or checks and writes four-byte offset tables. Roots pack
basic children or Merkleize composite child roots; lists mix in the actual element count.
Decode failures return completed values and nested child state without dropping them inside the operation.
Allocation identity and absence of element drops are also checked by Rust tests, not runtime-cost theorems.

```rust
use nyx_ssz::{codec::{decode, encode, hash_tree_root}, collections::{list, vector, List, Vector}};
let value = vector::<_, 2>(vec![list::<_, 4>(vec![1u8, 2]).unwrap(), list(vec![3]).unwrap()]).unwrap();
let bytes = encode(&value).unwrap();
let decoded = decode::<Vector<List<u8, 4>, 2>>(&bytes).unwrap();
assert_eq!(decoded.as_slice()[0].as_slice(), &[1, 2]);
assert_eq!(hash_tree_root(&decoded), hash_tree_root(&value));
```

## Official test vectors

The immutable `ethereum/consensus-spec-tests` commit in `sources.lock` is fetched into
an external cache, not vendored. Cache checks verify Git provenance, the complete file
inventory's independently pinned SHA-256 and each fixture's actual Git blob hash, rather than
trusting cached Git object storage or status alone.

```sh
python3 scripts/official_vectors.py check --family boolean --family uints --family basic_vector
```

This checks all 1,229 selected cases: exact YAML values, encoded bytes, roots and invalid-input
rejection. It is a three-family slice, not full conformance; six other families remain.
Omitting `--family` requests the entire corpus; unsupported families fail instead of being ignored.
The Rust CI matrix runs this explicit slice on x86_64 and aarch64. See
[runner details](tools/official-vectors/README.md).

## Reproduce

Requires Linux x86_64, Git, Python 3.11+, Rustup/Cargo, Elan, Nix and network access.
Bootstrap builds Aeneas from the exact public source revision in `sources.lock`;
Charon remains pinned independently. The Nix output link retains the built extractor.
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
