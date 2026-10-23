---
title: Native SSZ API
last_updated: 2026-10-23
tags:
  - ssz
  - rust
  - api
---
# Native SSZ API

Native completion and formal equivalence are separate. All 13 shapes in the pinned
specification have value codecs. Current-source proof status is tracked separately;
neither implementing nor deriving `Ssz` certifies a codec.

## Derive

```rust
use nyx_ssz::{codec::Ssz, collections::List, path::Step};

#[derive(nyx_ssz::Ssz)]
struct Message {
    slot: u64,
    votes: List<u16, 16>,
}
let value = Message {
    slot: 42,
    votes: nyx_ssz::collections::list(vec![1, 2]).unwrap(),
};
let bytes = value.encode().unwrap();
let decoded = Message::decode(&bytes).unwrap();
assert_eq!(decoded.encode().unwrap(), bytes);
let branch = nyx_ssz::proof::at_path(&value, &[Step::Field("votes"), Step::Length]).unwrap();
assert!(nyx_ssz::merkle::verify_merkle_proof(
    &branch.leaf, &branch.siblings, branch.index, &value.hash_tree_root().unwrap()
).unwrap());
```

Named structs are ordinary Containers. Generic field types acquire codec bounds.
Tuple/unit/empty structs are rejected. Width and packing metadata come from child declarations.

Add `#[ssz(progressive)]` to a named struct and require `#[ssz(position = N)]`
on each field, in 0..=255. Fields encode, decode and root in position order, not
Rust declaration order. Gaps become zero Merkle leaves; the packed active mask is mixed in.

Enums are CompatibleUnions. Each variant requires one unnamed payload and an explicit,
distinct `#[ssz(selector = N)]` in 1..=127. All options must have compatible declarations;
validation precedes wire/value processing. The encoded selector is followed by the selected
payload, and its root is mixed with the selector word. Empty/unknown wire selectors
return `NoSelector`/`UnknownSelector`.

Fields default to their Rust name (raw-identifier prefixes are removed).
`#[ssz(rename = "任意の名前")]` supplies an exact UTF-8 name; duplicate final names are rejected.
Renaming affects schema/path lookup, not bytes or roots.

## Direct encoding

`Ssz::encoded_len() -> Result<usize, CodecError>` performs complete value validation
and returns the exact encoded length without building encoded bytes.
`Ssz::encode_into(&mut [u8]) -> Result<(), CodecError>` writes into an exactly sized slice.
The library implementations need no encoded-child scratch buffers.
The existing `encode()` is now a default method: calculate length, allocate one
zero-initialized output Vec, then write directly into it.

```rust
use nyx_ssz::codec::Ssz;
let value = 0x1234_u16;
let mut output = vec![0; value.encoded_len().unwrap()];
value.encode_into(&mut output).unwrap();
assert_eq!(output, [0x34, 0x12]);
```

For valid values, an incorrectly sized destination returns `InvalidLength` before
any write. Other failures may leave partial output; discard it on error. Only the
supplied slice is writable, so a subslice's surrounding bytes remain untouched.
No rollback copy is made. Reusing a buffer is a separate operation from allocating
`encode()` and must be benchmarked separately.

Manual implementors must replace their old allocating `encode` implementation with
the two required methods. They must agree on validation, length and bytes, preserve
protocol-fault precedence, and never implement either by calling the default `encode()`.
For a simple wrapper, delegate both methods to the wrapped codec:

```rust
use nyx_ssz::{codec::Ssz, error::{CodecError, DecodeFailure}, type_info::TypeDescriptor};
struct Counter(u64);
impl Ssz for Counter {
    type DecodeState = ();
    const TYPE: &'static TypeDescriptor = &TypeDescriptor::Uint(8);
    fn encoded_len(&self) -> Result<usize, CodecError> { self.0.encoded_len() }
    fn encode_into(&self, out: &mut [u8]) -> Result<(), CodecError> { self.0.encode_into(out) }
    fn decode(input: &[u8]) -> Result<Self, DecodeFailure<()>> { u64::decode(input).map(Self) }
    fn hash_tree_root(&self) -> Result<[u8; 32], CodecError> { self.0.hash_tree_root() }
}
assert_eq!(Counter(42).encode().unwrap(), 42_u64.to_le_bytes());
```

Length calculation must still inspect later children after an earlier
`NativeOutputOverflow`, so their protocol errors win over deferred parent
assembly refusal. Sequence/Container output retains the strict four-byte budget;
do not impose that budget on top-level opaque bytes or union prefixes.
`NativeOutputOverflow` remains distinct from protocol `SizeOverflow`.

The new member laws and default-method bridge are **not formally proved**.
The historical `CodecLaw` does not cover these methods; the full proof gate rejects
that incomplete contract until [#29](https://github.com/NyxFoundation/nyx-ssz/issues/29)
is resolved. The 12 hash-independent current-source proofs remain checked.

## Failure ownership

A derived struct's `DecodeState` has one `FieldDecodeState<T>` per Rust field:
`value: Option<T>` retains a completed field, and `child: Option<T::DecodeState>`
retains the refusing child's state. Later fields remain empty. Layout/type refusals
contain no decoded fields. No completed or nested owner is destroyed inside a refusal.

A union returns `None` for declaration/layout refusal, or `Some(state)` with the
matching variant containing the selected child's state. State types are exposed through
`<T as Ssz>::DecodeState`, not by a generated global name. Callers control when to
inspect, move or drop returned state.

## Paths, nodes and proofs

`path::resolve::<T>(&steps)` resolves `Position`, `Field`, `Length`,
`ActiveFields` and `Selector` to a checked `u128` generalized index.
Positions are schema ordinals for Container fields, logical element/bit indices for
collections, and explicit selectors for unions. Progressive bounds do not restrict
type-level positions, matching the pinned specification.
`Location` includes packed byte ranges or a bit offset. Reserved words terminate a path.

`node::get(&value, index)` reads the root (one) or an existing descendant.
`node::at_path` resolves then reads. Packed elements share their enclosing node.
Bounded padding is addressable without allocating it. A path is type-level: it does
not establish that a list currently contains that element or a union selects that option.
Absent progressive-spine descendants can be unaddressable; requesting one returns an error.

`proof::create`/`at_path` build bottom-up single branches.
`proof::create_multi` preserves claim order and emits canonical descending helpers.
Zero/root, duplicate and nested claims retain the existing verifier's refusal rules.
Use `merkle::verify_merkle_proof` or `multiproof::verify_merkle_proof` to verify.

Tree access currently materializes the occupied tree from canonical encoded bytes.
It is not a persistent/lazy tree, and proof construction is not sublinear.
All padding is sparse. Index overflow is an error, never truncation.

## Scope

All 4,601 immutable official corpus cases are checked, including every Container and
ProgressiveContainer fixture. The pinned corpus has no CompatibleUnion family; independent
tests cover selectors, compatibility, roots, malformed bytes, generics and failure ownership.
Allocator exhaustion, cyclic external static declarations, arbitrary external trait
implementations and a production security audit are outside the correctness claim.
