---
title: Verification scope and trust boundary
last_updated: 2026-10-19
tags:
  - ssz
  - aeneas
  - formal-verification
---
# Verification scope and trust boundary

**Not release complete:** Boolean, uint8/16/32/64/128/256, Bitvector/Bitlist/ProgressiveBitlist and borrowed
ByteVector/ByteList/ProgressiveByteList codecs, SHA-256 node combination and
single-branch Merkle verification, generic node Merkleization and all basic-type
roots are implemented.
`verification/targets.json` links thirty-nine operations
to proofs over actual Aeneas output.
Every slice/bound yields `RustM.ok`; success contains exact reference bytes/values.
Conversion preserves bits, order and length. Byte codecs validate `Desc.wellFormed`.
Their relation permits only EmptyVector/vectorEmpty, InvalidLength/scope and
OverLimit/overLimit; other outcomes are false. Boolean errors classify scope/non-bit
faults. Bounds cover `usize`, not all naturals. Zero-copy is source/test evidence,
not a cost theorem. Derived error traits are not protocol proof targets.

ProgressiveByteList is checked against `.progressiveList (.uint 1) limit`, not
an opaque-byte descriptor. Its injective value view maps every byte to a uint8,
preserving order and length. The sequence layout and singleton-byte slicing are
proved to encode/decode exactly the borrowed input. `None` imposes no declared
capacity; optional capacities cover every `usize`. Both forms enforce the pinned
reference's sequence size of less than 2^32 bytes. Above that size, serialization
checks capacity first and deserialization checks offset width first; both error
precedences are proved, including inputs too large to allocate in unit tests.

Unsigned native codecs reuse Rust's standard little-endian and checked slice/array
conversions. Their actual models are proved against `Ssz.serialize`/`Ssz.deserialize`
for every value and input slice. Generic bitvector/byte lemmas establish both
encoding order and decoding value; only incorrect lengths are refused.
`U256` is `ruint::Uint<256, 4>` pinned to 1.20.1. Its value view concatenates all
four least-significant-first limbs, preserving all 256 bits. The reached library
getters, constructor, mask/count checks and Rust's `usize::div_ceil` are extracted
as real definitions and their required calls are proved. Ruint's unsafe byte casts
and arithmetic APIs are neither used nor covered. No library-correctness axiom is added.

Bitvector codecs cover every `usize` declaration and typed input, including
zero-length declarations, wrong lengths and noncanonical high padding. Their
actual Vec loops are proved terminating with decreasing natural measures; byte
counts, indices, shifts and increments are proved safe. The value view preserves
Boolean order exactly. Bitlist proofs cover delimiter insertion, empty values,
byte-boundary crossings, every final-byte pattern, capacity violations and the
separate empty-encoding/no-delimiter/trailing-zero error classes. Decoder byte-to-bit
arithmetic is guarded before multiplication/addition; both guards are proved equivalent
to the reference's natural-number count check. The all-zero scan has a decreasing
measure and prefix invariant. Vec allocation uses Aeneas's model; OS/resource failures
remain outside the guarantee.

ProgressiveBitlist accepts optional capacities, including no capacity, without
imposing a new format limit. The borrowed `BitListView` stores only validated,
immutable encoded bytes. Its value view is the reference's packed-bit decoding,
not a projection discarding bit contents. Returned views are proved nonempty and
canonical; their length getter's nonempty precondition is discharged by the decoder
and preserved by private fields and borrowing. The exact storage getter is also
audited. Bit counts use `u128` as an implementation choice to represent up to eight
times a `usize` byte count, not as an SSZ requirement. Widening, arithmetic safety,
all error classes and both bounded/unbounded codecs are proved.

Basic `hash_tree_root` operations cover Boolean and all six unsigned widths, for
every typed value. They refine the unchanged `Ssz.hashTreeRoot`, through its actual
layout, packing, bounded merkleization and depth-zero tree rules. The extracted
array-prefix mutation and standard `copy_from_slice` call are proved safe and
preserve every encoded byte, with zero padding to 32 bytes. A uint256 fills the
node exactly. Basic roots do not SHA-256 hash their single leaf; composite roots
remain unfinished.

`hash_pair_refines` proves termination and exact equality with upstream `Ssz.combine`
for every 512-bit input. This covers SSZ's 32-byte-child/32-byte-child hashing path,
not a general-purpose arbitrary-message SHA-256 API. Schedule, all 64 rounds,
both compression blocks, padding and output encoding are connected to the unchanged
upstream SHA-256 implementation. No external hash-function correctness is assumed.
RustCrypto `sha2` 0.10.9 is used only for differential tests.

`merkleize_refines` covers all complete-node slices and every optional `usize`
capacity against `Ssz.merkleizeBounded`. Empty trees, zero capacity, undersized
capacity errors and rounding up `usize::MAX` are covered. Depth uses overflow-free
halving rather than materializing the next power of two. Recursive calls decrease
the count or depth; every shift and slice boundary is proved safe. Zero subtrees
are computed without allocating padding and proved equal to the reference's cache.
These are correctness/termination guarantees, not allocation or runtime cost theorems.

`calculate_merkle_root_refines` and `verify_merkle_proof_refines` connect the actual
Rust APIs to `Ssz.calculateMerkleRoot` and `Ssz.verifyMerkleProof`. All `u128`
indices and representable branch slices are covered. Node widths are enforced by
`[u8; 32]`; their reference width checks are proved successful. Zero, the root
index and incorrect branch lengths return the corresponding error category;
a well-formed nonmatching proof returns false. Proofs cover index guards, sibling
order, recursive termination, SHA-256 composition and bytewise root comparison.
Error relations classify reasons, not the reference error's numeric diagnostics.
Generic collections, paths, multiproofs and full-library conformance are not yet proved.

Checks cover Rust tests/doctests/lints, extraction/API/import coverage, proofs and
pinned source integrity. Generated declarations are partitioned into dependency-ordered
modules with qualified names and declaration bodies preserved. Dependency-aware
canonical ordering and inter-declaration whitespace avoid unrelated extraction
order changes invalidating cached proofs. Registry source-location comments use
portable package-relative paths; executable declaration bodies are unchanged.
Extraction requires the pinned Rust toolchain's Miri and rust-src components. It prepares
the standard-library MIR with `cargo +nightly-2026-08-18 miri setup --print-sysroot`
and passes that sysroot explicitly to Charon. Preparation failures stop extraction;
there is no default-sysroot fallback and no executable-body rewriting. Each extraction
uses a fresh Cargo target directory to avoid reusing artifacts from a different sysroot.
Procedural macros discovered in locked Cargo metadata are first compiled with the normal
host sysroot: they execute during compilation and cannot link against Miri's runtime.
Charon then compiles the library dependencies and implementation against the explicit MIR sysroot.
The former Python `usize::div_ceil` body replacement was not machine-checked and has
been removed; its byte-equality check did not establish equivalence to the original output.
`sources.lock` explicitly names transparent foreign items; opaque foreign axioms
are refused rather than treated as library contracts. The complete module inventory
is checked against fresh extraction. Public inherent methods are discovered from
Rustdoc's implementation/type paths, and unknown or ambiguous paths are refused.
Pinned Charon cannot start at inherent methods: they must be reached through registered
call graphs, and every registered operation must have a concrete extracted definition.
Opaque declarations cannot satisfy that check. Public traits still fail pending
coverage support. Statement adequacy requires review. Negative fixtures reject custom/native axioms
and unrelated proofs. Only propext, Classical.choice and Quot.sound are allowed.

Pinned Cryspen Aeneas uses Lean 4.31.0; upstream SSZ pins 4.33.1.
The unchanged executable modules and imported codec lemmas build with 4.31.0 here.
Not all upstream proof modules do (`Codec.Admits` exceeds its recursion limit;
`Proofs.Merkle.Tree` has incompatible monadic simplification). Needed tree cache
and evaluation laws are re-proved locally over the unchanged executable definitions.
Unqualified `lake update` changes the toolchain.
Trust includes Lean's kernel, Charon/Aeneas/models, Rust's compiler/runtime and
downloaded tools/caches. Pins do not prove binary integrity; English/formal-model
alignment remains upstream.
OS faults/resource exhaustion and whole-library/cryptographic security are excluded.
x86_64 extraction requires the prepared Miri sysroot. Native aarch64 extraction has not been exercised.
