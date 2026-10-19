---
title: Verification scope and trust boundary
last_updated: 2026-10-19
tags:
  - ssz
  - aeneas
  - formal-verification
---
# Verification scope and trust boundary

**Not release complete:** Boolean, uint8/16/32/64/128/256, Bitvector/Bitlist and borrowed
ByteVector/ByteList/ProgressiveByteList codecs, SHA-256 node combination and
single-branch Merkle verification are implemented.
`verification/targets.json` links twenty-seven operations
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

`hash_pair_refines` proves termination and exact equality with upstream `Ssz.combine`
for every 512-bit input. This covers SSZ's 32-byte-child/32-byte-child hashing path,
not a general-purpose arbitrary-message SHA-256 API. Schedule, all 64 rounds,
both compression blocks, padding and output encoding are connected to the unchanged
upstream SHA-256 implementation. No external hash-function correctness is assumed.
RustCrypto `sha2` 0.10.9 is used only for differential tests.

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
`sources.lock` explicitly names transparent foreign items; opaque foreign axioms
are refused rather than treated as library contracts. The complete module inventory
is checked against fresh extraction. New traits/methods fail pending coverage support.
Statement adequacy requires review. Negative fixtures reject custom/native axioms
and unrelated proofs. Only propext, Classical.choice and Quot.sound are allowed.

Pinned Cryspen Aeneas uses Lean 4.31.0; upstream SSZ pins 4.33.1.
The unchanged executable modules and imported codec lemmas build with 4.31.0 here.
Not all upstream proof modules do (`Codec.Admits` exceeds its recursion limit).
Unqualified `lake update` changes the toolchain.
Trust includes Lean's kernel, Charon/Aeneas/models, Rust's compiler/runtime and
downloaded tools/caches. Pins do not prove binary integrity; English/formal-model
alignment remains upstream.
OS faults/resource exhaustion and whole-library/cryptographic security are excluded.
x86_64 extraction passed; native aarch64 and GitHub CI have not been exercised.
