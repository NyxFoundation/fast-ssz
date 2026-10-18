---
title: Verification scope and trust boundary
last_updated: 2026-10-19
tags:
  - ssz
  - aeneas
  - formal-verification
---
# Verification scope and trust boundary

**Not release complete:** Boolean/ByteVector/ByteList codecs, SHA-256 node
combination and single-branch Merkle verification are implemented.
`verification/targets.json` links nine operations
to proofs over actual Aeneas output.
Every slice/bound yields `RustM.ok`; success contains exact reference bytes/values.
Conversion preserves bits, order and length. Byte codecs validate `Desc.wellFormed`.
Their relation permits only EmptyVector/vectorEmpty, InvalidLength/scope and
OverLimit/overLimit; other outcomes are false. Boolean errors classify scope/non-bit
faults. Bounds cover `usize`, not all naturals. Zero-copy is source/test evidence,
not a cost theorem. Derived error traits are not protocol proof targets.

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
order changes invalidating cached proofs. The complete module inventory
is checked against fresh extraction. New traits/methods fail pending coverage support.
Statement adequacy requires review. Negative fixtures reject custom/native axioms
and unrelated proofs. Only propext, Classical.choice and Quot.sound are allowed.

Pinned Cryspen Aeneas uses Lean 4.31.0. Unchanged upstream SSZ (which pins 4.33.1)
builds with 4.31.0 here; unqualified `lake update` changes the toolchain.
Trust includes Lean's kernel, Charon/Aeneas/models, Rust's compiler/runtime and
downloaded tools/caches. Pins do not prove binary integrity; English/formal-model
alignment remains upstream.
OS faults/resource exhaustion and whole-library/cryptographic security are excluded.
x86_64 extraction passed; native aarch64 and GitHub CI have not been exercised.
