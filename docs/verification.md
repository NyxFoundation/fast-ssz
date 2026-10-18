---
title: Verification scope and trust boundary
last_updated: 2026-10-22
tags:
  - ssz
  - aeneas
  - formal-verification
---
# Verification scope and trust boundary

**Not release complete:** Boolean/ByteVector/ByteList codecs and SHA-256 node
combination are implemented. `verification/targets.json` links seven operations
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

Checks cover Rust tests/doctests/lints, extraction/API/import coverage, proofs and
pinned source integrity. Generated declarations are partitioned into dependency-ordered
modules with their text and qualified names preserved; the complete module inventory
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
