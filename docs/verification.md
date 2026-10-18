---
title: Verification scope and trust boundary
last_updated: 2026-10-22
tags:
  - ssz
  - aeneas
  - formal-verification
---
# Verification scope and trust boundary

**Not release complete:** only Boolean/ByteVector/ByteList codecs exist.
`verification/targets.json` links six functions to proofs over actual Aeneas output.
Every slice/bound yields `RustM.ok`; success contains exact reference bytes/values.
Conversion preserves bits, order and length. Byte codecs validate `Desc.wellFormed`.
Their relation permits only EmptyVector/vectorEmpty, InvalidLength/scope and
OverLimit/overLimit; other outcomes are false. Boolean errors classify scope/non-bit
faults. Bounds cover `usize`, not all naturals. Zero-copy is source/test evidence,
not a cost theorem. Derived error traits are not protocol proof targets.

Checks cover Rust tests/doctests/lints, extraction/API/import coverage, proofs and
pinned source integrity. New traits/methods fail pending coverage support.
Statement adequacy requires review. Negative fixtures reject custom/native axioms
and unrelated proofs. Only propext, Classical.choice and Quot.sound are allowed.

Pinned Cryspen Aeneas uses Lean 4.31.0. Unchanged upstream SSZ (which pins 4.33.1)
builds with 4.31.0 here; unqualified `lake update` changes the toolchain.
Trust includes Lean's kernel, Charon/Aeneas/models, Rust's compiler/runtime and
downloaded tools/caches. Pins do not prove binary integrity; English/formal-model
alignment remains upstream.
OS faults/resource exhaustion and whole-library/cryptographic security are excluded.
x86_64 extraction passed; native aarch64 and GitHub CI have not been exercised.
