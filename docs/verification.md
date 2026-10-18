---
title: Verification scope and trust boundary
last_updated: 2026-10-22
tags:
  - ssz
  - aeneas
  - formal-verification
---
# Verification scope and trust boundary

## Status: initial slice, not release complete

The agreed first-release condition is full correspondence for all types in the
pinned ethereum/ssz-specs specification, including malformed inputs and SHA-256.
This checkout does **not** meet that condition. It intentionally exposes only the
small implemented, proved codec slice. No unsigned-integer, hash, proof, derive,
or composite implementation is hidden behind an unproved external contract.

| Implemented API | Reference operation | Lean theorem |
| --- | --- | --- |
| `scalar::encode_bool` | `Ssz.serialize .bool` | `encode_bool_refines` |
| `scalar::decode_bool` | `Ssz.deserialize .bool` | `decode_bool_refines` |
| `bytes::encode_byte_vector` / `decode_byte_vector` | Checked ByteVector serialization/deserialization | `byte_vector_refines` |
| `bytes::encode_byte_list` / `decode_byte_list` | Checked ByteList serialization/deserialization | `byte_list_refines` |

All theorem names above belong to `FastSszVerification`. Their implementation
arguments are functions from the generated `FastSszRust` namespace, not
handwritten replacements for the Rust code.

## Representation and error relations

`byteToSpec` preserves all eight bits. `bytesToSpec` preserves the order and
length of the entire input, converting Aeneas lists of bytes into the upstream
array representation.

The Boolean decoder theorem is quantified over **every** Aeneas byte slice.
Its outer result is `RustM.ok`, including malformed input, so it cannot panic
or diverge in that model. Its inner Rust result agrees with the upstream result:
scope errors become `InvalidLength`; a non-bit Boolean becomes `InvalidBoolean`.
The Boolean reference cannot return another successful value shape.

The byte-array theorems quantify over every slice and every machine-sized
length/limit. They prove both encoding and decoding, including the exact returned
bytes, rather than merely round trips or matching acceptance flags.
They call upstream `Desc.wellFormed` before the codec: a zero-length ByteVector
is an illegal declaration, not an empty valid value. ByteList with limit zero
is valid and accepts only empty input.

The byte-array fault relation accepts only these corresponding errors:

| Rust | Upstream |
| --- | --- |
| `EmptyVector` | `vectorEmpty` |
| `InvalidLength` | `scope` |
| `OverLimit` | `overLimit` |

All other success/failure combinations make the relation false. Both byte-array
operations return the original borrowed slice. Content correspondence is proved;
zero allocation/copying is evident from the Rust source and checked by pointer
identity tests, not claimed as a formal performance theorem.

## Reproducibility and change detection

`sources.lock` pins the specification, Charon, Aeneas, Rust, and Lean.
`verification/lake-manifest.json` pins all transitive Lean dependencies.
The Aeneas version used here is the **Cryspen fork**, not an assertion that the
same commit exists in the AeneasVerif repository.

The reference pins Lean 4.33.1 upstream; the selected Aeneas release uses
Lean 4.31.0. This project builds the pinned, **unchanged reference source**
with Lean 4.31.0. It does not edit the specification to make a proof pass.
Do not run an unqualified `lake update`: it will select the newer upstream
toolchain. Dependency updates are deliberate maintenance, not part of verification.

The reproducible commands are in the root README. The check:

1. Discovers public free functions with rustdoc JSON and requires exact agreement
   with `verification/targets.json`. Public traits and associated functions are
   rejected until their coverage logic is implemented. Error formatting and
   derived standard traits are not protocol operations and are not extracted or proved.
2. Extracts the selected Rust call graphs with Charon's Aeneas preset, then Aeneas.
3. Requires byte-for-byte equality with checked-in generated Lean.
4. Requires every project Lean source to be in the audit's import closure.
5. Builds proofs and audits transitive axiom dependencies of all generated and
   handwritten declarations, including private ones.
6. Checks every pinned dependency's Git revision and clean working tree.
7. Requires each registered proof to be an actual Lean theorem whose statement
   mentions the associated extracted function.
8. Compiles negative fixtures to ensure the audit rejects custom axioms and
   native-evaluation axioms, and that unrelated theorems cannot satisfy coverage.

The Rust tests currently cover 100% of codec lines and functions, measured with
`cargo llvm-cov --workspace --fail-under-lines 80` (cargo-llvm-cov 0.8.7).
The README example is also run as a Rust doctest. CI is configured but has not
been run on GitHub because this checkout has no origin repository.

The theorem-registration check is a coverage guard, not a theorem about arbitrary future theorem
statements. Reviewing the adequacy of a new refinement statement remains necessary.
There are no opaque external operations in the six extracted codec call graphs
other than Aeneas's standard models for machine integers, slices, and indexing.

## Trust boundary and limits

Allowed logical axioms: `propext`, `Classical.choice`, and `Quot.sound`.
The audit rejects `sorryAx`, custom axioms, and native-evaluation proof axioms.
The existing proofs use neither `sorry` nor external SHA-256 assumptions.

The claims depend on Lean's kernel and logical foundations, the correctness of
Charon/Aeneas translation and standard-library models, and the Rust compiler,
borrow checker, compiler backend, and execution environment. Compiler correctness
is not established by this repository. Downloaded tool binaries and proof caches
are supply-chain dependencies; version pinning is not a proof of their integrity.
The correspondence between the upstream formal definitions and English SSZ
requirements remains an upstream review obligation.

The domain of Rust lengths is `usize`, not all mathematical natural numbers.
The currently tested extraction host is Linux x86_64. Native aarch64 execution
has not been verified in this checkout. These codecs contain no recursion or heap
allocation, but OS/hardware faults and arbitrary process resource exhaustion are
not covered by the functional semantics. No whole-library or cryptographic
security claim follows from this slice.

## Remaining first-release obligations

All unsigned-integer widths, bitfields, generic Vector/List, Container,
Progressive collections/containers, CompatibleUnion, and the typed derive API
remain to be implemented and proved. The same applies to SHA-256, hash-tree
roots, generalized indices, single proofs, and multiproofs, including malformed
requests. The pinned upstream model excludes legacy positional unions.

Official test-vector replay must then cover every supported vector category,
with an enforced expected case count. The current Rust regression tests are not
advertised as official conformance tests. Hardware/compiler-controlled
cross-library benchmarks and proof-preserving performance optimization follow
the completed first-release correspondence proofs, not this initial slice.
