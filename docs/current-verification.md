---
title: Current-source proof scope and explicit skips
last_updated: 2026-10-22
tags:
  - ssz
  - aeneas
  - formal-verification
---
# Current-source proof scope and explicit skips

Native completion and formal completion are different. The native implementation passes
all 4,601 pinned corpus cases. **Full-library equivalence is not proved.**

## Freshly proved slice

| Current production module | Public operations |
| --- | --- |
| SHA-256 parent hashing | 1 |
| Generalized-index arithmetic and paths | 11 |
| Bounded Merkleization and branch verification | 3 |
| Multiproof helper indices and verification | 3 |
| Total | 18 |

`verification/current_merkle.rs` includes the actual four production files by Rust path;
it does not copy, simplify or substitute their implementations. Root contents are checked.
Charon and Aeneas extract those files with the pinned compiler/MIR sysroot and tools.
Four checked-in generated modules must match fresh extraction byte for byte.
Existing equivalence theorems over these definitions are rechecked by Lean's kernel.
The audit binds every registered operation to its actual theorem and rejects foreign axioms,
native-decision axioms and unrelated theorem registrations. Allowed foundational axioms remain
`propext`, `Classical.choice` and `Quot.sound`, as in the existing audit.

## Explicitly unproved

`verification/current-scope.json` enumerates all **97 remaining documented APIs**
and **17 codec dictionaries**, plus the derive-transformation backlog.
Every documented API must be exactly in the proved or skipped set; additions, stale
registrations, overlaps or missing dictionary status fail the gate.
Hidden generated-code helpers are included in the unproved derive obligations.

- [#24: metadata extraction](https://github.com/NyxFoundation/nyx-ssz/issues/24):
  `current_metadata.rs` includes the real 13-shape metadata implementation.
  Charon produces LLBC; Aeneas reports **Returns inside of nested loops are not supported yet**
  in `union_options_agree`. The skip accepts only the recorded tool revisions, source hash,
  error status and diagnostic. Any unexpected failure remains a failure; success invalidates
  the skip and requires proving the laws.
- [#25: remaining equivalence laws](https://github.com/NyxFoundation/nyx-ssz/issues/25):
  includes whole-Cargo/MIR host-tool integration, metadata/codec laws, heterogeneous ownership,
  generated declarations/reordering/conversions, typed paths, node access and proof construction.
  These are integration-blocked obligations, **not** a claim that each operation is
  individually impossible to prove.

No Aeneas modification, new axiom, narrowed input domain or weakened fault relation is used.
Historical broader generated artifacts and registrations remain available but are not evidence
that the enlarged current program is proved. Unproved/skipped is never counted as proof success.

## Reproduce

Install the pinned Rust/Lean tools and cargo-hax described by `sources.lock`, then:

```sh
python3 scripts/verify.py bootstrap
python3 scripts/current_refinement.py check
```

The current check performs real extraction, freshness/API checks, the metadata refusal
probe, kernel checking, negative audit tests and dependency-pin validation.
`probe-metadata` runs the recorded blocker alone; `extract` regenerates only the four current
modules and does not establish proof success. `lake build` defaults to the current audit.

CI names this a **current Aeneas slice and explicit unproved status** check. Its green
status means that this bounded proof/status contract passed, not full-library equivalence.
The original `scripts/verify.py check` remains fail closed for the historical full registration
set; it is not advertised as passing against the enlarged library.
