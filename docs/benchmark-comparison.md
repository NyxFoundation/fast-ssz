---
title: Three-library SSZ benchmark comparison
last_updated: 2026-10-23
tags:
  - ssz
  - benchmarks
  - performance
---
# Three-library SSZ benchmark comparison

This is the 2026-10-22 scalar-SHA baseline. For the current backend and a same-day
before/after recheck, see [RustCrypto migration](rustcrypto-migration.md).

Measured on this development machine, not copied from upstream READMEs.
**nyx-ssz is substantially slower on these fixtures.** This is a valid-input,
hot-cache, end-to-end API comparison, not a security or formal-equivalence result.

## Machine and versions

- AMD Ryzen 9 PRO 8945HS, Linux x86_64; all timed processes pinned to CPU 0.
- Governor: performance; SHA-NI available. SMT sibling CPU 8 and other workloads were not isolated.
- Rust nightly-2026-08-18 (LLVM 23.1.0), opt-level 3, thin LTO for both Rust libraries.
- Go 1.24.1, standard optimized build, GOAMD64=v1, GOMAXPROCS=1.
- nyx-ssz: `91ff00042f891887a1ee0abb5aaef69821218a26`.
- libssz and its three companion crates: published **0.3.0**, Cargo checksum locked,
  source revision `5f5144ba4d5871a846f38d6993b08330cfb82852`. This is the release,
  not the different main-branch snapshot examined in the earlier README survey.
- fastssz: `0b1f38e4319865f920e4d79822005c7918659fc1`; module version and checksums locked.

## Main results

**Microseconds/op; lower is better.** Values are medians of five independent
per-run means, not the fastest individual run.

| Schema | Operation | nyx-ssz | libssz | fastssz |
| --- | --- | ---: | ---: | ---: |
| header | encode | 0.563 | 0.015 | 0.035 |
| header | decode | 0.405 | 0.003 | 0.038 |
| header | root | 2.737 | 0.528 | 0.679 |
| mixed | encode | 70.577 | 0.213 | 2.161 |
| mixed | decode | 7.641 | 0.297 | 6.487 |
| mixed | root | 263.821 | 43.135 | 42.779 |

Header is the five-field, 112-byte BeaconBlockHeader. Mixed is a 12,304-byte
Container: u64 slot, ByteList[4096] payload and List[u64,1024] votes. Inputs are
deterministic. All three libraries agreed on exact encoded bytes, decoded field
values and tree roots before timing.

For this sample, Mixed encode is about **331× slower than libssz** and **33× slower
than fastssz**. Mixed root is about **6.1× slower** than either alternative.
Mixed decode versus fastssz is much closer; run variation does not justify a
precise ranking there.

## Separate preallocated encode results

Microseconds/op; these are **not** mixed into the new-output-buffer comparison.

| Schema | libssz | fastssz |
| --- | ---: | ---: |
| header | 0.005 | 0.008 |
| mixed | 0.201 | 0.650 |

nyx-ssz has no corresponding caller-buffer encode API, so no fabricated reuse
measurement is reported. Go reports zero allocations for both reuse cases.

## Method and caveats

- Rust: Criterion 0.7.0, 20 samples, one-second warmup and one-second measurement
  per case per run. Every result is black-boxed.
- Go: standard testing benchmarks, one-second target per case per run; outputs
  are retained in package-level sinks to prevent dead-code elimination.
- Rust and Go processes alternate order across runs. Both Rust libraries share
  one benchmark executable/profile. No concurrent benchmark processes are started.
- Main encode produces a new output buffer; decode starts with a fresh value.
  Rust result destruction and Go garbage collection follow their normal runtime
  behavior. Cross-language allocation/escape behavior is not identical.
- Roots use normal public APIs and standard backends: nyx-ssz's local scalar
  SHA-256, libssz's sha2 backend, fastssz's default sha256-simd hasher pool.
  No optional gohashtree override or persistent Merkle-result cache is introduced.
  These results include SHA-backend differences; they do not isolate container logic.
- The machine was shared, turbo/frequency was not locked, and SMT siblings were
  not isolated. Load average changed from 2.85/3.14/2.77 to 4.21/3.74/3.11.
  Variation is substantial: Mixed root spans 178.7–344.5 µs for nyx-ssz,
  32.6–63.7 µs for libssz and 42.1–78.6 µs for fastssz across runs.
  Do not rank close results or generalize exact ratios to all SSZ workloads.
- This covers two shapes and valid data only, not BeaconState, malformed input,
  proof generation, full corpus coverage or production load.

The checked-in [raw report](../tools/bench-compare/results/2026-10-22.json) contains
every run mean, ranges, Go allocation counts, exact wire bytes/root/digests,
compiler/library versions, machine state and a source-harness SHA-256 fingerprint.
The [harness README](../tools/bench-compare/README.md) gives reproduction commands.
The native library itself is unchanged by this benchmark work.
