---
title: Direct encode optimization
last_updated: 2026-10-23
tags:
  - ssz
  - rust
  - performance
---
# Direct encode optimization

This records the initial direct-write stage. Newer length-arithmetic results are in
[bulk codec optimization](bulk-codecs.md).

Typed encoding now calculates the validated length and writes directly into an
exactly sized slice. The default `encode()` allocates its output Vec once; scalar,
collection and generated field codecs no longer build encoded-child Vecs.
No unsafe code, new runtime dependency or compatibility fallback is introduced.
Decode/root algorithms are not changed, although their shared encoding calls can
benefit indirectly. Manual trait implementors must migrate; see the
[API contract and example](native-api.md#direct-encoding).

## Deterministic allocation regression

The shared mixed Container contains a u64, 4,096 payload bytes and 1,024 u64 votes,
encoding to 12,304 bytes. `stats_alloc` is a test-only dependency.

| Operation | Allocations | Reallocations |
| --- | ---: | ---: |
| Previous allocating encode | 1,030 | 38 |
| Direct-path allocating encode | 1 | 0 |
| Direct encode into an existing slice | 0 | 0 |

The test was first observed failing on the old implementation with the first row,
then passing with one output allocation. Input construction and destination allocation
are outside the measured region. Buffer reuse is not substituted for allocating encode
in the timing comparison below.

## Observed timing

2026-10-23, AMD Ryzen 9 PRO 8945HS, Linux CPU 0, pinned tools and the unchanged
three-library harness. Each value is a median of five per-run means, in microseconds.

| Fixture | Previous encode | Direct-path encode | Observed ratio |
| --- | ---: | ---: | ---: |
| Header, 112 bytes | 0.9785 | 0.1796 | 5.45× |
| Mixed, 12,304 bytes | 75.2871 | 1.6839 | 44.71× |

Same-batch allocating encode comparison after the change:

| Fixture | nyx-ssz | libssz 0.3.0 | fastssz | nyx/libssz time |
| --- | ---: | ---: | ---: | ---: |
| Header | 0.1796 | 0.0264 | 0.0645 | 6.80× |
| Mixed | 1.6839 | 0.2834 | 2.7740 | 5.94× |

nyx-ssz still does not match libssz. Remaining CPU costs are not profiled in this change.

### Limits and evidence

These are **observations, not isolated or universal speedup guarantees**. The shared
machine was heavily loaded. The unchanged Rust libssz encode control moved from
0.0187 to 0.0264 µs for Header and 0.1743 to 0.2834 µs for Mixed, a roughly 1.4–1.6×
variation. The Go encode controls were much steadier. Versions ran in consecutive
batches, direct first and baseline second, not interleaved or randomized. Do not
attribute every timing difference, especially decode/root differences, to this encoder.
The allocation reduction is independently asserted by regression tests.

- [Before JSON](../tools/bench-compare/results/2026-10-23-before-direct.json), source
  `28b82ef8ce28beff1d3a849fd1894b67f1341bd8`.
- [After JSON](../tools/bench-compare/results/2026-10-23-direct-encode.json), source
  `958caecaefaf5c55c2da52456d7e88fb7a6eab23`.
- Both JSONs have the identical harness digest, fixtures, wire bytes and roots.
  Every run, tool/library version, CPU affinity and load is retained, including outliers.
- Reproduce using [the existing harness](../tools/bench-compare/README.md) with `--cpu 0 --rounds 5`.

## Correctness and formal scope

All 4,601 pinned official cases pass. Typed valid cases now check encoded length and
direct-write bytes against the independent corpus, as well as allocating encode/root.
Host and 32-bit tests cover exact destination widths, untouched surrounding bytes,
empty/variable bodies, nested offsets, huge symbolic lengths and fault precedence.
The native output/protocol overflow distinction and strict parent envelope remain unchanged.

Twelve hash-independent current-source proofs remain kernel checked. The new length,
destination and default-method laws are **unproved** under
[#29](https://github.com/NyxFoundation/nyx-ssz/issues/29). The existing historical
`CodecLaw` does not cover these methods, and the full proof gate explicitly rejects
that gap. No axiom, narrowed input domain or weakened fault relation is used.
