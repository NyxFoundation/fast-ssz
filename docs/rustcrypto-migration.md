---
title: RustCrypto SHA-256 migration
last_updated: 2026-10-23
tags:
  - ssz
  - rust
  - performance
---
# RustCrypto SHA-256 migration

Runtime `sha256::hash_pair` now delegates to pinned RustCrypto `sha2` 0.10.9,
using its standard CPU-dispatched backend, like libssz 0.3.0. The local scalar
SHA implementation is removed; no local fallback or forced portable backend remains.
The public signature and exact left/right concatenation are unchanged. A fixed
64-byte stack buffer avoids heap allocation in the wrapper.

## Measured result

Same-day remeasurement on 2026-10-23, AMD Ryzen 9 PRO 8945HS, Linux CPU 0,
SHA instructions available, unchanged pinned Rust/Go tools and benchmark settings.
Five runs per version; values are medians of per-run mean times, in microseconds.

| Root fixture | Scalar recheck | RustCrypto | Speedup |
| --- | ---: | ---: | ---: |
| Header, 112 encoded bytes | 2.728 | 0.740 | 3.69× |
| Mixed Container, 12,304 encoded bytes | 179.353 | 68.251 | 2.63× |

The same batches' encode/decode medians differ by less than 4%; no codec/allocation
optimization is included. Unchanged libssz/fastssz root controls differ by at most
about 3%. All three libraries still agree on every fixture byte and root.

Current root comparison from the RustCrypto batch:

| Fixture | nyx-ssz | libssz | fastssz |
| --- | ---: | ---: | ---: |
| Header | 0.740 | 0.492 | 0.676 |
| Mixed | 68.251 | 33.048 | 42.787 |

nyx-ssz remains slower; temporary allocations and packing are not addressed here.

## Evidence and limits

- Scalar source: `5aaa7c8371c822c3cee850d18379bb8a727d6e12`.
- RustCrypto source: `cc999507a88698168aa9d5d1247cfaf629b70fc3`.
- [Scalar recheck JSON](../tools/bench-compare/results/2026-10-23-scalar.json).
- [RustCrypto JSON](../tools/bench-compare/results/2026-10-23-rustcrypto.json).
- [Harness and reproduction](../tools/bench-compare/README.md).

Each JSON contains every run, fixture bytes/roots, tool/library revisions, affinity,
load and harness digest. Benchmark source/settings are unchanged; the harness digest
changes because the Cargo lock records sha2 as a production dependency of nyx-ssz.

These are consecutive five-run batches, not interleaved version trials. RustCrypto
was measured first, then the scalar baseline was rechecked. This is a shared development
machine with load/outliers, not a confidence-interval or universal performance claim.
The older 2026-10-22 mixed-root scalar measurement was 263.821 µs; it is deliberately
**not** used to calculate the improvement above because the same-day scalar recheck
was faster. CPU affinity is per process; no global machine setting was changed.

## Formal status

Twelve hash-independent gindex/helper-index operations are freshly extracted and
kernel checked. Six formerly proved hash/Merkle operations are now explicitly
**unproved**, tracked in [#27](https://github.com/NyxFoundation/nyx-ssz/issues/27).
No hash axiom or old scalar implementation is used to pretend that RustCrypto is proved.
See [current verification scope](current-verification.md).
