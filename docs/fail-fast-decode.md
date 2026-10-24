---
title: Fail-fast variable container decoding
last_updated: 2026-10-24
tags:
  - ssz
  - rust
  - performance
  - api
---
# Fail-fast variable container decoding

The codec API now returns `Result<T, CodecError>` directly. `Ssz::DecodeState`,
`DecodeFailure`, generated field-state types and sequence failure-state buffers are removed.
Completed values are dropped normally when a later child fails.

Derived containers const-evaluate field widths and header positions. Variable offsets are
read into fixed-size stack arrays, validated in specification order and converted directly
to field slices. The generated path no longer allocates `Vec<BodyRange>`, offsets or spans.
It remains safe Rust and preserves SSZ wire bytes, roots, declaration validation and protocol
error precedence.

This is an intentionally breaking API change. nyx-ssz is unpublished and had no downstream
compatibility requirement when the change was made.

## Observed timing

2026-10-24, AMD Ryzen 9 PRO 8945HS, Linux CPU 0, five rounds. Times are medians
of per-run means in nanoseconds.

| Decode fixture | Before | After | Observed speedup |
| --- | ---: | ---: | ---: |
| Header, 112 bytes | 20.301 | 10.431 | 1.95× |
| Mixed, 12,304 bytes | 545.743 | 407.767 | 1.34× |

Same-batch comparison after the change:

| Fixture | nyx-ssz | libssz 0.3.0 | fastssz | nyx/libssz time |
| --- | ---: | ---: | ---: | ---: |
| Header | 10.431 | 9.893 | 66.740 | 1.05× |
| Mixed | 407.767 | 319.306 | 11,540.000 | 1.28× |

The unchanged mixed controls improved by 3.7% for libssz and 4.8% for fastssz between
batches, less than nyx-ssz's 25.3% time reduction. The Header control moved in opposite
directions across libraries. These are shared-host observations, not randomized causal
trials or guaranteed speedups.

The mixed fixture owns a 4 KiB `ByteList` and 1,024 `u64` values. Its decode now performs
exactly two allocations—the owned field buffers—and zero reallocations. Generated container
layout metadata itself allocates nothing.

- [Before JSON](data/const-decode-after.json), source
  `ba460e0cab7054debe5530902434043d17a0bd47`.
- [After JSON](data/fail-fast-decode-after.json), source
  `78d5b91b255952aa0c54d50a4104381662da81fc`.
- Both reports use the same harness digest and contain all 22 cases, individual runs,
  fixtures, tool versions, CPU affinity and load averages.
- Reproduce with `python3 tools/bench-compare/run.py run --cpu 0 --rounds 5 --out <dir>`.

## Validation and formal status

The workspace tests, documentation tests, Clippy, formatting, 32-bit workspace tests,
117 script tests and all 4,601 pinned official corpus cases pass. The current Aeneas slice
still extracts successfully, but the local full check exceeded the available Lean build
window. The changed codec and derive laws are therefore explicitly unproved under
[#25](https://github.com/NyxFoundation/nyx-ssz/issues/25); no axiom or weakened domain is used.
