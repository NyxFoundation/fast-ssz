---
title: Small fixed decode optimization
last_updated: 2026-10-23
tags:
  - benchmarks
  - codecs
  - ownership
---
# Small fixed decode optimization

Header decode was allocating a range table and three 32-byte buffers. All-fixed,
non-progressive containers now split field slices after declaration and exact-length
checks. `ByteVector` values of at most 32 bytes are copied into the value. Larger
vectors and every `ByteList` still move their `Vec`. Progressive and variable
containers keep the existing view. No crate-local unsafe was added.

Allocation tests count zero allocations for a 32-byte vector and for the 112-byte
header, and one allocation for a 33-byte vector. Fixed-field failures still retain
completed owners. These laws remain unproved under
[#25](https://github.com/NyxFoundation/nyx-ssz/issues/25).

## Same-workload measurement

Before is the previous bulk-codec revision `7e6716e08cebb8f3b11ead4df2facdff1a117da8`.
After is `ab8a39385305b26c16bf5d08c844c3b180134af8`. The harness hash and fixture
wires are unchanged. Both use CPU 0 and five rounds. Numbers are nanoseconds per
operation, median of per-run means.

The after machine load was about 10, so only differences that the unchanged libssz
control does not show are treated as real.

| Operation | nyx before | nyx after | libssz after | nyx/libssz after |
|---|---:|---:|---:|---:|
| Header decode | 153.85 | 83.64 | 7.24 | 11.55x |
| Header encode | 104.01 | 143.42 | 16.88 | 8.50x |
| Header root | 800.78 | 1,068.02 | 548.98 | 1.95x |
| Mixed decode | 379.64 | 480.69 | 323.42 | 1.49x |

Header decode's five after runs were 62.1, 79.7, 83.6, 94.6 and 104.6 ns. Every run
beat the previous 153.85 ns median, while libssz stayed at 7.2 ns (before 7.23).
That is about **1.84x faster**, and the gap to libssz fell from 21.3x to 11.6x.
It is not parity. libssz's header is three raw `[u8; 32]` arrays and does not walk
a separate type declaration.

Header encode, header root and mixed decode moved with the high load. Their libssz
controls also moved, so this run does not establish a regression or a further win.
Raw runs are in [data/small-decode-after.json](data/small-decode-after.json). The
previous batch is [data/bulk-codecs-after.json](data/bulk-codecs-after.json).
