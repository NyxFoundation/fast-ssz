---
title: Fixed container encode optimization
last_updated: 2026-10-24
tags:
  - benchmarks
  - codecs
  - ownership
---
# Fixed container encode optimization

All-fixed, non-progressive containers now validate every child in order and write
those bytes directly. They no longer build offset headers. Variable and progressive
containers still use `ContainerWriter`. A later protocol error still wins over an
earlier deferred native overflow. `ByteVector` values of at most 32 bytes copy from
inline storage. The allocating `encode()` still creates exactly one output buffer.

These changed laws remain unproved under
[#25](https://github.com/NyxFoundation/nyx-ssz/issues/25) and
[#29](https://github.com/NyxFoundation/nyx-ssz/issues/29).

## Measurement

Before is `ab8a39385305b26c16bf5d08c844c3b180134af8`. After is
`4b154ec5e8fd05b4c9a43727d893658317559821`. The harness and fixture wires match.
CPU 0, five rounds. Numbers are nanoseconds per operation, median of per-run means.
The after load average was about 12, so controls moved and small differences are
not claimed.

| Operation | nyx before | nyx after | libssz after | same-run nyx/libssz |
|---|---:|---:|---:|---:|
| Header encode | 143.42 | 83.14 | 27.23 | 3.05x |
| Header decode | 83.64 | 111.35 | 12.07 | 9.22x |
| Mixed encode | 707.86 | 807.73 | 289.12 | 2.79x |

Header encode's after runs were 80.5, 80.7, 83.1, 89.1 and 210.5 ns. Four of five
beat the previous 143.42 ns median while the machine was slower for libssz
(16.9 ns before, 27.2 ns after). The absolute improvement is therefore real, but
the 3.05x ratio is not a stable comparison with the earlier 8.5x figure. Header
decode and mixed encode moved with the controls and are not regressions or wins
from this change. Mixed containers contain variable fields, so they do not use
this path.

Raw runs: [data/fixed-encode-after.json](data/fixed-encode-after.json).
