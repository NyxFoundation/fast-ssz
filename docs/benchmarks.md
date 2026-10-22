---
title: Reproducible codec benchmarks
last_updated: 2026-10-22
tags:
  - ssz
  - rust
  - benchmarks
---
# Reproducible codec benchmarks

Run `cargo bench -p nyx-ssz --bench codec` with the pinned toolchain.
Criterion 0.7.0 uses 10 samples, one-second warmup and one-second measurement per operation.
The fixture is a derived Container with a u64, 4,096 bytes and 1,024 u64 votes
(12,304 encoded bytes).

2026-10-22, x86_64 Linux, AMD Ryzen 9 PRO 8945HS, optimized Cargo bench profile:

| Operation | Central estimate | Reported interval |
| --- | --- | --- |
| Encode | 60.73 µs | 55.61–67.57 µs |
| Decode | 5.73 µs | 4.74–6.66 µs |
| Root | 270.13 µs | 221.48–307.80 µs |
| Single proof | 231.41 µs | 220.70–248.54 µs |
| Multiproof | 252.42 µs | 237.10–273.42 µs |

These are diagnostic measurements on a shared development machine, not a comparative
performance claim. Small samples and observed outliers limit precision. Proof construction
currently serializes and builds the occupied tree; it is not a sublinear implementation.
SHA-256 is the local Rust implementation, not hardware-accelerated RustCrypto.
Criterion writes detailed reports under the ignored `target/criterion` directory.
