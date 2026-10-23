# RustCrypto extraction probe

This separate Cargo root includes the actual production `sha256.rs`; it does not
provide a copied implementation, a fake hasher or an opaque-hash axiom. Its locked
`sha2` dependency uses the same normal default features as the runtime.

After installing the repository's pinned tools, run from the repository root:

```sh
python3 scripts/probe_rustcrypto.py --out target/crypto-expanded-1 --seconds 90
python3 scripts/probe_rustcrypto.py --out target/crypto-opaque-1 --seconds 45 --opaque-dependencies
```

Requires Python 3.11+, GNU coreutils `timeout`, and the pinned Rust/Charon/Aeneas
tools. Output directories must be new. Cargo uses the normal pinned compiler
sysroot, without unrelated nyx-ssz derive dependencies. Expanded mode includes
sha2, digest, block_buffer, crypto_common, generic_array and cpufeatures.

Each tool stage is bounded separately; GNU timeout terminates the process group
and escalates after five seconds. Logs, Cargo artifacts and any LLBC/Lean output
remain in the chosen directory. Status 124 means the time budget expired.
Completing extraction would still not establish an equivalence theorem.

The recorded 90-second expanded and 45-second opaque attempts timed out before
LLBC creation. That is bounded tooling/resource evidence, not a diagnosis of an
upstream bug or proof of impossibility. See [issue #27](https://github.com/NyxFoundation/nyx-ssz/issues/27).
Current CI validates the recorded wrapper/dependency/tool fingerprints, not this
timing-dependent probe. It never counts the six dependent laws as proved.
