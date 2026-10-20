# Official SSZ vector runner

Requires the repository's pinned Rust toolchain, Python 3.11+, Git and network access on the first run.
From the repository root:

```sh
python3 scripts/official_vectors.py check --family boolean --family uints --family basic_vector
```

The wrapper fetches the immutable upstream commit from `sources.lock`, validates its entire SSZ-generic
subtree, then runs formatting, lints, runner unit tests and all selected official cases. Data is cached
under `$XDG_CACHE_HOME/nyx-ssz/official-vectors/<commit>` (default `~/.cache`). An altered cache fails;
it is never reset or silently reused. Fixture bytes are checked against the pinned Git blob hashes,
even if local Git index flags hide changes from `git status`.

Current coverage is 1,229 cases across `boolean`, `uints` and `basic_vector`: exact decoded YAML values,
serialized bytes, 32-byte roots and rejection of invalid encodings. Raw Snappy and YAML use maintained
Rust libraries, with input/output bounds and strict fixture inventories. Unknown schemas or requested
families fail. No unrecognized fixture is skipped.

Six other families are not yet supported. Omitting all `--family` arguments asks for the entire pinned
corpus and currently fails; this runner does not claim full SSZ conformance. The explicit supported
selection is also run by the root verification gate and both native Rust CI architectures.

To fetch and validate data without compiling the runner:

```sh
python3 scripts/official_vectors.py setup
```

The runner is a separate Cargo workspace: its parser/compression dependencies are test tooling,
not dependencies of the SSZ library or its extraction. `tools/official-vectors/Cargo.lock` is committed.
