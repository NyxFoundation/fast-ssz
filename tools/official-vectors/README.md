# Official SSZ vector runner

Requires the repository's pinned Rust toolchain, Python 3.11+, Git and network access on the first run.
From the repository root:

```sh
python3 scripts/official_vectors.py check --family boolean --family uints --family basic_vector
```

The wrapper fetches the immutable upstream commit from `sources.lock`, validates its entire SSZ-generic
subtree, then runs formatting, lints, runner unit tests and all selected official cases.
Fresh checkouts explicitly disable filter, text, ident and encoding conversions: host Git LFS or
line-ending settings cannot transform the pinned fixture blobs. Data is cached
under `$XDG_CACHE_HOME/nyx-ssz/official-vectors/<commit>` (default `~/.cache`). Altered fixture contents
or inventory fail; the cache is never reset to conceal changes. Fixture bytes are checked against the pinned Git blob hashes,
even if local Git index flags hide changes from `git status`. Verification ignores Git replacement
objects and disables cache-local hooks/fsmonitor. It avoids `git status` and other worktree commands
that can run clean filters; actual bytes and inventory are verified directly instead of trusting the index.

A separately pinned SHA-256 authenticates the inventory even if cached nested Git tree objects are
corrupted. It hashes the ASCII records `100644 blob <oid>\t<repository-relative-path>\0`, sorted by
path. For a source-pin update, derive and cross-check this manifest from the authoritative upstream
Git tree API or a fresh independently verified source; never bless an existing cache's own manifest.

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
