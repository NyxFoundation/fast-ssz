# Version-aligned official SSZ vector runner

Requires the repository's pinned Rust toolchain, Python 3.11+, Git and network access on the first run.
Install the pinned oracle decompressor with `python3 -m pip install -r tools/official-vectors/requirements.txt`.
From the repository root:

```sh
python3 scripts/official_vectors.py check
```

The wrapper checks formatting, lints, unit tests and all 4,601 source cases in all nine families. It compares
exact decoded YAML values, encoded bytes, 32-byte roots and rejection of invalid encodings. Bit-family
cases exercise both borrowed operations and actual owned BitVector/BitList/ProgressiveBitList Ssz
dictionaries, including each logical bit/getter and out-of-range access. The `uint8` basic-vector
cases exercise both generic `Vector<u8, N>` and dedicated owned `ByteVector<N>` dictionaries.
Owned ByteList fixture parsing, limits, values and roots also have unit regressions; this corpus has
no standalone byte-list family. Unknown schemas or selected families fail; no fixture is silently skipped. The malformed bitlist cases whose
upstream names omit a capacity are checked at both zero and machine-maximum capacity rather than
inventing one declaration. Container and ProgressiveContainer fixtures use the actual public derive,
including nested collections and bitfields. Omitting `--family` checks the complete pinned corpus.
This corpus does not contain a CompatibleUnion family; independent union tests cover it.

## Original corpus integrity

The immutable upstream commit in `sources.lock` is fetched into
`$XDG_CACHE_HOME/nyx-ssz/official-vectors/<commit>` (default `~/.cache`). Data is not vendored.
Altered fixture contents or inventory fail; the cache is never reset to conceal changes. Source
checks use the independently pinned SHA-256 inventory plus actual Git blob hashes, not index status.
Replacement refs are disabled, as are hooks/fsmonitor. Verification avoids filter-capable worktree
commands. Fresh checkouts force raw blobs without filter/text/ident/encoding transformations, so
host Git LFS or line-ending settings cannot mutate the data or trigger false modification reports.

The manifest authenticates the ASCII records `100644 blob <oid>\t<repository-relative-path>\0`, sorted
by path, independently of mutable cached Git objects. For pin updates derive and cross-check it from
an authoritative upstream Git tree or a fresh independently verified source, never from an existing
cache alone. Real regression repositories exercise replacement refs, corrupt nested objects, hidden
worktree modifications and executable Git filter/fsmonitor configuration.

## Progressive root version alignment

The published corpus is `v1.6.0-beta.0` from September 2025. Its Progressive roots predate the official
[2026 orientation fix](https://github.com/ethereum/remerkleable/commit/4c07ef2e9078b36e7887581f8966ea6b18b8e695).
The current EIP, pinned Lean executable and Rust implementation use a right-hand recursive spine.
The original corpus and metadata are preserved, not edited or treated as current-version roots.

For `progressive_bitlist`, `basic_progressive_list`, `containers` and `progressive_containers`,
1,744 root expectations are regenerated using the official reference commit in `sources.lock`
(1,109 differ from the original roots, including nested Progressive values). Its archive is cached separately under
`$XDG_CACHE_HOME/nyx-ssz/reference-oracle/<commit>` and authenticated against its pinned SHA-256 before
any source is extracted or executed. Extraction accepts only bounded, regular entries below the exact
revision prefix. An isolated Python process imports that authenticated pure-Python reference.
The separately pinned Snappy dependency decompresses Container inputs; it does not compute SSZ roots.
Wire values must remain unchanged.

Generated expectations live only in a temporary file. The Rust runner requires their exact reference
and corpus revisions, checks every original published root before using its current-version replacement,
and requires the entire generated inventory to be exercised exactly once. There is no obsolete-root
fallback or root-skipping mode. The runtime prints regeneration, correction and selected-case counts.

## Contradictory published labels

The old basic-ProgressiveList data labels 237 inputs invalid despite their compressed blobs being
byte-identical to valid fixtures of the same primitive type (30 empty and 207 nonempty). For example,
`invalid/proglist_uint128_0_max_one_byte_less` and `valid/proglist_uint128_max_0` both contain the same
empty wire value. Rejecting it would contradict both the valid case and the fixed Lean specification.

The version-2 generated profile records an explicit valid-witness key for each such case. The original
labels/data remain unchanged. The current official reference roots each valid witness; the runner
requires its original root metadata, same primitive declaration and exact decompressed byte equality.
It then verifies the formerly-invalid input against that witness's full YAML value, canonical bytes
and current root. Missing/repeated, cross-type, escaping or unused witnesses fail. Every other invalid
fixture must still be rejected; no invalid input is ignored or blanket reclassified.

## Setup and integration

To fetch and validate only the original corpus:

```sh
python3 scripts/official_vectors.py setup
```

Both native Rust CI architectures run all nine families. The formal gate's historical slice is not evidence of full native conformance.
The runner is a separate Cargo workspace: its parser/compression dependencies are test tooling, not
SSZ runtime/extraction dependencies. `tools/official-vectors/Cargo.lock` is committed. The oracle is an
independent test implementation, not an additional formal-correctness axiom.
