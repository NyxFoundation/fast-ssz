# Three-library SSZ benchmark harness

Compare nyx-ssz, published libssz 0.3.0 and pinned ferranbt/fastssz on identical
BeaconBlockHeader (112 bytes) and mixed Container (12,304 bytes) values.

Requires Linux with taskset, the repository's pinned Rust toolchain, Python 3.11+
and Go 1.24.1 or newer. Dependencies are locked by Cargo.lock and go/go.sum.
No benchmark runs automatically during ordinary tests.

From the repository root:

```sh
python3 -m unittest discover -s tools/bench-compare -p 'test_*.py'
python3 tools/bench-compare/run.py check --out tools/bench-compare/.runs/check-1
python3 tools/bench-compare/run.py run --cpu 0 --rounds 5 \
  --out tools/bench-compare/.runs/run-1
```

The output directory must not already exist. Select a CPU from the process's
allowed affinity mask; the default is its lowest allowed CPU. Runs alternate
Rust/Go process order, pin both to the same CPU and use one Go scheduler thread.

The runner first compares both Rust implementations' exact wire bytes/roots and
round trips, then verifies fastssz's encoding, decoded fields and roots against
the same fixtures. It compiles both benchmark executables before timing.
It refuses incomplete, duplicate or nonfinite results. Existing files are never reset.

Main cases: new-buffer encode, fresh-value decode and normal public-API root.
Preallocated encode is a separate category for libssz/fastssz; nyx-ssz has no
matching API. Rust uses Criterion (20 samples, 1s warmup, 1s measurement);
Go uses testing (1s target per case). The report uses medians of per-run means.
Cross-language GC/destruction and SHA-backend differences remain part of API cost.

`report.json` stores all run means and provenance. `fixtures.json`, raw logs and
Criterion estimates remain in the ignored run directory. No CPU governor, boost,
system affinity or other global machine setting is changed.

Generated Go methods are committed. To verify reproducibility:

```sh
cd tools/bench-compare/go
go generate ./...
git diff --exit-code -- encoding.go
```

Do not hand-edit encoding.go. The generator resolves the same pinned module as
the library. Its normal default SHA backend is used, not the optional gohashtree override.

Measured results and limitations: [comparison](../../docs/benchmark-comparison.md).
