#!/usr/bin/env python3
"""Validate identical SSZ inputs, then measure three libraries on one CPU core."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

from measurements import parse_criterion, parse_go, summarize

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
MANIFEST = BASE / "Cargo.toml"


def run(arguments, *, cwd=ROOT, env=None):
    result = subprocess.run([str(arg) for arg in arguments], cwd=cwd, env=env,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
        raise RuntimeError("benchmark command failed")
    return result.stdout


def environment(output):
    env = os.environ.copy()
    for key in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_TARGET", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "GOFLAGS"):
        env.pop(key, None)
    env.update({"CARGO_TARGET_DIR": str(BASE / "target"), "CRITERION_HOME": str(output / "criterion"),
                "GOMAXPROCS": "1", "GOTOOLCHAIN": "local", "NYX_BENCH_FIXTURES": str(output / "fixtures.json")})
    return env


def prepare(output, env):
    run(["cargo", "test", "--locked", "--manifest-path", MANIFEST], env=env)
    fixtures = run(["cargo", "run", "--locked", "--quiet", "--release", "--manifest-path", MANIFEST, "--bin", "fixtures"], env=env)
    (output / "fixtures.json").write_text(fixtures)
    run(["go", "test", "-count=1", "./..."], cwd=BASE / "go", env=env)
    run(["go", "test", "-c", "-o", output / "fastssz.test"], cwd=BASE / "go", env=env)
    messages = run(["cargo", "bench", "--locked", "--manifest-path", MANIFEST, "--bench", "compare", "--no-run", "--message-format=json"], env=env)
    candidates = [entry["executable"] for line in messages.splitlines()
                  if (entry := json.loads(line)).get("reason") == "compiler-artifact"
                  and entry["target"]["name"] == "compare" and entry.get("executable")]
    if len(candidates) != 1:
        raise ValueError("expected one compiled Criterion executable")
    return candidates[0]


def source_versions(env):
    metadata = json.loads(run(["cargo", "metadata", "--locked", "--format-version=1", "--manifest-path", MANIFEST], env=env))
    libraries = {}
    for package in metadata["packages"]:
        if package["name"].startswith("libssz"):
            vcs = json.loads(Path(package["manifest_path"]).with_name(".cargo_vcs_info.json").read_text())
            libraries[package["name"]] = {"version": package["version"], "git_revision": vcs["git"]["sha1"]}
    go = json.loads(run(["go", "list", "-m", "-json", "github.com/ferranbt/fastssz"], cwd=BASE / "go", env=env))
    libraries["fastssz"] = {"version": go["Version"], "git_revision": "0b1f38e4319865f920e4d79822005c7918659fc1"}
    libraries["nyx"] = {"git_revision": run(["git", "rev-parse", "HEAD"]).strip()}
    return libraries


def machine(cpu, env):
    info = Path("/proc/cpuinfo").read_text()
    model = next(line.split(":", 1)[1].strip() for line in info.splitlines() if line.startswith("model name"))
    governor = Path(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_governor")
    siblings = Path(f"/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list")
    return {"cpu_model": model, "logical_cpu": cpu, "available_cpus": sorted(os.sched_getaffinity(0)),
            "smt_siblings": siblings.read_text().strip(), "governor": governor.read_text().strip(),
            "sha_ni_available": "sha_ni" in info.split(), "os": platform.system(), "kernel": platform.release(),
            "rustc": run(["rustc", "-Vv"], env=env).strip(), "go": run(["go", "version"], env=env).strip(),
            "go_amd64": run(["go", "env", "GOAMD64"], env=env).strip(), "load_average_before": os.getloadavg()}


def harness_digest():
    paths = [BASE / name for name in ("Cargo.toml", "Cargo.lock", "run.py", "measurements.py", "go/go.mod", "go/go.sum")]
    paths.extend(BASE.glob("src/**/*.rs")); paths.extend(BASE.glob("benches/*.rs")); paths.extend(BASE.glob("go/*.go"))
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(path.relative_to(BASE).as_posix().encode() + b"\0" + path.read_bytes() + b"\0")
    return digest.hexdigest()


def measure_round(index, cpu, executable, output, env):
    baseline = f"round{index}"
    rust_command = ["taskset", "-c", cpu, executable, "--bench", "--noplot", "--save-baseline", baseline]
    go_command = ["taskset", "-c", cpu, output / "fastssz.test", "-test.run=^$", "-test.bench=Benchmark(Header|Mixed)$", "-test.benchtime=1s", "-test.count=1", "-test.cpu=1"]
    commands = [("rust", rust_command), ("go", go_command)]
    for name, command in (commands if index % 2 else commands[::-1]):
        (output / f"{name}-{index}.log").write_text(run(command, env=env))
    return {**parse_criterion(output / "criterion", baseline), **parse_go((output / f"go-{index}.log").read_text())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "run"))
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--rounds", type=int, default=5)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.cpu not in os.sched_getaffinity(0) or not 1 <= args.rounds <= 20:
        parser.error("CPU must be allowed and rounds must be in 1..20")
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = environment(output)
    executable = prepare(output, env)
    if args.command == "check":
        print("Both fixtures have identical bytes, decoded values and roots across all three libraries.")
        return
    metadata = machine(args.cpu, env)
    rounds = []
    for index in range(1, args.rounds + 1):
        print(f"Measuring round {index}/{args.rounds} on CPU {args.cpu}", flush=True)
        rounds.append(measure_round(index, args.cpu, executable, output, env))
    metadata["load_average_after"] = os.getloadavg()
    report = {"format_version": 1, "measured_at": datetime.now(timezone.utc).isoformat(), "machine": metadata,
              "libraries": source_versions(env), "harness_sha256": harness_digest(), "rounds": args.rounds,
              "statistic": "median of per-run means in ns/op", "fixtures": json.loads((output / "fixtures.json").read_text()),
              "results": summarize(rounds)}
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Measured {len(report['results'])} cases; report.json contains every run and the full provenance.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, RuntimeError):
        print("Benchmark run failed; no successful comparison is claimed.", file=sys.stderr)
        sys.exit(1)
