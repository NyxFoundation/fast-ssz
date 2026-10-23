#!/usr/bin/env python3
"""Bounded extraction attempt of the actual runtime hash wrapper, not a proof."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys
import verify as legacy
import current_refinement as current


def attempt(command, directory, seconds, name):
    with (directory / f"{name}.log").open("w") as output:
        result = subprocess.run(["timeout", "--kill-after=5s", f"{seconds}s", *map(str, command)],
                                cwd=legacy.ROOT, stdout=output, stderr=subprocess.STDOUT)
    return result.returncode


def probe(directory, seconds, opaque):
    pins = legacy.load_pins()
    legacy.validate_pins(pins)
    legacy.validate_tools(pins)
    directory.mkdir(parents=True, exist_ok=False)
    llbc = directory / "probe.llbc"
    command = [legacy.tool_path("charon", pins), "cargo", "--preset=aeneas", "--precise-drops",
               "--sysroot", "default", "--start-from", "nyx_rustcrypto_probe::sha256::hash_pair"]
    if not opaque:
        for crate in ("sha2", "digest", "block_buffer", "crypto_common", "generic_array", "cpufeatures"):
            command.extend(["--include", crate])
    command.extend(["--dest-file", llbc, "--", "--lib", "--locked", "--manifest-path",
                    "verification/rustcrypto-probe/Cargo.toml", "--target-dir", directory / "cargo"])
    code = attempt(command, directory, seconds, "charon")
    if code == 0:
        code = attempt(current.aeneas_command(pins, directory, llbc), directory, seconds, "aeneas")
    print(f"Extraction exit status: {code}. Equivalence remains UNPROVED; see issue #27.")
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="new artifact directory")
    parser.add_argument("--seconds", type=int, default=90, help="per-stage limit (1..3600)")
    parser.add_argument("--opaque-dependencies", action="store_true")
    args = parser.parse_args()
    if not 1 <= args.seconds <= 3600 or not shutil.which("timeout"):
        parser.error("a 1..3600 second limit and GNU timeout are required")
    return probe(args.out.resolve(), args.seconds, args.opaque_dependencies)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.CalledProcessError):
        print("extraction attempt failed; equivalence remains unproved", file=sys.stderr)
        sys.exit(1)
