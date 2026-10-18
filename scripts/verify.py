#!/usr/bin/env python3
"""Reproduce and check the implemented SSZ proof slice, not full SSZ conformance."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
VERIFICATION = ROOT / "verification"
GENERATED = VERIFICATION / "FastSszRust.lean"


def run(arguments, *, cwd=ROOT, capture=False):
    return subprocess.run(
        [str(argument) for argument in arguments],
        cwd=cwd,
        check=True,
        text=True,
        stdout=subprocess.PIPE if capture else None,
    ).stdout


def load_pins():
    with (ROOT / "sources.lock").open("rb") as source:
        return tomllib.load(source)


def load_targets(path=VERIFICATION / "targets.json"):
    targets = json.loads(path.read_text())
    if not isinstance(targets, list) or not targets:
        raise ValueError("the extraction target list must be nonempty")
    for target in targets:
        if not isinstance(target, dict):
            raise ValueError("each extraction target must be an object")
        for field, separator in (("rust", "::"), ("lean", "."), ("proof", ".")):
            if not isinstance(target.get(field), str):
                raise ValueError(f"extraction target {field} must be a string")
            parts = target[field].split(separator)
            if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", part) for part in parts):
                raise ValueError(f"invalid {field} identifier in extraction targets")
    if len({target["rust"] for target in targets}) != len(targets):
        raise ValueError("duplicate Rust extraction targets")
    return targets


def tool_path(tool, pins):
    cache = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    binary = cache / "hax" / "tools" / tool / pins["tools"][f"{tool}_version"] / tool
    if not binary.is_file():
        raise ValueError(f"{tool} is not installed; run python3 scripts/verify.py bootstrap")
    return binary


def validate_pins(pins):
    tools = pins["tools"]
    with (ROOT / "rust-toolchain.toml").open("rb") as source:
        rust = tomllib.load(source)["toolchain"]["channel"]
    with (ROOT / "hax.toml").open("rb") as source:
        hax = tomllib.load(source)
    lean = (VERIFICATION / "lean-toolchain").read_text().strip()
    if rust != tools["rust_toolchain"] or lean != tools["lean_toolchain"]:
        raise ValueError("Rust or Lean toolchain differs from sources.lock")
    for tool in ("charon", "aeneas"):
        if hax["tools"][tool] != tools[f"{tool}_version"]:
            raise ValueError(f"{tool} pin differs from sources.lock")
    if hax["versions"]["lean"] != lean:
        raise ValueError("hax Lean version differs from sources.lock")


def validate_tools(pins):
    aeneas = tool_path("aeneas", pins)
    charon = tool_path("charon", pins)
    tools = pins["tools"]
    if run([aeneas, "-version"], capture=True).strip() != f"aeneas {tools['aeneas_version']}":
        raise ValueError("unexpected Aeneas version")
    if tools["charon_revision"] not in run([charon, "version"], capture=True):
        raise ValueError("unexpected Charon revision")
    if run([charon, "toolchain-version"], capture=True).strip() != tools["rust_toolchain"]:
        raise ValueError("Charon and Rust toolchains differ")
    lean_version = run(["lean", "--version"], cwd=VERIFICATION, capture=True)
    if tools["lean_toolchain"].split(":v")[1] not in lean_version:
        raise ValueError("unexpected Lean version")


def validate_dependencies(pins):
    manifest = json.loads((VERIFICATION / "lake-manifest.json").read_text())
    expected = {
        "ssz": (pins["specification"]["repository"], pins["specification"]["revision"]),
        "aeneas": (pins["tools"]["aeneas_repository"], pins["tools"]["aeneas_revision"]),
    }
    for package in manifest["packages"]:
        if package["type"] != "git":
            raise ValueError("verification dependencies must use pinned Git sources")
        if package["name"] in expected:
            if (package["url"], package["rev"]) != expected.pop(package["name"]):
                raise ValueError("Lake manifest differs from sources.lock")
        directory = VERIFICATION / ".lake" / "packages" / package["name"]
        revision = run(["git", "rev-parse", "HEAD"], cwd=directory, capture=True).strip()
        dirty = run(["git", "status", "--porcelain"], cwd=directory, capture=True).strip()
        if revision != package["rev"] or dirty:
            raise ValueError(f"dependency {package['name']} is modified or at the wrong revision")
    if expected:
        raise ValueError("the specification or Aeneas dependency is missing")


def bootstrap(pins):
    version = run(["cargo", "hax", "--version"], capture=True).splitlines()
    if f"version={pins['tools']['cargo_hax_version']}" not in version:
        raise ValueError("install the cargo-hax version recorded in sources.lock")
    for tool in ("charon", "aeneas"):
        run(["cargo", "hax", "tools", "install", f"{tool}@{pins['tools'][f'{tool}_version']}"])
    validate_tools(pins)
    run(["lake", "exe", "cache", "get"], cwd=VERIFICATION)
    run(["lake", "build", "Aeneas", "Ssz"], cwd=VERIFICATION)
    validate_dependencies(pins)


def extract(pins, targets, destination):
    llbc = destination / "fast_ssz.llbc"
    arguments = [tool_path("charon", pins), "cargo", "--preset=aeneas"]
    for target in targets:
        arguments.extend(["--start-from", target["rust"]])
    arguments.extend([
        "--dest-file", llbc, "--", "--lib", "--manifest-path", "crates/fast-ssz/Cargo.toml",
    ])
    run(arguments)
    run([
        tool_path("aeneas", pins), "-backend", "lean", "-namespace", "FastSszRust",
        "-abort-on-error", "-warnings-as-errors", "-no-progress-bar",
        "-dest", destination, llbc,
    ])
    return (destination / "FastSsz.lean").read_bytes()


def assert_same_artifact(actual, expected):
    if actual != expected:
        raise ValueError("Rust extraction is stale; run python3 scripts/verify.py extract and review the diff")


def api_functions(document):
    for identifier, item in document.get("index", {}).items():
        if item["crate_id"] != 0 or item["visibility"] != "public":
            continue
        if "trait" in item["inner"]:
            raise ValueError("public traits require extending the proof coverage checker")
        if "function" in item["inner"] and identifier not in document["paths"]:
            raise ValueError("public associated functions require extending the proof coverage checker")
    return {
        "::".join(item["path"])
        for item in document["paths"].values()
        if item["crate_id"] == 0 and item["kind"] == "function"
    }


def assert_api_covered(functions, targets):
    registered = {target["rust"] for target in targets}
    if functions != registered:
        missing = sorted(functions - registered)
        stale = sorted(registered - functions)
        raise ValueError(f"API/extraction coverage differs; missing={missing}, stale={stale}")


def check_api(targets):
    directory = ROOT / "target" / "api-coverage"
    run([
        "cargo", "rustdoc", "--lib", "--package", "fast-ssz", "--target-dir", directory,
        "--", "--output-format", "json", "-Z", "unstable-options",
    ])
    document = json.loads((directory / "doc" / "fast_ssz.json").read_text())
    assert_api_covered(api_functions(document), targets)


def assert_import_closure(directory):
    modules = {
        ".".join(path.relative_to(directory).with_suffix("").parts): path
        for path in directory.rglob("*.lean")
        if not any(part.startswith(".") or part == "extraction" for part in path.relative_to(directory).parts)
    }
    visited = set()
    pending = ["FastSszVerification.Audit"]
    while pending:
        module = pending.pop()
        if module in visited or module not in modules:
            continue
        visited.add(module)
        for line in modules[module].read_text().splitlines():
            if line.startswith("import "):
                pending.extend(line.removeprefix("import ").split())
    if set(modules) != visited:
        raise ValueError(f"Lean files outside the audited import closure: {sorted(set(modules) - visited)}")


def check_proof_targets(targets, directory):
    lines = ["import FastSszVerification.Audit"]
    lines.extend(f"check_refinement {target['lean']} via {target['proof']}" for target in targets)
    file = directory / "CheckTargets.lean"
    file.write_text("\n".join(lines) + "\n")
    run(["lake", "env", "lean", file], cwd=VERIFICATION)


def check_rejection_guards(directory):
    cases = {
        "ForbiddenAxiom": (
            "namespace FastSszVerification\naxiom forbidden : False\nend FastSszVerification\n"
            "audit_fast_ssz\n",
            "forbidden axiom",
        ),
        "NativeEvaluation": (
            "namespace FastSszVerification\n"
            "theorem nativeResult : (List.range 100).length = 100 := by native_decide\n"
            "end FastSszVerification\naudit_fast_ssz\n",
            "forbidden axiom",
        ),
        "UnrelatedTheorem": (
            "check_refinement FastSszRust.scalar.encode_bool via "
            "FastSszVerification.decode_bool_refines\n",
            "does not mention",
        ),
    }
    for label, (source, expected) in cases.items():
        file = directory / f"{label}.lean"
        file.write_text("import FastSszVerification.Audit\n" + source)
        result = subprocess.run(
            ["lake", "env", "lean", str(file)], cwd=VERIFICATION,
            text=True, capture_output=True, check=False,
        )
        if result.returncode == 0 or expected not in result.stdout + result.stderr:
            raise ValueError(f"proof guard did not reject {label} for the expected reason")


def check(pins, targets, directory):
    validate_tools(pins)
    run(["cargo", "fmt", "--all", "--", "--check"])
    run(["cargo", "clippy", "--workspace", "--all-targets", "--", "-D", "warnings"])
    run(["cargo", "test", "--workspace"])
    check_api(targets)
    assert_same_artifact(extract(pins, targets, directory), GENERATED.read_bytes())
    assert_import_closure(VERIFICATION)
    run(["lake", "build", "FastSszVerification"], cwd=VERIFICATION)
    validate_dependencies(pins)
    check_proof_targets(targets, directory)
    check_rejection_guards(directory)
    print(f"Verified implemented slice: {len(targets)} codec functions. This is NOT full SSZ conformance.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("bootstrap", "extract", "check"))
    arguments = parser.parse_args()
    pins = load_pins()
    validate_pins(pins)
    if arguments.command == "bootstrap":
        bootstrap(pins)
        return
    targets = load_targets()
    with tempfile.TemporaryDirectory(prefix="fast-ssz-verify-") as temporary:
        directory = Path(temporary)
        if arguments.command == "extract":
            validate_tools(pins)
            GENERATED.write_bytes(extract(pins, targets, directory))
        else:
            check(pins, targets, directory)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"verification failed: {error}", file=sys.stderr)
        sys.exit(1)
