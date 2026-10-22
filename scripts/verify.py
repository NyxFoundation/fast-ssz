#!/usr/bin/env python3
"""Check the implemented SSZ proof slice, not full conformance."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib
from extracted_modules import NAMESPACE, declared_names, split_model
from llbc_drops import assert_safe_drops
from generic_contract_fixtures import generic_contract_success, generic_rejection_cases
from native_output_fixtures import native_output_success, native_output_rejection_cases
from trait_contracts import load_contracts, validate_traits, assert_extracted_instances

ROOT = Path(__file__).resolve().parents[1]
VERIFICATION = ROOT / "verification"
GENERATED = VERIFICATION / "NyxSszRust.lean"
GENERATED_MODULES = VERIFICATION / "NyxSszRust"


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
        raise ValueError("nonempty targets required")
    for target in targets:
        if not isinstance(target, dict):
            raise ValueError("target must be an object")
        for field, separator in (("rust", "::"), ("lean", "."), ("proof", ".")):
            if not isinstance(target.get(field), str):
                raise ValueError(f"target {field} must be a string")
            parts = target[field].split(separator)
            if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", part) for part in parts):
                raise ValueError(f"invalid {field} identifier")
    if len({target["rust"] for target in targets}) != len(targets):
        raise ValueError("duplicate targets")
    return targets


def tool_directory(tool, pins):
    version = pins["tools"][f"{tool}_version"]
    if not isinstance(version, str) or not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", version):
        raise ValueError("invalid tool version")
    cache = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    return cache / "hax" / "tools" / tool / version


def tool_path(tool, pins):
    binary = tool_directory(tool, pins) / tool
    if not binary.is_file():
        raise ValueError(f"{tool} unavailable; run verify.py bootstrap")
    return binary


def validate_pins(pins):
    tools = pins["tools"]
    transparent = pins["extraction"]["transparent_items"]
    if not isinstance(transparent, list) or not all(isinstance(item, str) and item for item in transparent):
        raise ValueError("invalid transparent extraction items")
    with (ROOT / "rust-toolchain.toml").open("rb") as source:
        rust = tomllib.load(source)["toolchain"]["channel"]
    with (ROOT / "hax.toml").open("rb") as source:
        hax = tomllib.load(source)
    lean = (VERIFICATION / "lean-toolchain").read_text().strip()
    if rust != tools["rust_toolchain"] or lean != tools["lean_toolchain"]:
        raise ValueError("toolchain differs from sources.lock")
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


def aeneas_source_reference(pins):
    tools = pins["tools"]
    url, revision = tools["aeneas_repository"], tools["aeneas_revision"]
    if not isinstance(url, str) or not isinstance(revision, str):
        raise ValueError("Aeneas requires an immutable pinned GitHub source")
    repository = re.fullmatch(r"https://github\.com/([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+)", url)
    if repository is None or not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Aeneas requires an immutable pinned GitHub source")
    return f"github:{repository[1]}/{revision}#aeneas-standalone"


def bootstrap_aeneas(pins):
    directory = tool_directory("aeneas", pins)
    directory.mkdir(parents=True, exist_ok=True)
    binary = directory / "aeneas"
    link = Path("package/bin/aeneas")
    if ((binary.is_symlink() and binary.readlink() != link)
            or (binary.exists() and not binary.is_symlink())):
        raise ValueError("Aeneas cache entry conflicts with the pinned source build")
    run(["nix", "--extra-experimental-features", "nix-command flakes", "build",
         aeneas_source_reference(pins), "--out-link", directory / "package"])
    if not (directory / link).is_file():
        raise ValueError("Nix did not produce the pinned Aeneas executable")
    if not binary.is_symlink():
        binary.symlink_to(link)


def bootstrap(pins):
    version = run(["cargo", "hax", "--version"], capture=True).splitlines()
    if f"version={pins['tools']['cargo_hax_version']}" not in version:
        raise ValueError("install cargo-hax from sources.lock")
    run(["cargo", "hax", "tools", "install", f"charon@{pins['tools']['charon_version']}"])
    bootstrap_aeneas(pins)
    validate_tools(pins)
    miri_sysroot(pins)
    run(["lake", "exe", "cache", "get"], cwd=VERIFICATION)
    run(["lake", "build", "Aeneas", "Ssz"], cwd=VERIFICATION)
    validate_dependencies(pins)


def assert_extracted_targets(artifacts, targets):
    definitions = {f"{NAMESPACE}.{name}" for source in artifacts.values()
                   for name in declared_names(source)}
    missing = sorted({target["lean"] for target in targets} - definitions)
    if missing:
        raise ValueError(f"registered operations were not extracted: {missing}")


def extract(pins, targets, destination, contracts):
    methods = check_api(targets, contracts)
    llbc = destination / "nyx_ssz.llbc"
    arguments = [tool_path("charon", pins), "cargo", "--preset=aeneas", "--precise-drops",
                 "--start-from-attribute=verify::start_from", "--sysroot", miri_sysroot(pins)]
    for item in pins["extraction"]["transparent_items"]:
        arguments.extend(["--include", item])
    # Explicit method paths are unsupported by pinned Charon. Selected methods
    # use declaration-only entry attributes; other methods need real call graphs.
    # Exact coverage still requires a concrete body for every registered method.
    for target in targets:
        if target["rust"] not in methods:
            arguments.extend(["--start-from", target["rust"]])
    for module in sorted({module for contract in contracts for module in contract["modules"]}):
        arguments.extend(["--start-from", module])
    arguments.extend([
        "--dest-file", llbc, "--", "--lib", "--manifest-path", "crates/nyx-ssz/Cargo.toml",
        "--features", "verification", "--target-dir", destination / "cargo",
    ])
    prepare_native_macros(destination / "cargo")
    run(arguments)
    assert_safe_drops(json.loads(llbc.read_text(encoding="utf-8")))
    run([
        tool_path("aeneas", pins), "-backend", "lean", "-namespace", "NyxSszRust",
        "-checks", "-abort-on-error", "-warnings-as-errors", "-no-progress-bar",
        "-dest", destination, llbc,
    ])
    source = (destination / "NyxSsz.lean").read_text(encoding="utf-8")
    artifacts = split_model(source)
    assert_extracted_targets(artifacts, targets)
    assert_extracted_instances(artifacts, contracts)
    return {path: content.encode("utf-8") for path, content in artifacts.items()}


def miri_sysroot(pins):
    """Prepare the pinned standard-library MIR; never use a different sysroot."""
    output = run([
        "cargo", f"+{pins['tools']['rust_toolchain']}", "miri", "setup", "--print-sysroot",
    ], capture=True).strip()
    directory = Path(output)
    if not output or not directory.is_absolute() or not directory.is_dir():
        raise ValueError("Miri sysroot unavailable; run verify.py bootstrap")
    return directory


def prepare_native_macros(target):
    """Build host executables with the normal sysroot, before MIR extraction."""
    metadata = json.loads(run([
        "cargo", "metadata", "--locked", "--format-version", "1",
    ], capture=True))
    packages = [f"{package['name']}@{package['version']}" for package in metadata["packages"]
                if any("proc-macro" in item["kind"] for item in package["targets"])]
    if not packages:
        return
    arguments = ["cargo", "build", "--locked", "--target-dir", target]
    for package in packages:
        arguments.extend(["--package", package])
    run(arguments)


def generated_artifacts():
    paths = list(GENERATED_MODULES.rglob("*.lean"))
    if GENERATED.is_file():
        paths.append(GENERATED)
    return {path.relative_to(VERIFICATION).as_posix(): path.read_bytes() for path in paths}


def write_artifacts(artifacts):
    obsolete = set(generated_artifacts()) - artifacts.keys()
    if obsolete:
        raise ValueError(f"obsolete generated modules need explicit removal: {sorted(obsolete)}")
    for relative, content in artifacts.items():
        path = VERIFICATION / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)


def assert_same_artifact(actual, expected):
    if actual != expected:
        raise ValueError("stale extraction; run verify.py extract and review")


def inherent_method_paths(document):
    index = document.get("index", {})
    methods = {}
    for item in index.values():
        implementation = item["inner"].get("impl")
        if item["crate_id"] != 0 or not implementation or implementation.get("trait") is not None:
            continue
        reference = implementation.get("for", {}).get("resolved_path", {})
        owner = document["paths"].get(str(reference.get("id")))
        if not owner or owner["crate_id"] != 0:
            continue
        for identifier in implementation["items"]:
            method = index.get(str(identifier))
            if not method or method["crate_id"] != 0 or method["visibility"] != "public":
                continue
            if "function" not in method["inner"]:
                continue
            path = "::".join([*owner["path"], method["name"]])
            if path in methods.values():
                raise ValueError("ambiguous associated function path")
            methods[str(identifier)] = path
    return methods


def api_functions(document, contracts=()):
    reserved = validate_traits(document, contracts)
    methods = inherent_method_paths(document)
    for identifier, item in document.get("index", {}).items():
        if item["crate_id"] != 0 or item["visibility"] != "public":
            continue
        if ("function" in item["inner"] and identifier not in document["paths"]
                and identifier not in methods and identifier not in reserved):
            raise ValueError("public associated function has no discoverable type path")
    return {
        "::".join(item["path"])
        for identifier, item in document["paths"].items()
        if item["crate_id"] == 0 and item["kind"] == "function" and identifier not in reserved
    } | set(methods.values())


def assert_api_covered(functions, targets):
    registered = {target["rust"] for target in targets}
    if functions != registered:
        missing = sorted(functions - registered)
        stale = sorted(registered - functions)
        raise ValueError(f"API/extraction coverage differs; missing={missing}, stale={stale}")


def check_api(targets, contracts):
    directory = ROOT / "target" / "api-coverage"
    run([
        "cargo", "rustdoc", "--lib", "--package", "nyx-ssz", "--target-dir", directory,
        "--", "--output-format", "json", "-Z", "unstable-options",
    ])
    document = json.loads((directory / "doc" / "nyx_ssz.json").read_text())
    assert_api_covered(api_functions(document, contracts), targets)
    return set(inherent_method_paths(document).values())


def assert_import_closure(directory):
    modules = {
        ".".join(path.relative_to(directory).with_suffix("").parts): path
        for path in directory.rglob("*.lean")
        if not any(part.startswith(".") or part == "extraction" for part in path.relative_to(directory).parts)
    }
    visited = set()
    pending = ["NyxSszVerification.Audit"]
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


def check_proof_targets(targets, contracts, directory):
    lines = ["import NyxSszVerification.Audit"]
    lines.extend(f"check_refinement {target['lean']} via {target['proof']}" for target in targets)
    lines.extend(f"check_trait_contract {instance['lean']} against {contract['law']} via {instance['proof']}"
                 for contract in contracts for instance in contract["instances"])
    file = directory / "CheckTargets.lean"
    file.write_text("\n".join(lines) + "\n")
    run(["lake", "env", "lean", file], cwd=VERIFICATION)


def rejection_cases():
    return {
        "ForbiddenAxiom": (
            "namespace NyxSszVerification\naxiom forbidden : False\nend NyxSszVerification\n"
            "audit_nyx_ssz\n",
            "forbidden axiom",
        ),
        "NativeEvaluation": (
            "namespace NyxSszVerification\n"
            "theorem nativeResult : (List.range 100).length = 100 := by native_decide\n"
            "end NyxSszVerification\naudit_nyx_ssz\n",
            "forbidden axiom",
        ),
        "UnrelatedTheorem": (
            "check_refinement NyxSszRust.scalar.encode_bool via "
            "NyxSszVerification.decode_bool_refines\n",
            "does not mention",
        ),
        **trait_rejection_cases(),
        **generic_rejection_cases(),
        **native_output_rejection_cases(),
    }


def trait_rejection_cases():
    return {
        "UnrelatedTraitTheorem": (
            "check_trait_contract NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple "
            "against NyxSszVerification.CodecLaw via NyxSszVerification.encode_bool_refines\n",
            "registered trait contract",
        ),
        "VacuousTraitLaw": (
            "theorem reflexiveDictionary : NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple = "
            "NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple := rfl\n"
            "check_trait_contract NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple "
            "against Eq via reflexiveDictionary\n",
            "unsupported trait correctness law",
        ),
        "ConditionalTraitTheorem": (
            "theorem impossibleDictionary (h : False) : NyxSszVerification.CodecLaw "
            "NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple Ssz.Desc.bool Ssz.Value.bool := False.elim h\n"
            "check_trait_contract NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple "
            "against NyxSszVerification.CodecLaw via impossibleDictionary\n",
            "unconditional registered trait contract",
        ),
        "MismatchedTypeDeclaration": (
            "def misleadingBool : NyxSszRust.codec.Ssz Bool Unit := "
            "{ NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple with "
            "TYPE := Aeneas.Std.RustM.ok (NyxSszRust.type_info.TypeDescriptor.Uint 1) }\n"
            "example : NyxSszVerification.CodecLaw misleadingBool Ssz.Desc.bool Ssz.Value.bool := by\n"
            "  constructor\n  · rfl\n"
            "  · exact NyxSszVerification.bool_codec_refines.encode\n"
            "  · exact NyxSszVerification.bool_codec_refines.decode\n"
            "  · exact NyxSszVerification.bool_codec_refines.root\n",
            "Tactic `rfl` failed",
        ),
        "WrongTraitDictionary": (
            "check_trait_contract NyxSszRust.Bool.Insts.Nyx_sszCodecSszTuple "
            "against NyxSszVerification.CodecLaw via NyxSszVerification.u8_codec_refines\n",
            "wrong dictionary",
        ),
    }


def check_generic_contract_success(directory):
    file = directory / "GenericContractSuccess.lean"
    file.write_text("import NyxSszVerification.Audit\n" + generic_contract_success())
    run(["lake", "env", "lean", file], cwd=VERIFICATION)
    file = directory / "NativeOutputSuccess.lean"
    file.write_text("import NyxSszVerification.Audit\n" + native_output_success())
    run(["lake", "env", "lean", file], cwd=VERIFICATION)


def check_rejection_guards(directory):
    for label, (source, expected) in rejection_cases().items():
        file = directory / f"{label}.lean"
        file.write_text("import NyxSszVerification.Audit\n" + source)
        result = subprocess.run(
            ["lake", "env", "lean", str(file)], cwd=VERIFICATION,
            text=True, capture_output=True, check=False,
        )
        if result.returncode == 0 or expected not in result.stdout + result.stderr:
            raise ValueError(f"proof guard failed for {label}")


def check_ownership_examples(pins, directory):
    source = VERIFICATION / "fixtures" / "drop_bookkeeping.rs"
    cases = (("discard_bookkeeping", True), ("discard_nodes", True),
             ("discard_optional_bytes", True), ("discard_optional_user", False),
             ("discard_user_value", False))
    for function, accepted in cases:
        artifact = directory / f"{function}.llbc"
        run([tool_path("charon", pins), "rustc", "--preset=aeneas", "--precise-drops",
             "--sysroot", miri_sysroot(pins), "--start-from", f"nyx_drop_ownership::{function}",
             "--dest-file", artifact, "--", source, "--crate-name", "nyx_drop_ownership",
             "--crate-type", "lib"])
        try:
            assert_safe_drops(json.loads(artifact.read_text()))
        except ValueError as error:
            if accepted or "unmodeled normal-flow drop" not in str(error):
                raise
        else:
            if not accepted:
                raise ValueError("ownership guard accepted a user destructor")


def check(pins, targets, contracts, directory):
    validate_tools(pins)
    check_ownership_examples(pins, directory)
    run(["cargo", "fmt", "--all", "--", "--check"])
    run(["cargo", "clippy", "--workspace", "--all-targets", "--", "-D", "warnings"])
    run(["cargo", "test", "--workspace"])
    run([sys.executable, ROOT / "scripts" / "official_vectors.py", "check",
         "--family", "boolean", "--family", "uints", "--family", "basic_vector",
         "--family", "bitvector", "--family", "bitlist", "--family", "progressive_bitlist",
         "--family", "basic_progressive_list"])
    assert_same_artifact(extract(pins, targets, directory, contracts), generated_artifacts())
    assert_import_closure(VERIFICATION)
    run(["lake", "build", "NyxSszVerification"], cwd=VERIFICATION)
    run(["lake", "env", "lean", "--run", ROOT / "tools" / "multiproof-oracle.lean"], cwd=VERIFICATION)
    validate_dependencies(pins)
    check_proof_targets(targets, contracts, directory)
    check_generic_contract_success(directory)
    check_rejection_guards(directory)
    instances = sum(len(contract["instances"]) for contract in contracts)
    print(f"Verified slice: {len(targets)} registered operations and {instances} trait implementations. "
          "This is NOT full SSZ conformance.")


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
    contracts = load_contracts(VERIFICATION / "traits.json")
    with tempfile.TemporaryDirectory(prefix="nyx-ssz-verify-") as temporary:
        directory = Path(temporary)
        if arguments.command == "extract":
            validate_tools(pins)
            write_artifacts(extract(pins, targets, directory, contracts))
        else:
            check(pins, targets, contracts, directory)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"verification failed: {error}", file=sys.stderr)
        sys.exit(1)
