#!/usr/bin/env python3
"""Verify explicitly selected families of immutable official SSZ test vectors."""

import argparse
import errno
import hashlib
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
OFFICIAL = "https://github.com/ethereum/consensus-spec-tests"
SUBTREE = "tests/general/phase0/ssz_generic"
MANIFEST = ROOT / "tools" / "official-vectors" / "Cargo.toml"
MAX_FILE_BYTES = 64 * 1024 * 1024


def source_reference(pins):
    source = pins["test_vectors"]
    repository, revision, path = (source.get(key) for key in ("repository", "revision", "path"))
    manifest = source.get("manifest_sha256")
    if (repository != OFFICIAL or path != SUBTREE or not isinstance(revision, str)
            or not re.fullmatch(r"[0-9a-f]{40}", revision) or not isinstance(manifest, str)
            or not re.fullmatch(r"[0-9a-f]{64}", manifest)):
        raise ValueError("official vectors require canonical sources and immutable revision/manifest pins")
    return repository, revision, path


def cache_directory(pins):
    _, revision, _ = source_reference(pins)
    cache = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    if not cache.is_absolute():
        raise ValueError("XDG_CACHE_HOME must be absolute")
    return cache / "nyx-ssz" / "official-vectors" / revision


def git_output(directory, *arguments):
    # Inspect raw objects without running cache-local hooks or fsmonitor.
    return subprocess.run(["git", "--no-replace-objects", "-c", "core.fsmonitor=false",
                           "-c", f"core.hooksPath={os.devnull}", "-C", str(directory), *arguments],
                          check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout


def tree_entries(relative, entries):
    result = {}
    prefix = PurePosixPath(relative)
    for entry in entries.removesuffix("\0").split("\0"):
        header, separator, name = entry.partition("\t")
        fields = header.split()
        if (not separator or len(fields) != 3 or fields[:2] != ["100644", "blob"]
                or not re.fullmatch(r"[0-9a-f]{40}", fields[2])):
            raise ValueError("official vectors must contain regular Git blobs")
        path = PurePosixPath(name)
        if (not path.is_relative_to(prefix) or path == prefix or ".." in path.parts
                or path.as_posix() != name or not re.fullmatch(r"[A-Za-z0-9_./-]+", name)):
            raise ValueError("Git tree path is outside the pinned vector subtree")
        if name in result:
            raise ValueError("duplicate official vector path")
        result[name] = fields[2]
    return result


def manifest_digest(relative, entries):
    """Authenticate the inventory independently of mutable local Git object storage."""
    expected = tree_entries(relative, entries)
    records = (f"100644 blob {expected[name]}\t{name}\0".encode("ascii") for name in sorted(expected))
    return hashlib.sha256(b"".join(records)).hexdigest()


def verify_tree(directory, relative, entries):
    expected = tree_entries(relative, entries)
    root = directory
    for part in PurePosixPath(relative).parts:
        root = root / part
        if root.is_symlink():
            raise ValueError("official vector cache contains a symlink")
    prefix = PurePosixPath(relative)
    expected_directories = {str(parent) for name in expected for parent in PurePosixPath(name).parents
                            if parent != prefix and parent.is_relative_to(prefix)}
    actual, directories = set(), set()
    for path in root.rglob("*"):
        if path.is_symlink():
            raise ValueError("official vector cache contains a symlink")
        if path.is_file():
            actual.add(path.relative_to(directory).as_posix())
        elif path.is_dir():
            directories.add(path.relative_to(directory).as_posix())
        else:
            raise ValueError("official vectors require regular files")
    if actual != expected.keys() or directories != expected_directories:
        raise ValueError("official vector file inventory differs from the pinned tree")
    for name, expected_digest in expected.items():
        path = directory / name
        if path.stat().st_size > MAX_FILE_BYTES:
            raise ValueError("official vector exceeds the fixture size limit")
        with path.open("rb") as source:
            data = source.read(MAX_FILE_BYTES + 1)
        if len(data) > MAX_FILE_BYTES:
            raise ValueError("official vector exceeds the fixture size limit")
        digest = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if digest != expected_digest:
            raise ValueError("official vector content differs from the pinned tree")


def verify_checkout(pins, directory):
    repository, revision, relative = source_reference(pins)
    head = git_output(directory, "rev-parse", "HEAD").strip()
    origin = git_output(directory, "remote", "get-url", "origin").strip()
    # Worktree commands such as status can execute cache-local clean filters.
    # Actual file inventory and raw blob checks below supersede index cleanliness.
    if (head, origin) != (revision, repository):
        raise ValueError("official vector cache is modified or at the wrong source revision")
    entries = git_output(directory, "ls-tree", "-r", "-z", revision, "--", relative)
    if manifest_digest(relative, entries) != pins["test_vectors"]["manifest_sha256"]:
        raise ValueError("official vector manifest differs from the independently pinned inventory")
    verify_tree(directory, relative, entries)
    return directory / relative


def prepare_raw_checkout(directory):
    """Materialize pinned blobs, never host-specific filters or text conversions."""
    attributes = directory / ".git" / "info" / "attributes"
    attributes.parent.mkdir(parents=True, exist_ok=True)
    attributes.write_text("* -filter -text -ident -working-tree-encoding\n", encoding="ascii")


def ensure_checkout(pins):
    repository, revision, relative = source_reference(pins)
    directory = cache_directory(pins)
    if directory.exists():
        return verify_checkout(pins, directory)
    directory.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".official-vectors-", dir=directory.parent) as temporary:
        checkout = Path(temporary) / "checkout"
        subprocess.run(["git", "clone", "--filter=blob:none", "--no-checkout", "--depth", "1",
                        repository, str(checkout)], check=True)
        prepare_raw_checkout(checkout)
        git_output(checkout, "sparse-checkout", "set", "--cone", relative)
        git_output(checkout, "fetch", "--depth", "1", "origin", revision)
        git_output(checkout, "checkout", "--detach", revision)
        verify_checkout(pins, checkout)
        try:
            checkout.rename(directory)
        except OSError as error:
            if error.errno not in (errno.EEXIST, errno.ENOTEMPTY):
                raise
            return verify_checkout(pins, directory)
    return directory / relative


def check(pins, families):
    directory = ensure_checkout(pins)
    available = sorted(path.name for path in directory.iterdir() if path.is_dir())
    selected = list(families) if families else available
    if not selected or len(set(selected)) != len(selected) or set(selected) - set(available):
        raise ValueError("families must be a nonempty distinct selection from the pinned corpus")
    for arguments in (["fmt", "--manifest-path", str(MANIFEST), "--", "--check"],
                      ["clippy", "--locked", "--manifest-path", str(MANIFEST), "--all-targets", "--", "-D", "warnings"],
                      ["test", "--locked", "--manifest-path", str(MANIFEST)],
                      ["run", "--locked", "--manifest-path", str(MANIFEST), "--", str(directory), *selected]):
        subprocess.run(["cargo", *arguments], cwd=ROOT, check=True)
    remaining = sorted(set(available) - set(selected))
    if remaining:
        print(f"Official vector slice only; remaining families: {', '.join(remaining)}. NOT full conformance.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("setup", "check"))
    parser.add_argument("--family", action="append", default=[])
    arguments = parser.parse_args()
    if arguments.command == "setup" and arguments.family:
        parser.error("family selection is valid only for check")
    with (ROOT / "sources.lock").open("rb") as source:
        pins = tomllib.load(source)
    if arguments.command == "setup":
        ensure_checkout(pins)
        print(f"Pinned official vector cache verified at {source_reference(pins)[1]}.")
    else:
        check(pins, arguments.family)


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(f"official vector tool failed (exit {error.returncode})", file=sys.stderr)
        sys.exit(1)
    except (OSError, ValueError, KeyError) as error:
        message = str(error) if isinstance(error, ValueError) else "official vector configuration or cache unavailable"
        print(f"official vector verification failed: {message}", file=sys.stderr)
        sys.exit(1)
