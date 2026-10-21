"""Regenerate current-version roots with an authenticated official reference oracle."""

import hashlib
import io
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

OFFICIAL_REFERENCE = "https://github.com/ethereum/remerkleable"
MAX_ARCHIVE_BYTES = 4 * 1024 * 1024
MAX_SOURCE_BYTES = 16 * 1024 * 1024
MAX_MEMBERS = 1000
ORACLE = Path(__file__).with_name("reference_oracle.py")


def reference_source(pins):
    source = pins["test_vectors"]
    repository = source.get("reference_repository")
    revision = source.get("reference_revision")
    digest = source.get("reference_archive_sha256")
    if (repository != OFFICIAL_REFERENCE or not isinstance(revision, str)
            or not re.fullmatch(r"[0-9a-f]{40}", revision) or not isinstance(digest, str)
            or not re.fullmatch(r"[0-9a-f]{64}", digest)):
        raise ValueError("regenerated roots require immutable official reference/source-digest pins")
    return revision, digest


def archive_path(pins):
    revision, _ = reference_source(pins)
    cache = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    if not cache.is_absolute():
        raise ValueError("XDG_CACHE_HOME must be absolute")
    return cache / "nyx-ssz" / "reference-oracle" / revision / "source.tar.gz"


def authenticate(data, digest):
    if len(data) > MAX_ARCHIVE_BYTES or hashlib.sha256(data).hexdigest() != digest:
        raise ValueError("official reference archive digest or size differs from its pin")
    return data


def read_archive(path, digest):
    if path.is_symlink() or not path.is_file():
        raise ValueError("reference archive cache must be a regular file")
    with path.open("rb") as source:
        return authenticate(source.read(MAX_ARCHIVE_BYTES + 1), digest)


def source_archive(pins):
    revision, digest = reference_source(pins)
    path = archive_path(pins)
    if path.exists() or path.is_symlink():
        return read_archive(path, digest)
    url = f"https://codeload.github.com/ethereum/remerkleable/tar.gz/{revision}"
    request = urllib.request.Request(url, headers={"User-Agent": "nyx-ssz-vector-verification"})
    with urllib.request.urlopen(request, timeout=30) as response:
        data = authenticate(response.read(MAX_ARCHIVE_BYTES + 1), digest)
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(prefix=".reference-source-", dir=path.parent) as output:
        output.write(data)
        output.flush()
        os.fsync(output.fileno())
        try:
            os.link(output.name, path)
        except FileExistsError:
            return read_archive(path, digest)
    return data


def extract_members(archive, revision, directory):
    prefix = f"remerkleable-{revision}"
    seen, total = set(), 0
    for index, member in enumerate(archive):
        if index >= MAX_MEMBERS:
            raise ValueError("reference archive has too many entries")
        name = member.name.rstrip("/") if member.isdir() else member.name
        path = PurePosixPath(name)
        if (not path.parts or path.parts[0] != prefix or path.is_absolute()
                or ".." in path.parts or path.as_posix() != name or name in seen):
            raise ValueError("unsafe or duplicate reference archive path")
        seen.add(name)
        target = directory.joinpath(*path.parts)
        if member.isdir():
            target.mkdir(parents=True, exist_ok=True)
            continue
        if not member.isfile() or member.size < 0:
            raise ValueError("reference archive must contain only regular files and directories")
        total += member.size
        if total > MAX_SOURCE_BYTES:
            raise ValueError("reference source exceeds its size limit")
        source = archive.extractfile(member)
        if source is None:
            raise ValueError("reference archive entry has no contents")
        data = source.read(member.size + 1)
        if len(data) != member.size:
            raise ValueError("reference archive entry is truncated")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    root = directory / prefix
    if not (root / "remerkleable" / "progressive.py").is_file():
        raise ValueError("reference archive has no progressive implementation")
    return root


def extract_reference(data, revision, directory):
    try:
        with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
            return extract_members(archive, revision, directory)
    except tarfile.TarError:
        raise ValueError("invalid reference source archive") from None


def regenerate(pins, corpus, families, temporary):
    if "progressive_bitlist" not in families:
        return None
    revision, _ = reference_source(pins)
    source = extract_reference(source_archive(pins), revision, temporary / "reference")
    output = temporary / "reference-roots.json"
    subprocess.run([sys.executable, "-I", "-B", str(ORACLE), str(source), str(corpus), str(output),
                    revision, pins["test_vectors"]["revision"]], check=True, cwd=temporary)
    return output
