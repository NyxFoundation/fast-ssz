"""Check immutable reference-oracle acquisition and extraction boundaries."""

import hashlib
import io
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from reference_vectors import extract_reference, reference_source, source_archive

REVISION = "2f0baeef0082d4278acaef7d822deb7009d7db7e"
ARCHIVE_HASH = "a25c10de302585649542dbbd61da1689959db7a57ac5cd4505a8ed795eee3feb"
PINS = {"test_vectors": {
    "reference_repository": "https://github.com/ethereum/remerkleable",
    "reference_revision": REVISION,
    "reference_archive_sha256": ARCHIVE_HASH,
}}


def archive(entries):
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w:gz") as output:
        for name, kind, contents in entries:
            member = tarfile.TarInfo(name)
            member.type = kind
            member.size = len(contents) if kind == tarfile.REGTYPE else 0
            output.addfile(member, io.BytesIO(contents) if member.size else None)
    return buffer.getvalue()


class ReferenceVectorTests(unittest.TestCase):
    def test_should_require_pinned_official_reference_sources(self):
        self.assertEqual(reference_source(PINS), (REVISION, ARCHIVE_HASH))
        for field, value in (("reference_repository", "https://example.com/oracle"),
                             ("reference_revision", "main"), ("reference_archive_sha256", "invalid")):
            with self.subTest(field=field), self.assertRaises(ValueError):
                reference_source({"test_vectors": {**PINS["test_vectors"], field: value}})

    def test_should_extract_only_regular_files_below_the_exact_reference_prefix(self):
        prefix = f"remerkleable-{REVISION}"
        data = archive([(f"{prefix}/remerkleable/progressive.py", tarfile.REGTYPE, b"verified\n")])
        with tempfile.TemporaryDirectory() as directory:
            root = extract_reference(data, REVISION, Path(directory))
            self.assertEqual((root / "remerkleable/progressive.py").read_bytes(), b"verified\n")

    def test_should_reject_traversal_links_and_duplicate_archive_paths(self):
        prefix = f"remerkleable-{REVISION}"
        normal = (f"{prefix}/remerkleable/progressive.py", tarfile.REGTYPE, b"verified\n")
        entries = [[(f"{prefix}/../outside", tarfile.REGTYPE, b"bad")],
                   [(f"{prefix}/linked", tarfile.SYMTYPE, b"")], [normal, normal]]
        for members in entries:
            with self.subTest(members=members), tempfile.TemporaryDirectory() as directory:
                with self.assertRaises(ValueError):
                    extract_reference(archive(members), REVISION, Path(directory))

    def test_should_authenticate_cached_reference_code_before_extracting_or_executing(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.tar.gz"
            data = b"authenticated archive bytes"
            path.write_bytes(data)
            pins = {"test_vectors": {**PINS["test_vectors"],
                    "reference_archive_sha256": hashlib.sha256(data).hexdigest()}}
            with patch("reference_vectors.archive_path", return_value=path):
                self.assertEqual(source_archive(pins), data)
                path.write_bytes(b"modified cache")
                with self.assertRaisesRegex(ValueError, "digest"):
                    source_archive(pins)


if __name__ == "__main__":
    unittest.main()
