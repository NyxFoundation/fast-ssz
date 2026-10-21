"""Test authenticated source caching and isolated oracle invocation."""

import hashlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import reference_vectors as reference

REVISION = "2f0baeef0082d4278acaef7d822deb7009d7db7e"
DATA = b"pinned source fixture"
PINS = {"test_vectors": {"reference_repository": reference.OFFICIAL_REFERENCE,
        "reference_revision": REVISION, "reference_archive_sha256": hashlib.sha256(DATA).hexdigest(),
        "revision": "b" * 40}}


class ReferenceSourceFlowTests(unittest.TestCase):
    def test_should_cache_only_an_authenticated_download_and_reuse_identical_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "cache/source.tar.gz"
            with patch.object(reference, "archive_path", return_value=path), \
                    patch.object(reference.urllib.request, "urlopen", return_value=io.BytesIO(DATA)):
                self.assertEqual(reference.source_archive(PINS), DATA)
                self.assertEqual(path.read_bytes(), DATA)
            with patch.object(reference, "archive_path", return_value=path), \
                    patch.object(reference.urllib.request, "urlopen", side_effect=AssertionError("network")):
                self.assertEqual(reference.source_archive(PINS), DATA)

    def test_should_reject_an_unauthenticated_download_without_installing_it(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "cache/source.tar.gz"
            with patch.object(reference, "archive_path", return_value=path), \
                    patch.object(reference.urllib.request, "urlopen", return_value=io.BytesIO(b"wrong")):
                with self.assertRaisesRegex(ValueError, "digest"):
                    reference.source_archive(PINS)
            self.assertFalse(path.exists())

    def test_should_validate_a_concurrent_installation_instead_of_overwriting_it(self):
        def installed_first(_source, destination):
            Path(destination).write_bytes(DATA)
            raise FileExistsError("concurrent writer")
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "source.tar.gz"
            with patch.object(reference, "archive_path", return_value=path), \
                    patch.object(reference.urllib.request, "urlopen", return_value=io.BytesIO(DATA)), \
                    patch.object(reference.os, "link", side_effect=installed_first):
                self.assertEqual(reference.source_archive(PINS), DATA)

    def test_should_reject_symlinked_archives_before_reading_them(self):
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary) / "target"
            target.write_bytes(DATA)
            path = Path(temporary) / "source.tar.gz"
            path.symlink_to(target)
            with patch.object(reference, "archive_path", return_value=path), self.assertRaises(ValueError):
                reference.source_archive(PINS)

    def test_should_run_the_oracle_in_an_isolated_process_only_for_selected_progressive_roots(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with patch.object(reference, "source_archive", return_value=DATA), \
                    patch.object(reference, "extract_reference", return_value=root / "verified"), \
                    patch.object(reference.subprocess, "run", return_value=None) as run:
                self.assertIsNone(reference.regenerate(PINS, root, ["boolean"], root))
                run.assert_not_called()
                self.assertEqual(reference.regenerate(PINS, root, ["progressive_bitlist"], root),
                                 root / "reference-roots.json")
                self.assertEqual(run.call_args.args[0][1:3], ["-I", "-B"])
                self.assertEqual(run.call_args.args[0][-3:], [REVISION, "b" * 40, "progressive_bitlist"])

    def test_should_reject_invalid_archive_structure(self):
        with tempfile.TemporaryDirectory() as temporary, self.assertRaises(ValueError):
            reference.extract_reference(b"not a gzip archive", REVISION, Path(temporary))


if __name__ == "__main__":
    unittest.main()
