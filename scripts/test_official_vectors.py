"""Exercise pinned-vector provenance and fail-closed fixture integrity checks."""

import hashlib
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from official_vectors import cache_directory, source_reference, verify_tree

REVISION = "bc5c1a7fb2a8871aaffd4b16ee4dd9c72bb81908"
SOURCE = {
    "repository": "https://github.com/ethereum/consensus-spec-tests",
    "revision": REVISION,
    "path": "tests/general/phase0/ssz_generic",
    "manifest_sha256": "0" * 64,
}


def tree_entry(path, data):
    digest = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    return f"100644 blob {digest}\t{path}\0"


class OfficialVectorTests(unittest.TestCase):
    def test_should_accept_only_the_official_immutable_source(self):
        self.assertEqual(source_reference({"test_vectors": SOURCE}),
                         tuple(SOURCE[key] for key in ("repository", "revision", "path")))
        for key, value in (("revision", "main"), ("repository", "https://example.com/vectors"),
                           ("path", "../outside"), ("manifest_sha256", "main")):
            with self.subTest(key=key), self.assertRaises(ValueError):
                source_reference({"test_vectors": {**SOURCE, key: value}})

    def test_should_use_a_revision_specific_absolute_cache_directory(self):
        with patch.dict(os.environ, {"XDG_CACHE_HOME": "/tmp/vector-cache"}):
            self.assertEqual(cache_directory({"test_vectors": SOURCE}),
                             Path("/tmp/vector-cache/nyx-ssz/official-vectors") / REVISION)
        with patch.dict(os.environ, {"XDG_CACHE_HOME": "relative"}), self.assertRaises(ValueError):
            cache_directory({"test_vectors": SOURCE})

    def test_should_verify_actual_bytes_not_only_git_status(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory)
            relative = f"{SOURCE['path']}/boolean/valid/true/value.yaml"
            file = checkout / relative
            file.parent.mkdir(parents=True)
            file.write_bytes(b"true\n")
            entries = tree_entry(relative, b"true\n")
            verify_tree(checkout, SOURCE["path"], entries)
            file.write_bytes(b"false\n")
            with self.assertRaisesRegex(ValueError, "content differs"):
                verify_tree(checkout, SOURCE["path"], entries)

    def test_should_reject_extra_files_and_symlinks(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory)
            relative = f"{SOURCE['path']}/boolean/valid/true/value.yaml"
            file = checkout / relative
            file.parent.mkdir(parents=True)
            file.write_bytes(b"true\n")
            entries = tree_entry(relative, b"true\n")
            extra = file.parent / "unexpected.yaml"
            extra.write_bytes(b"true\n")
            with self.assertRaisesRegex(ValueError, "file inventory"):
                verify_tree(checkout, SOURCE["path"], entries)
            extra.unlink()
            extra.symlink_to(file)
            with self.assertRaisesRegex(ValueError, "symlink"):
                verify_tree(checkout, SOURCE["path"], entries)

    def test_should_reject_extra_empty_directories(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory)
            relative = f"{SOURCE['path']}/boolean/valid/true/value.yaml"
            file = checkout / relative
            file.parent.mkdir(parents=True)
            file.write_bytes(b"true\n")
            (file.parent / "unexpected").mkdir()
            with self.assertRaisesRegex(ValueError, "file inventory"):
                verify_tree(checkout, SOURCE["path"], tree_entry(relative, b"true\n"))

    def test_should_reject_missing_files_or_unexpected_git_modes(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout = Path(directory)
            relative = f"{SOURCE['path']}/boolean/valid/true/value.yaml"
            (checkout / relative).parent.mkdir(parents=True)
            entries = tree_entry(relative, b"true\n")
            with self.assertRaises(ValueError):
                verify_tree(checkout, SOURCE["path"], entries)
            with self.assertRaisesRegex(ValueError, "regular"):
                verify_tree(checkout, SOURCE["path"], entries.replace("100644", "120000"))

    def test_should_reject_git_tree_paths_outside_the_pinned_subtree(self):
        with tempfile.TemporaryDirectory() as directory, self.assertRaises(ValueError):
            verify_tree(Path(directory), SOURCE["path"], tree_entry("../outside", b"true\n"))


if __name__ == "__main__":
    unittest.main()
