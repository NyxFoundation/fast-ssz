"""Test cache creation, provenance checks and explicit corpus selection without network access."""

import errno
import hashlib
from pathlib import Path
import shutil
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import official_vectors as vectors

REVISION = "bc5c1a7fb2a8871aaffd4b16ee4dd9c72bb81908"
RELATIVE = f"{vectors.SUBTREE}/boolean/valid/true/value.yaml"
DATA = b"true\n"
DIGEST = hashlib.sha1(b"blob 5\0" + DATA).hexdigest()
ENTRY = f"100644 blob {DIGEST}\t{RELATIVE}\0"
PINS = {"test_vectors": {"repository": vectors.OFFICIAL, "revision": REVISION, "path": vectors.SUBTREE,
                         "manifest_sha256": vectors.manifest_digest(vectors.SUBTREE, ENTRY)}}


def seed(directory):
    file = directory / RELATIVE
    file.parent.mkdir(parents=True)
    file.write_bytes(DATA)


def replies(_directory, *arguments):
    return {"rev-parse": REVISION, "remote": vectors.OFFICIAL,
            "status": "", "ls-tree": ENTRY}.get(arguments[0], "")


def clone(arguments, **_kwargs):
    seed(Path(arguments[-1]))
    return SimpleNamespace(stdout="")


class VectorCacheFlowTests(unittest.TestCase):
    def test_should_validate_source_revision_and_origin_before_reusing_a_cache(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            seed(directory)
            with patch.object(vectors, "git_output", side_effect=replies):
                self.assertEqual(vectors.verify_checkout(PINS, directory), directory / vectors.SUBTREE)
            for command, wrong in (("rev-parse", "0" * 40), ("remote", "https://example.com")):
                def response(path, *arguments):
                    return wrong if arguments[0] == command else replies(path, *arguments)
                with self.subTest(command=command), patch.object(vectors, "git_output", side_effect=response):
                    with self.assertRaisesRegex(ValueError, "wrong source revision"):
                        vectors.verify_checkout(PINS, directory)

    def test_should_create_an_atomic_cache_and_reuse_it_without_cloning_again(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "cache"
            with patch.object(vectors, "cache_directory", return_value=directory), \
                    patch.object(vectors, "git_output", side_effect=replies), \
                    patch.object(vectors.subprocess, "run", side_effect=clone):
                self.assertEqual(vectors.ensure_checkout(PINS), directory / vectors.SUBTREE)
                self.assertEqual((directory / RELATIVE).read_bytes(), DATA)
                with patch.object(vectors.subprocess, "run", side_effect=AssertionError("unexpected clone")):
                    self.assertEqual(vectors.ensure_checkout(PINS), directory / vectors.SUBTREE)

    def test_should_verify_the_winning_cache_when_another_process_installs_it_first(self):
        def concurrent_install(source, destination):
            shutil.copytree(source, destination)
            raise OSError(errno.ENOTEMPTY, "concurrent cache installation")
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "cache"
            with patch.object(vectors, "cache_directory", return_value=directory), \
                    patch.object(vectors, "git_output", side_effect=replies), \
                    patch.object(vectors.subprocess, "run", side_effect=clone), \
                    patch.object(Path, "rename", concurrent_install):
                self.assertEqual(vectors.ensure_checkout(PINS), directory / vectors.SUBTREE)

    def test_should_not_hide_cache_installation_errors(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "cache"
            with patch.object(vectors, "cache_directory", return_value=directory), \
                    patch.object(vectors, "git_output", side_effect=replies), \
                    patch.object(vectors.subprocess, "run", side_effect=clone), \
                    patch.object(Path, "rename", side_effect=PermissionError(errno.EACCES, "denied")):
                with self.assertRaises(PermissionError):
                    vectors.ensure_checkout(PINS)

    def test_should_request_the_complete_corpus_when_no_families_are_selected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in ("boolean", "uints", "containers"):
                (root / name).mkdir()
            with patch.object(vectors, "ensure_checkout", return_value=root), \
                    patch.object(vectors, "regenerate", return_value=None), \
                    patch.object(vectors.subprocess, "run", return_value=None) as run:
                vectors.check(PINS, [])
                self.assertEqual(run.call_args.args[0][-3:], ["boolean", "containers", "uints"])
                for selected in (["boolean", "boolean"], ["../outside"], ["unknown"]):
                    with self.assertRaises(ValueError):
                        vectors.check(PINS, selected)

    def test_should_forward_both_pins_and_the_fresh_reference_document_to_the_runner(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "progressive_bitlist").mkdir()
            with patch.object(vectors, "ensure_checkout", return_value=root), \
                    patch.object(vectors, "regenerate", return_value=root / "current.json"), \
                    patch.object(vectors, "reference_source", return_value=("a" * 40, "c" * 64)), \
                    patch.object(vectors.subprocess, "run", return_value=None) as run:
                vectors.check(PINS, ["progressive_bitlist"])
                arguments = run.call_args.args[0]
                self.assertEqual(arguments[-6:], ["--reference-roots", str(root / "current.json"),
                    "--reference-revision", "a" * 40, "--corpus-revision", REVISION])

    def test_should_report_unselected_families_explicitly(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "boolean").mkdir()
            (root / "uints").mkdir()
            with patch.object(vectors, "ensure_checkout", return_value=root), \
                    patch.object(vectors.subprocess, "run", return_value=None), \
                    patch("builtins.print") as output:
                vectors.check(PINS, ["boolean"])
                self.assertIn("NOT full conformance", output.call_args.args[0])
                self.assertIn("uints", output.call_args.args[0])

    def test_should_reject_empty_duplicate_or_malformed_git_tree_entries(self):
        for entries in ("", ENTRY + ENTRY, ENTRY.replace(" blob ", " tree "),
                        ENTRY.replace(DIGEST, "not-a-digest")):
            with self.subTest(entries=entries), self.assertRaises(ValueError):
                vectors.tree_entries(vectors.SUBTREE, entries)

    def test_should_return_git_output_without_using_a_shell(self):
        with patch.object(vectors.subprocess, "run", return_value=SimpleNamespace(stdout="pinned\n")) as run:
            self.assertEqual(vectors.git_output(Path("/tmp/cache"), "rev-parse", "HEAD"), "pinned\n")
            self.assertNotIn("shell", run.call_args.kwargs)


if __name__ == "__main__":
    unittest.main()
