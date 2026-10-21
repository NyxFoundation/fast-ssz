"""Exercise cache-local Git tampering against real temporary repositories."""

import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest
import zlib

import official_vectors as vectors


class VectorCacheSecurityTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.parent = Path(temporary.name)
        self.repository = self.parent / "repository"
        self.repository.mkdir()
        self.git("init", "--initial-branch", "fixture")
        self.git("remote", "add", "origin", vectors.OFFICIAL)
        self.file = self.repository / vectors.SUBTREE / "boolean/valid/true/value.yaml"
        self.file.parent.mkdir(parents=True)
        self.file.write_bytes(b"true\n")
        self.pinned = self.commit("pin true")
        entries = self.git("ls-tree", "-r", "-z", self.pinned, "--", vectors.SUBTREE)
        self.pins = {"test_vectors": {"repository": vectors.OFFICIAL,
                                     "revision": self.pinned, "path": vectors.SUBTREE,
                                     "manifest_sha256": vectors.manifest_digest(vectors.SUBTREE, entries)}}

    def git(self, *arguments):
        return subprocess.run(["git", "-C", str(self.repository), *arguments], check=True,
                              text=True, capture_output=True).stdout.strip()

    def commit(self, message):
        self.git("add", "--", str(self.file.relative_to(self.repository)))
        self.git("-c", "user.name=Fixture tests", "-c", "user.email=fixtures@example.invalid",
                 "-c", "commit.gpgsign=false", "commit", "-m", message)
        return self.git("rev-parse", "HEAD")

    def test_should_refuse_replacement_objects_even_when_head_and_status_appear_correct(self):
        self.file.write_bytes(b"false\n")
        substitute = self.commit("substitute false")
        self.git("replace", self.pinned, substitute)
        self.git("checkout", "--detach", self.pinned)
        self.assertEqual(self.git("rev-parse", "HEAD"), self.pinned)
        self.assertEqual(self.git("status", "--porcelain"), "")
        with self.assertRaises(ValueError):
            vectors.verify_checkout(self.pins, self.repository)

    def test_should_reject_a_corrupt_object_stored_under_the_pinned_commit_id(self):
        self.file.write_bytes(b"false\n")
        substitute = self.commit("substitute false")
        body = self.git("cat-file", "-p", substitute).encode() + b"\n"
        object_path = self.repository / ".git/objects" / self.pinned[:2] / self.pinned[2:]
        object_path.chmod(0o600)
        object_path.write_bytes(zlib.compress(b"commit " + str(len(body)).encode() + b"\0" + body))
        (self.repository / ".git/HEAD").write_text(self.pinned + "\n")
        self.assertEqual(self.git("rev-parse", "HEAD"), self.pinned)
        with self.assertRaises((ValueError, subprocess.CalledProcessError)):
            vectors.verify_checkout(self.pins, self.repository)

    def reject_corrupt_tree(self, path):
        suffix = f":{path}" if path else "^{tree}"
        original = self.git("rev-parse", self.pinned + suffix)
        self.file.write_bytes(b"false\n")
        substitute = self.commit("substitute false")
        replacement = self.git("rev-parse", substitute + suffix)
        body = subprocess.run(["git", "-C", str(self.repository), "cat-file", "tree", replacement],
                              check=True, capture_output=True).stdout
        object_path = self.repository / ".git/objects" / original[:2] / original[2:]
        object_path.chmod(0o600)
        object_path.write_bytes(zlib.compress(b"tree " + str(len(body)).encode() + b"\0" + body))
        (self.repository / ".git/HEAD").write_text(self.pinned + "\n")
        with self.assertRaises((ValueError, subprocess.CalledProcessError)):
            vectors.verify_checkout(self.pins, self.repository)

    def test_should_reject_corrupt_root_tree_objects(self):
        self.reject_corrupt_tree("")

    def test_should_reject_corrupt_nested_tree_objects(self):
        self.reject_corrupt_tree(vectors.SUBTREE)

    def test_should_not_execute_a_cache_local_fsmonitor_hook(self):
        marker = self.parent / "executed"
        hook = self.parent / "monitor.sh"
        hook.write_text(f"#!/bin/sh\nprintf ran > {shlex.quote(str(marker))}\nprintf 'token\\000/\\000'\n")
        hook.chmod(0o700)
        self.git("config", "core.fsmonitor", str(hook))
        self.assertEqual(vectors.verify_checkout(self.pins, self.repository),
                         self.repository / vectors.SUBTREE)
        self.assertFalse(marker.exists(), "cache-local executable hook must not run")

    def test_should_detect_modified_bytes_hidden_from_git_status(self):
        self.git("update-index", "--assume-unchanged", "--",
                 str(self.file.relative_to(self.repository)))
        self.file.write_bytes(b"false\n")
        self.assertEqual(self.git("status", "--porcelain"), "")
        with self.assertRaisesRegex(ValueError, "content differs"):
            vectors.verify_checkout(self.pins, self.repository)

    def test_should_materialize_raw_blobs_without_filters_or_line_ending_conversion(self):
        marker = self.parent / "smudged"
        filter_script = self.parent / "smudge.sh"
        filter_script.write_text(
            f"#!/bin/sh\nprintf ran > {shlex.quote(str(marker))}\nprintf 'converted\\r\\n'\n")
        filter_script.chmod(0o700)
        (self.repository / ".gitattributes").write_text("*.yaml filter=cache-probe text eol=crlf\n")
        self.git("config", "filter.cache-probe.smudge", str(filter_script))
        self.git("config", "filter.cache-probe.required", "true")
        vectors.prepare_raw_checkout(self.repository)
        self.git("checkout-index", "--force", "--", str(self.file.relative_to(self.repository)))
        self.assertEqual(self.file.read_bytes(), b"true\n")
        self.assertFalse(marker.exists(), "fresh checkout must disable host conversion filters")

    def test_should_not_execute_cache_local_clean_filters_during_verification(self):
        marker = self.parent / "filtered"
        filter_script = self.parent / "clean.sh"
        filter_script.write_text(
            f"#!/bin/sh\nprintf ran > {shlex.quote(str(marker))}\nprintf 'true\\n'\n")
        filter_script.chmod(0o700)
        attributes = self.repository / ".git/info/attributes"
        attributes.write_text("*.yaml filter=cache-probe\n")
        self.git("config", "filter.cache-probe.clean", str(filter_script))
        stamp = self.file.stat().st_mtime + 1
        os.utime(self.file, (stamp, stamp))
        self.assertEqual(vectors.verify_checkout(self.pins, self.repository),
                         self.repository / vectors.SUBTREE)
        self.assertFalse(marker.exists(), "cache-local clean filter must not run")


if __name__ == "__main__":
    unittest.main()
