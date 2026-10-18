"""Proof gate regressions."""
import json
from pathlib import Path
import tempfile
import unittest
import verify

ENTRY = {"rust": "fast_ssz::encode", "lean": "Rust.encode", "proof": "Proof.encode"}


class VerificationGateTests(unittest.TestCase):
    def assert_invalid_targets(self, entries, message):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "targets.json"
            path.write_text(json.dumps(entries))
            with self.assertRaisesRegex(ValueError, message):
                verify.load_targets(path)

    def test_should_accept_identical_artifacts(self):
        verify.assert_same_artifact(b"generated", b"generated")

    def test_should_reject_stale_artifacts(self):
        with self.assertRaisesRegex(ValueError, "stale"):
            verify.assert_same_artifact(b"old", b"new")

    def test_should_discover_only_local_functions(self):
        items = [(0, "function"), (1, "function"), (0, "enum")]
        paths = {str(i): {"crate_id": c, "kind": k, "path": ["fast_ssz", "encode"]}
                 for i, (c, k) in enumerate(items)}
        self.assertEqual(verify.api_functions({"paths": paths}), {"fast_ssz::encode"})

    def test_should_reject_unhandled_associated_functions_and_traits(self):
        for kind in ("function", "trait"):
            item = {"crate_id": 0, "visibility": "public", "inner": {kind: {}}}
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                verify.api_functions({"paths": {}, "index": {"0": item}})

    def test_should_require_exact_api_coverage(self):
        verify.assert_api_covered({ENTRY["rust"]}, [ENTRY])
        for functions, message in ((set(), "stale"), ({"new"}, "missing")):
            with self.subTest(functions=functions), self.assertRaisesRegex(ValueError, message):
                verify.assert_api_covered(functions, [ENTRY])

    def test_should_reject_duplicate_empty_and_malformed_targets(self):
        for data, message in (([ENTRY, ENTRY], "duplicate"), ([], "nonempty"),
                              ([{**ENTRY, "lean": "Rust.encode\naxiom"}], "identifier"),
                              ([None], "object"), ([{}], "string")):
            with self.subTest(data=data):
                self.assert_invalid_targets(data, message)

    def test_should_require_every_lean_file_in_the_audit_closure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "FastSszVerification").mkdir()
            (root / "FastSszVerification/Audit.lean").write_text("import FastSszRust\n")
            (root / "FastSszRust.lean").write_text("import Aeneas\n")
            (root / ".lake").mkdir()
            (root / ".lake/Ignored.lean").write_text("import Other\n")
            verify.assert_import_closure(root)
            (root / "Hidden.lean").write_text("namespace Hidden\nend Hidden\n")
            with self.assertRaisesRegex(ValueError, "Hidden"):
                verify.assert_import_closure(root)


if __name__ == "__main__":
    unittest.main()
