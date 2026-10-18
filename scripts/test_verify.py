"""Regression tests for proof coverage and stale-artifact rejection."""

import json
from pathlib import Path
import tempfile
import unittest

import verify


class VerificationGateTests(unittest.TestCase):
    def test_should_accept_identical_extraction_artifacts(self):
        verify.assert_same_artifact(b"generated", b"generated")

    def test_should_reject_stale_extraction_artifacts(self):
        with self.assertRaisesRegex(ValueError, "stale"):
            verify.assert_same_artifact(b"old", b"new")

    def test_should_extract_only_local_functions_from_rustdoc(self):
        document = {"paths": {
            "0": {"crate_id": 0, "kind": "function", "path": ["fast_ssz", "encode"]},
            "1": {"crate_id": 1, "kind": "function", "path": ["other", "encode"]},
            "2": {"crate_id": 0, "kind": "enum", "path": ["fast_ssz", "Error"]},
        }}
        self.assertEqual(verify.api_functions(document), {"fast_ssz::encode"})

    def test_should_reject_public_associated_functions_without_coverage(self):
        document = {"paths": {}, "index": {
            "0": {"crate_id": 0, "visibility": "public", "inner": {"function": {}}},
        }}
        with self.assertRaisesRegex(ValueError, "associated functions"):
            verify.api_functions(document)

    def test_should_reject_public_traits_without_coverage(self):
        document = {"paths": {}, "index": {
            "0": {"crate_id": 0, "visibility": "public", "inner": {"trait": {}}},
        }}
        with self.assertRaisesRegex(ValueError, "public traits"):
            verify.api_functions(document)

    def test_should_reject_unregistered_public_functions(self):
        with self.assertRaisesRegex(ValueError, "missing=.*decode"):
            verify.assert_api_covered({"fast_ssz::encode", "fast_ssz::decode"}, [
                {"rust": "fast_ssz::encode"},
            ])

    def test_should_reject_registry_entries_for_removed_functions(self):
        with self.assertRaisesRegex(ValueError, "stale=.*encode"):
            verify.assert_api_covered(set(), [{"rust": "fast_ssz::encode"}])

    def test_should_accept_exact_api_coverage(self):
        verify.assert_api_covered({"fast_ssz::encode"}, [{"rust": "fast_ssz::encode"}])

    def test_should_reject_duplicate_targets(self):
        entry = {"rust": "fast_ssz::encode", "lean": "Rust.encode", "proof": "Proof.encode"}
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "targets.json"
            path.write_text(json.dumps([entry, entry]))
            with self.assertRaisesRegex(ValueError, "duplicate"):
                verify.load_targets(path)

    def test_should_reject_empty_targets(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "targets.json"
            path.write_text("[]")
            with self.assertRaisesRegex(ValueError, "nonempty"):
                verify.load_targets(path)

    def test_should_reject_invalid_lean_identifiers(self):
        entry = {"rust": "fast_ssz::encode", "lean": "Rust.encode\naxiom", "proof": "Proof.encode"}
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "targets.json"
            path.write_text(json.dumps([entry]))
            with self.assertRaisesRegex(ValueError, "identifier"):
                verify.load_targets(path)

    def test_should_reject_proof_files_outside_the_audit_import_closure(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "FastSszVerification").mkdir()
            (root / "FastSszVerification/Audit.lean").write_text("import FastSszRust\n")
            (root / "FastSszRust.lean").write_text("import Aeneas\n")
            (root / "Unimported.lean").write_text("namespace Hidden\nend Hidden\n")
            with self.assertRaisesRegex(ValueError, "Unimported"):
                verify.assert_import_closure(root)

    def test_should_accept_the_complete_audit_import_closure(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "FastSszVerification").mkdir()
            (root / "FastSszVerification/Audit.lean").write_text("import FastSszRust\n")
            (root / "FastSszRust.lean").write_text("import Aeneas\n")
            (root / ".lake").mkdir()
            (root / ".lake/IgnoredDependency.lean").write_text("import Other\n")
            verify.assert_import_closure(root)


if __name__ == "__main__":
    unittest.main()
