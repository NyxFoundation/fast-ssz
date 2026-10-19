"""Proof gate regressions."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import verify

ENTRY = {"rust": "nyx_ssz::encode", "lean": "Rust.encode", "proof": "Proof.encode"}


class VerificationGateTests(unittest.TestCase):
    def assert_invalid_targets(self, entries, message):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "targets.json"
            path.write_text(json.dumps(entries))
            with self.assertRaisesRegex(ValueError, message):
                verify.load_targets(path)

    def test_should_normalize_only_the_miri_dependent_usize_division(self):
        unstable = "prefix\n" + verify.UNSTABLE_USIZE_DIVISION + "suffix\n"
        stable = "prefix\n" + verify.STABLE_USIZE_DIVISION + "suffix\n"
        self.assertEqual(verify.normalize_usize_division(unstable), stable)
        self.assertEqual(verify.normalize_usize_division(stable), stable)
        with self.assertRaisesRegex(ValueError, "unexpected"):
            verify.normalize_usize_division("let d ← Usize.div self rhs\n")
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            verify.normalize_usize_division(unstable + unstable)

    def test_should_accept_identical_artifacts(self):
        verify.assert_same_artifact(b"generated", b"generated")

    def test_should_reject_stale_artifacts(self):
        with self.assertRaisesRegex(ValueError, "stale"):
            verify.assert_same_artifact(b"old", b"new")

    def test_should_discover_only_local_functions(self):
        items = [(0, "function"), (1, "function"), (0, "enum")]
        paths = {str(i): {"crate_id": c, "kind": k, "path": ["nyx_ssz", "encode"]}
                 for i, (c, k) in enumerate(items)}
        self.assertEqual(verify.api_functions({"paths": paths}), {"nyx_ssz::encode"})

    def test_should_discover_public_inherent_methods_using_their_type_paths(self):
        document = {
            "paths": {"10": {"crate_id": 0, "kind": "struct",
                               "path": ["nyx_ssz", "bitfield", "BitListView"]}},
            "index": {
                "20": {"crate_id": 0, "visibility": "default", "inner": {"impl": {
                    "trait": None, "for": {"resolved_path": {"id": 10}}, "items": [30, 31]}}},
                "30": {"crate_id": 0, "visibility": "public", "name": "len_bits",
                       "inner": {"function": {}}},
                "31": {"crate_id": 0, "visibility": "default", "name": "private_helper",
                       "inner": {"function": {}}},
            },
        }
        methods = {"nyx_ssz::bitfield::BitListView::len_bits"}
        self.assertEqual(verify.api_functions(document), methods)
        with self.assertRaisesRegex(ValueError, "missing"):
            verify.assert_api_covered(verify.api_functions(document), [ENTRY])

    def test_should_reject_methods_without_a_discoverable_public_type(self):
        document = {
            "paths": {},
            "index": {
                "20": {"crate_id": 0, "visibility": "default", "inner": {"impl": {
                    "trait": None, "for": {"resolved_path": {"id": 10}}, "items": [30]}}},
                "30": {"crate_id": 0, "visibility": "public", "name": "len_bits",
                       "inner": {"function": {}}},
            },
        }
        with self.assertRaisesRegex(ValueError, "associated"):
            verify.api_functions(document)

    def test_should_reject_ambiguous_inherent_method_paths(self):
        document = {
            "paths": {"10": {"crate_id": 0, "kind": "struct", "path": ["nyx_ssz", "View"]}},
            "index": {
                "20": {"crate_id": 0, "visibility": "default", "inner": {"impl": {
                    "trait": None, "for": {"resolved_path": {"id": 10}}, "items": [30, 31]}}},
                "30": {"crate_id": 0, "visibility": "public", "name": "len",
                       "inner": {"function": {}}},
                "31": {"crate_id": 0, "visibility": "public", "name": "len",
                       "inner": {"function": {}}},
            },
        }
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            verify.api_functions(document)

    def test_should_reject_unknown_associated_functions_and_traits(self):
        for kind in ("function", "trait"):
            item = {"crate_id": 0, "visibility": "public", "inner": {kind: {}}}
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                verify.api_functions({"paths": {}, "index": {"0": item}})

    def test_should_require_concrete_extraction_of_every_registered_method(self):
        method = {"rust": "nyx_ssz::bitfield::BitListView::len_bits",
                  "lean": "NyxSszRust.bitfield.BitListView.len_bits",
                  "proof": "Proof.len_bits"}
        artifacts = {"Bitfield.lean": "def bitfield.BitListView.len_bits := value\n"}
        verify.assert_extracted_targets(artifacts, [method])
        for source in ("", "axiom bitfield.BitListView.len_bits : Nat\n"):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, "not extracted"):
                verify.assert_extracted_targets({"Bitfield.lean": source}, [method])

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

    def test_should_create_and_compare_the_complete_generated_module_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.multiple(verify, VERIFICATION=root, GENERATED=root / "NyxSszRust.lean",
                                GENERATED_MODULES=root / "NyxSszRust"):
                artifacts = {"NyxSszRust.lean": b"import NyxSszRust.One\n",
                             "NyxSszRust/One.lean": b"generated declarations\n"}
                verify.write_artifacts(artifacts)
                self.assertEqual(verify.generated_artifacts(), artifacts)
                with self.assertRaisesRegex(ValueError, "obsolete"):
                    verify.write_artifacts({"NyxSszRust.lean": b"changed"})
                self.assertEqual(verify.generated_artifacts(), artifacts)

    def test_should_require_every_lean_file_in_the_audit_closure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "NyxSszVerification").mkdir()
            (root / "NyxSszVerification/Audit.lean").write_text("import NyxSszRust\n")
            (root / "NyxSszRust.lean").write_text("import Aeneas\n")
            (root / ".lake").mkdir()
            (root / ".lake/Ignored.lean").write_text("import Other\n")
            verify.assert_import_closure(root)
            (root / "Hidden.lean").write_text("namespace Hidden\nend Hidden\n")
            with self.assertRaisesRegex(ValueError, "Hidden"):
                verify.assert_import_closure(root)


if __name__ == "__main__":
    unittest.main()
