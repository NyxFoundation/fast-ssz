"""Keep source-bound proof extraction and public aliases honest after migration."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import current_refinement as current
from historical_models import archive_omitted
import verify


class CryptoMigrationTests(unittest.TestCase):
    def aliases(self):
        return {
            "paths": {
                "1": {"kind": "function", "path": ["nyx_ssz", "multiproof", "helpers", "helper_indices"]},
                "2": {"kind": "module", "path": ["nyx_ssz", "multiproof"]},
            },
            "index": {
                "2": {"visibility": "public", "inner": {"module": {"items": [3]}}},
                "3": {"visibility": "public", "inner": {"use": {
                    "id": 1, "name": "helper_indices", "is_glob": False}}},
            },
        }

    def test_should_use_callable_public_paths_when_functions_are_reexported(self):
        self.assertEqual(verify.public_function_aliases(self.aliases()),
                         {"1": "nyx_ssz::multiproof::helper_indices"})

    def test_should_ignore_private_and_nonfunction_reexports(self):
        for change in ("owner", "import", "kind", "glob"):
            document = self.aliases()
            if change == "owner": document["index"]["2"]["visibility"] = "default"
            if change == "import": document["index"]["3"]["visibility"] = "default"
            if change == "kind": document["paths"]["1"]["kind"] = "enum"
            if change == "glob": document["index"]["3"]["inner"]["use"]["is_glob"] = True
            self.assertEqual(verify.public_function_aliases(document), {})

    def test_should_refuse_ambiguous_public_aliases(self):
        document = self.aliases()
        other = deepcopy(document["index"]["3"])
        other["inner"]["use"]["name"] = "another_name"
        document["index"]["4"] = other
        document["index"]["2"]["inner"]["module"]["items"].append(4)
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            verify.public_function_aliases(document)

    def test_should_preserve_omitted_declaration_bodies_without_counting_them_as_current(self):
        kept = "/-- [nyx_ssz::merkle::ProofError] -/\ninductive merkle.ProofError where\n| Invalid\n\n"
        omitted = "/-- [nyx_ssz::merkle::old_hash] -/\ndef merkle.old_hash := 123\n"
        source = "import Aeneas\nnamespace NyxSszRust\n" + kept + omitted + "\nend NyxSszRust\n"
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "Merkle.lean"
            path.write_text(source)
            archive_omitted(path, kept)
            historical = path.with_name("HistoricalMerkle.lean")
            archived = historical.read_text()
            self.assertIn(omitted, archived)
            self.assertNotIn(kept, archived)
            self.assertIn("import NyxSszRust.Merkle", archived)
            self.assertEqual(path.read_text(), source)
            historical.write_text(archived + "-- changed\n")
            with self.assertRaisesRegex(ValueError, "explicit review"):
                archive_omitted(path, kept)

    def test_should_refuse_stale_crypto_evidence_and_changed_backend_settings(self):
        scope = current.load_scope()
        current.check_crypto_evidence(scope)
        for key in ("rustcrypto_source_sha256", "rustcrypto_probe_lock_sha256"):
            invalid = {**scope, key: "0" * 64}
            with self.assertRaisesRegex(ValueError, "evidence changed"):
                current.check_crypto_evidence(invalid)
        with patch.object(current.tomllib, "loads", return_value={"dependencies": {"sha2": "=0.11.0"}}):
            with self.assertRaisesRegex(ValueError, "dependency changed"):
                current.check_crypto_evidence(scope)

    def test_should_bind_public_aliases_to_the_actual_extracted_source_files(self):
        document = self.aliases()
        document["paths"]["1"]["crate_id"] = 0
        document["paths"]["2"]["crate_id"] = 0
        document["index"]["1"] = {"inner": {}, "span": {
            "filename": "crates/nyx-ssz/src/multiproof/helpers.rs"}}
        document["paths"].update({
            "5": {"crate_id": 0, "kind": "enum", "path": ["nyx_ssz", "merkle", "error", "ProofError"]},
            "6": {"crate_id": 0, "kind": "module", "path": ["nyx_ssz", "merkle"]},
        })
        document["index"].update({
            "5": {"inner": {}, "span": {"filename": "crates/nyx-ssz/src/merkle/error.rs"}},
            "6": {"visibility": "public", "inner": {"module": {"items": [7]}}},
            "7": {"visibility": "public", "inner": {"use": {"id": 5, "name": "ProofError", "is_glob": False}}},
        })
        scope = {"proven": ["nyx_ssz::multiproof::helper_indices"]}
        current.check_source_bindings(document, scope)
        wrong_function = deepcopy(document)
        wrong_function["index"]["1"]["span"]["filename"] = "other.rs"
        with self.assertRaisesRegex(ValueError, "production source"):
            current.check_source_bindings(wrong_function, scope)
        wrong_type = deepcopy(document)
        wrong_type["paths"]["5"]["path"][-1] = "OtherError"
        with self.assertRaisesRegex(ValueError, "proof error"):
            current.check_source_bindings(wrong_type, scope)

    def test_should_require_all_six_crypto_skips_and_recorded_evidence(self):
        scope = current.load_scope()
        invalid = deepcopy(scope)
        invalid["rustcrypto_dependent_skips"].pop()
        with patch.object(Path, "read_text", return_value=json.dumps(invalid)):
            with self.assertRaisesRegex(ValueError, "explicit"):
                current.load_scope()
        for key in ("rustcrypto_source_sha256", "rustcrypto_probe_lock_sha256"):
            invalid = deepcopy(scope)
            invalid.pop(key)
            with patch.object(Path, "read_text", return_value=json.dumps(invalid)):
                with self.assertRaisesRegex(ValueError, "fingerprint"):
                    current.load_scope()


if __name__ == "__main__":
    unittest.main()
