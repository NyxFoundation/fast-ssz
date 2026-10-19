"""Trait declarations and all local instances require explicit proof coverage."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from trait_contracts import load_contracts, validate_traits, assert_extracted_instances

CONTRACT = {
    "rust": "nyx_ssz::codec::Ssz", "law": "NyxSszVerification.CodecLaw",
    "members": {"FIXED_SIZE": "assoc_const", "encode": "function"},
    "instances": [{"type": "bool", "lean": "NyxSszRust.Bool.Insts.Ssz",
                   "proof": "NyxSszVerification.bool_law"}],
}


def document():
    return {"paths": {"1": {"path": ["nyx_ssz", "codec", "Ssz"]}}, "index": {
        "1": {"crate_id": 0, "visibility": "public", "name": "Ssz",
              "inner": {"trait": {"items": [2, 3], "implementations": [4]}}},
        "2": {"name": "FIXED_SIZE", "inner": {"assoc_const": {}}},
        "3": {"name": "encode", "inner": {"function": {}}},
        "4": {"inner": {"impl": {"for": {"primitive": "bool"}, "items": [5, 6]}}},
        "5": {"name": "FIXED_SIZE", "inner": {"assoc_const": {}}},
        "6": {"name": "encode", "inner": {"function": {}}},
    }}


class TraitContractTests(unittest.TestCase):
    def load(self, value):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "traits.json"
            path.write_text(json.dumps(value))
            return load_contracts(path)

    def test_should_require_exact_declaration_and_instance_inventories(self):
        contracts = self.load([CONTRACT])
        self.assertEqual(validate_traits(document(), contracts), {"2", "3", "5", "6"})
        for mutation in ("trait", "member", "instance"):
            data = document()
            if mutation == "trait":
                contracts = []
            elif mutation == "member":
                data["index"]["3"]["name"] = "unregistered"
            else:
                data["index"]["4"]["inner"]["impl"]["for"] = {"primitive": "u8"}
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_traits(data, contracts)
            contracts = self.load([CONTRACT])

    def test_should_reject_duplicate_traits_instances_and_malformed_identifiers(self):
        duplicate_instance = copy.deepcopy(CONTRACT)
        duplicate_instance["instances"].append(duplicate_instance["instances"][0])
        malformed = {**CONTRACT, "law": "invalid\naxiom injected"}
        vacuous = {**CONTRACT, "law": "Eq"}
        for value in ([CONTRACT, CONTRACT], [duplicate_instance], [malformed], [vacuous], [{}], [None]):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.load(value)

    def test_should_reject_stale_contracts_for_removed_traits(self):
        with self.assertRaisesRegex(ValueError, "trait"):
            validate_traits({"paths": {}, "index": {}}, [CONTRACT])

    def test_should_require_the_exact_extracted_trait_dictionary_inventory(self):
        source = (
            "/-- Trait implementation: [nyx_ssz::codec::{impl nyx_ssz::codec::Ssz for bool}] -/\n"
            "def Bool.Insts.Ssz : codec.Ssz Bool := dictionary\n"
        )
        assert_extracted_instances({"Codec.lean": source}, [CONTRACT])
        for artifacts in ({}, {"Codec.lean": source.replace("Bool.Insts.Ssz", "U8.Insts.Ssz")}):
            with self.subTest(artifacts=artifacts), self.assertRaises(ValueError):
                assert_extracted_instances(artifacts, [CONTRACT])


if __name__ == "__main__":
    unittest.main()
