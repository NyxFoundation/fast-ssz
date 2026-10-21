"""Test exact primitive observations for the current Progressive-list oracle."""

from functools import partial
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock

from reference_oracle import basic_list_case, bitlist_case, generate, invalid_aliases, fixture_blob


class ProgressiveOracleTests(unittest.TestCase):
    def fixture(self, root, primitive, value):
        case = root / "basic_progressive_list/valid" / f"proglist_{primitive}_max_0"
        case.mkdir(parents=True, exist_ok=True)
        (case / "value.yaml").write_text(value)
        (case / "meta.yaml").write_text("root: '0x" + "00" * 32 + "'\n")
        (case / "serialized.ssz_snappy").write_bytes(b"\x00")
        (root / "basic_progressive_list/invalid").mkdir(exist_ok=True)
        return case

    def test_should_preserve_unsigned_width_and_boolean_observations_when_building_wire_values(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for primitive, value, encoded in [
                    ("bool", "[true, false]", b"\x01\x00"),
                    ("uint16", "[258, 772]", b"\x02\x01\x04\x03"),
                    ("uint256", "['" + str(2 ** 256 - 1) + "']", bytes([255]) * 32)]:
                case = self.fixture(root, primitive, value)
                decoded = Mock()
                decoded.encode_bytes.return_value = encoded
                decoded.hash_tree_root.return_value = bytes([17]) * 32
                decoder = Mock(return_value=decoded)
                record = basic_list_case(case, {primitive: decoder})
                decoder.assert_called_once_with(encoded)
                self.assertEqual(record["root"], "0x" + "11" * 32)

    def test_should_reject_ambiguous_or_out_of_range_primitive_values(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for primitive, value in [("bool", "[1]"), ("uint8", "[true]"),
                                     ("uint8", "[256]"), ("uint8", "[-1]"),
                                     ("uint8", "[1.0]"), ("uint8", "['not-an-int']"),
                                     ("uint17", "[0]"), ("uint8", "[[1]]")]:
                case = self.fixture(root, primitive, value)
                with self.assertRaises(ValueError, msg=f"{primitive}:{value}"):
                    basic_list_case(case, {primitive: Mock()})

    def test_should_link_mislabeled_cases_only_to_same_type_byte_identical_valid_witnesses(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            valid = self.fixture(root, "uint16", "[]")
            directory = root / "basic_progressive_list/invalid"
            for name, wire in [("proglist_uint16_0_bad", b"\x00"),
                               ("proglist_uint32_0_bad", b"\x00"),
                               ("proglist_uint16_1_bad", b"\x01")]:
                case = directory / name
                case.mkdir()
                (case / "serialized.ssz_snappy").write_bytes(wire)
            aliases = invalid_aliases(root)
            self.assertEqual(aliases, {"basic_progressive_list/invalid/proglist_uint16_0_bad":
                             {"witness": "basic_progressive_list/valid/" + valid.name}})
            value = Mock()
            value.encode_bytes.return_value = b""
            value.hash_tree_root.return_value = bytes(32)
            handlers = {"basic_progressive_list": partial(basic_list_case,
                decoders={"uint16": Mock(return_value=value)})}
            result = generate(root, "a" * 40, "b" * 40, handlers)
            self.assertEqual(len(result["roots"]), 2)
            self.assertEqual(result["format_version"], 2)
            linked = root / "linked"
            linked.mkdir()
            (linked / "serialized.ssz_snappy").symlink_to(valid / "serialized.ssz_snappy")
            with self.assertRaises(ValueError):
                fixture_blob(linked)

    def test_should_generate_only_explicitly_selected_families(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.fixture(root, "uint8", "[]")
            value = Mock()
            value.encode_bytes.return_value = b""
            value.hash_tree_root.return_value = bytes(32)
            handlers = {"basic_progressive_list": partial(basic_list_case,
                decoders={"uint8": Mock(return_value=value)})}
            result = generate(root, "a" * 40, "b" * 40, handlers)
            self.assertEqual(list(result["roots"]),
                             ["basic_progressive_list/valid/proglist_uint8_max_0"])
            with self.assertRaises(ValueError):
                generate(root, "a" * 40, "b" * 40, {})
            with self.assertRaises(ValueError):
                generate(root, "a" * 40, "b" * 40, {"unknown": bitlist_case})


if __name__ == "__main__":
    unittest.main()
