"""Test regenerated-root metadata pairing without trusting a replacement cache."""

from functools import partial
import json
from pathlib import Path
import sys
from types import ModuleType, SimpleNamespace
import tempfile
import unittest
from unittest.mock import Mock, patch

import reference_oracle

from reference_oracle import bitlist_case, generate, read_text

REVISION = "a" * 40
CORPUS = "b" * 40


def fixture(directory):
    case = directory / "progressive_bitlist/valid/progbitlist_max_1_0"
    case.mkdir(parents=True)
    (case / "value.yaml").write_text("'0x03'\n")
    (case / "meta.yaml").write_text("root: '0x" + "00" * 32 + "'\n")
    return case


def decoder():
    decoded = Mock()
    decoded.encode_bytes.return_value = b"\x03"
    decoded.hash_tree_root.return_value = bytes([17]) * 32
    return Mock(return_value=decoded)


def handlers(decode):
    return {"progressive_bitlist": partial(bitlist_case, decoder=decode)}


class ReferenceOracleTests(unittest.TestCase):
    def test_should_preserve_the_published_root_and_identify_both_source_revisions(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            fixture(root)
            decode = decoder()
            result = generate(root, REVISION, CORPUS, handlers(decode))
            decode.assert_called_once_with(b"\x03")
            self.assertEqual(result["reference_revision"], REVISION)
            self.assertEqual(result["corpus_revision"], CORPUS)
            value = result["roots"]["progressive_bitlist/valid/progbitlist_max_1_0"]
            self.assertEqual(value, {"source_root": "0x" + "00" * 32, "root": "0x" + "11" * 32})

    def test_should_reject_changed_wire_values_or_invalid_reference_roots(self):
        with tempfile.TemporaryDirectory() as temporary:
            case = fixture(Path(temporary))
            decode = decoder()
            decode.return_value.encode_bytes.return_value = b"\x02"
            with self.assertRaisesRegex(ValueError, "changes the fixture wire"):
                bitlist_case(case, decode)
            decode.return_value.encode_bytes.return_value = b"\x03"
            decode.return_value.hash_tree_root.return_value = b"short"
            with self.assertRaisesRegex(ValueError, "invalid root"):
                bitlist_case(case, decode)

    def test_should_reject_noncanonical_metadata_and_mutable_revision_names(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            case = fixture(root)
            (case / "value.yaml").write_text("!!python/object malicious\n")
            with self.assertRaises(ValueError):
                bitlist_case(case, decoder())
            with self.assertRaises(ValueError):
                generate(root, "main", CORPUS, handlers(decoder()))
            (case.parent / "unexpected").write_text("not a case")
            (case / "value.yaml").write_text("'0x03'\n")
            with self.assertRaises(ValueError):
                generate(root, REVISION, CORPUS, handlers(decoder()))

    def test_should_write_explicit_revisioned_metadata_from_the_selected_decoder(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            fixture(root)
            output = root / "generated.json"
            package = ModuleType("remerkleable")
            module = ModuleType("remerkleable.progressive")
            module.ProgressiveBitlist = SimpleNamespace(decode_bytes=decoder())
            arguments = ["oracle", str(root / "verified"), str(root), str(output), REVISION, CORPUS,
                         "progressive_bitlist"]
            with patch.object(sys, "argv", arguments), patch.object(sys, "path", sys.path.copy()), \
                    patch.dict(sys.modules, {"remerkleable": package, "remerkleable.progressive": module}), \
                    patch("builtins.print") as printed:
                reference_oracle.main()
            self.assertEqual(json.loads(output.read_text())["reference_revision"], REVISION)
            self.assertIn("1 differ", printed.call_args.args[0])
        with patch.object(sys, "argv", ["oracle"]), self.assertRaises(ValueError):
            reference_oracle.main()

    def test_should_refuse_empty_selections_symlinks_and_oversized_metadata(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / "progressive_bitlist/valid"
            directory.mkdir(parents=True)
            with self.assertRaisesRegex(ValueError, "empty"):
                generate(root, REVISION, CORPUS, handlers(decoder()))
            target = root / "data"
            target.write_bytes(b"safe")
            link = root / "linked"
            link.symlink_to(target)
            with self.assertRaises(ValueError):
                read_text(link)
            target.write_bytes(bytes(1024 * 1024 + 1))
            with self.assertRaises(ValueError):
                read_text(target)


if __name__ == "__main__":
    unittest.main()
