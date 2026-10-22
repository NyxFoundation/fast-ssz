"""Proof gate regressions."""
import json
from pathlib import Path
import subprocess
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

    def test_should_preserve_aeneas_bodies_and_select_the_prepared_sysroot(self):
        body = (
            "  massert (¬ (rhs = 0#usize))\n"
            "  let d ← Usize.div self rhs\n"
            "  let r ← Usize.rem self rhs\n"
            "  if r > 0#usize\n"
            "  then ok (Std.Usize.wrapping_add d 1#usize)\n"
            "  else ok d\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory)
            (destination / "NyxSsz.lean").write_text(body)
            (destination / "nyx_ssz.llbc").write_text('{"translated": {}}')
            with patch.object(verify, "check_api", return_value=set()), \
                 patch.object(verify, "tool_path", side_effect=lambda tool, _: tool), \
                 patch.object(verify, "miri_sysroot", return_value=destination) as sysroot, \
                 patch.object(verify, "prepare_native_macros", create=True) as native, \
                 patch.object(verify, "run") as run, \
                 patch.object(verify, "assert_safe_drops") as ownership, \
                 patch.object(verify, "split_model", return_value={"Core.lean": body}) as partition:
                result = verify.extract({"extraction": {"transparent_items": []}}, [], destination, [])
            partition.assert_called_once_with(body)
            ownership.assert_called_once_with({"translated": {}})
            sysroot.assert_called_once()
            native.assert_called_once_with(destination / "cargo")
            charon = run.call_args_list[0].args[0]
            self.assertEqual(charon[charon.index("--sysroot") + 1], destination)
            self.assertIn("--start-from-attribute=verify::start_from", charon)
            self.assertIn("--precise-drops", charon)
            self.assertIn("-checks", run.call_args_list[1].args[0])
            self.assertEqual(charon[charon.index("--features") + 1], "verification")
            self.assertEqual(charon[charon.index("--target-dir") + 1], destination / "cargo")
            self.assertEqual(result, {"Core.lean": body.encode("utf-8")})

    def test_should_prepare_miri_using_the_pinned_rust_toolchain(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(verify, "run", return_value=directory + "\n") as run:
                self.assertEqual(verify.miri_sysroot(verify.load_pins()), Path(directory))
            run.assert_called_once_with(
                ["cargo", "+" + verify.load_pins()["tools"]["rust_toolchain"],
                 "miri", "setup", "--print-sysroot"], capture=True,
            )

    def test_should_fail_closed_when_miri_is_unavailable(self):
        error = subprocess.CalledProcessError(1, ["cargo", "miri", "setup"])
        with patch.object(verify, "run", side_effect=error) as run:
            with self.assertRaises(subprocess.CalledProcessError):
                verify.miri_sysroot(verify.load_pins())
            self.assertEqual(run.call_count, 1)

    def test_should_reject_missing_or_relative_miri_sysroots(self):
        for output in ("", "relative/sysroot", "/missing-nyx-ssz-miri-sysroot"):
            with self.subTest(output=output), patch.object(verify, "run", return_value=output):
                with self.assertRaisesRegex(ValueError, "Miri sysroot"):
                    verify.miri_sysroot(verify.load_pins())

    def test_should_prebuild_only_host_proc_macros_from_locked_metadata(self):
        packages = [
            {"id": "registry+https://github.com/rust-lang/crates.io-index#library@1.0", "name": "library", "version": "1.0", "targets": [{"kind": ["lib"]}]},
            {"id": "registry+https://github.com/rust-lang/crates.io-index#derive@1.0", "name": "derive", "version": "1.0", "targets": [{"kind": ["proc-macro"]}]},
        ]
        with patch.object(verify, "run", side_effect=[json.dumps({"packages": packages}), None]) as run:
            verify.prepare_native_macros(Path("target"))
        self.assertEqual(run.call_count, 2)
        self.assertEqual(run.call_args.args[0], [
            "cargo", "build", "--locked", "--target-dir", Path("target"),
            "--package", "derive@1.0",
        ])

    def test_should_skip_host_build_when_no_proc_macros_are_present(self):
        with patch.object(verify, "run", return_value=json.dumps({"packages": []})) as run:
            verify.prepare_native_macros(Path("target"))
        run.assert_called_once_with(
            ["cargo", "metadata", "--locked", "--format-version", "1"], capture=True,
        )

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

    def test_should_register_all_owned_byte_methods_and_real_extracted_dictionaries(self):
        targets = verify.load_targets()
        contracts = verify.load_contracts(verify.VERIFICATION / "traits.json")
        artifacts = {path: data.decode("utf-8")
                     for path, data in verify.generated_artifacts().items()}
        byte_targets = [target for target in targets
                        if target["rust"].startswith("nyx_ssz::bytecollections::")]
        self.assertEqual({target["rust"] for target in byte_targets}, {
            f"nyx_ssz::bytecollections::{kind}::{method}"
            for kind in ("ByteVector", "ByteList")
            for method in ("from_bytes", "as_bytes")
        })
        verify.assert_extracted_targets(artifacts, targets)
        verify.assert_extracted_instances(artifacts, contracts)
        path = "NyxSszRust/Bytecollections.lean"
        body = artifacts[path]
        for target in byte_targets:
            name = target["lean"].removeprefix("NyxSszRust.")
            with self.subTest(method=name), self.assertRaisesRegex(ValueError, "not extracted"):
                verify.assert_extracted_targets(
                    {**artifacts, path: body.replace(f"def {name}\n", f"axiom {name}\n")}, targets)
        for kind in ("ByteVector", "ByteList"):
            name = f"bytecollections.{kind}.Insts.Nyx_sszCodecSszTuple"
            self.assertIn(f"def {name} (", body)
            with self.subTest(dictionary=name), self.assertRaisesRegex(ValueError, "inventory|ambiguous"):
                verify.assert_extracted_instances(
                    {**artifacts, path: body.replace(f"def {name} (", f"axiom {name} (")}, contracts)

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
