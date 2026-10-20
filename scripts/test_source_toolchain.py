"""The extractor must be built from exactly the pinned, public source."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import verify


class SourceToolchainTests(unittest.TestCase):
    def test_should_build_the_pinned_standalone_extractor_without_bundling_charon(self):
        pins = verify.load_pins()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "aeneas"
            target = root / "package" / "bin" / "aeneas"
            target.parent.mkdir(parents=True)
            target.write_text("extractor")
            with patch.object(verify, "tool_directory", return_value=root), patch.object(verify, "run") as run:
                verify.bootstrap_aeneas(pins)
                verify.bootstrap_aeneas(pins)
            self.assertTrue(binary.is_symlink())
            self.assertEqual(binary.readlink(), Path("package/bin/aeneas"))
            self.assertEqual(run.call_count, 2)
            self.assertEqual(run.call_args.args[0], [
                "nix", "--extra-experimental-features", "nix-command flakes", "build",
                verify.aeneas_source_reference(pins), "--out-link", root / "package",
            ])

    def test_should_reject_invalid_or_unpinned_source_references(self):
        pins = verify.load_pins()
        self.assertTrue(verify.aeneas_source_reference(pins).endswith("#aeneas-standalone"))
        for key, value in (("aeneas_repository", "https://example.com/repository"),
                           ("aeneas_revision", "main")):
            tools = {**pins["tools"], key: value}
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "pinned GitHub source"):
                verify.aeneas_source_reference({**pins, "tools": tools})

    def test_should_reject_tool_versions_that_escape_the_cache_directory(self):
        pins = verify.load_pins()
        for version in ("../other", "/absolute", "", 1):
            tools = {**pins["tools"], "aeneas_version": version}
            with self.subTest(version=version), self.assertRaisesRegex(ValueError, "invalid tool version"):
                verify.tool_directory("aeneas", {**pins, "tools": tools})

    def test_should_fail_closed_when_the_build_does_not_produce_an_extractor(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(verify, "tool_directory", return_value=Path(directory)), \
                 patch.object(verify, "run"):
                with self.assertRaisesRegex(ValueError, "did not produce"):
                    verify.bootstrap_aeneas(verify.load_pins())

    def test_should_not_replace_an_unrelated_cached_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "aeneas").write_text("unrelated")
            target = root / "package" / "bin" / "aeneas"
            target.parent.mkdir(parents=True)
            target.write_text("extractor")
            with patch.object(verify, "tool_directory", return_value=root), patch.object(verify, "run"):
                with self.assertRaisesRegex(ValueError, "cache entry"):
                    verify.bootstrap_aeneas(verify.load_pins())
            self.assertEqual((root / "aeneas").read_text(), "unrelated")


if __name__ == "__main__":
    unittest.main()
