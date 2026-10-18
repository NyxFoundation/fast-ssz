"""Generated Lean layout must preserve declarations and dependency order."""
import unittest
from extracted_modules import split_model

HEADER = "-- GENERATED\nimport Aeneas\nnamespace FastSszRust\n\n"
FOOTER = "\nend FastSszRust\n"


def source(*declarations):
    return HEADER + "\n".join(declarations) + FOOTER


def declaration(module, body):
    return f"/-- [fast_ssz::{module}::item] -/\n{body}\n"


class ExtractedModuleTests(unittest.TestCase):
    def test_should_preserve_generated_declarations_verbatim(self):
        scalar = declaration("scalar", "def scalar.item := 1")
        sha = declaration("sha256", "def sha256.item := 2")
        result = split_model(source(scalar, sha))
        self.assertIn(scalar, result["FastSszRust/Scalar.lean"])
        self.assertIn(sha, result["FastSszRust/Sha256.lean"])
        self.assertNotIn(sha, result["FastSszRust/Scalar.lean"])
        self.assertIn("import FastSszRust.Sha256", result["FastSszRust.lean"])

    def test_should_import_dependencies_before_dependent_modules(self):
        result = split_model(source(
            declaration("merkle", "def merkle.item := sha256.item"),
            declaration("sha256", "def sha256.item := 2"),
        ))
        self.assertIn("import FastSszRust.Sha256", result["FastSszRust/Merkle.lean"])
        root = result["FastSszRust.lean"]
        self.assertLess(root.index(".Sha256"), root.index(".Merkle"))

    def test_should_keep_each_modules_original_declaration_order(self):
        first = declaration("sha256", "def sha256.first := 1")
        second = declaration("sha256", "def sha256.second := sha256.first")
        result = split_model(source(first, declaration("scalar", "def scalar.x := 0"), second))
        generated = result["FastSszRust/Sha256.lean"]
        self.assertLess(generated.index(first), generated.index(second))

    def test_should_canonicalize_independent_declaration_order(self):
        first = declaration("sha256", "def sha256.a := 1")
        second = declaration("sha256", "def sha256.b := 2")
        a = split_model(source(first, second))["FastSszRust/Sha256.lean"]
        b = split_model(source(second, declaration("other", "def other.x := 3"), first))
        self.assertEqual(a, b["FastSszRust/Sha256.lean"])

    def test_should_order_types_before_constructor_references(self):
        constructor = declaration("merkle", "def merkle.a := merkle.Z.Bad")
        kind = declaration("merkle", "inductive merkle.Z where\n| Bad : merkle.Z")
        model = split_model(source(constructor, kind))["FastSszRust/Merkle.lean"]
        self.assertLess(model.index("inductive merkle.Z"), model.index("def merkle.a"))

    def test_should_reject_duplicate_generated_names(self):
        unit = declaration("scalar", "def scalar.item := 0")
        with self.assertRaisesRegex(ValueError, "duplicate"):
            split_model(source(unit, unit))

    def test_should_partition_transparent_foreign_crates(self):
        foreign = "/-- [ruint::Uint] -/\nstructure ruint.Uint where\n  value : Nat\n"
        own = declaration("scalar", "def scalar.item (x : ruint.Uint) := x.value")
        result = split_model(source(own, foreign))
        self.assertIn(foreign, result["FastSszRust/Ruint.lean"])
        self.assertIn("import FastSszRust.Ruint", result["FastSszRust/Scalar.lean"])

    def test_should_distinguish_std_names_from_extracted_core_definitions(self):
        core = "/-- [core::num::{usize}::div_ceil] -/\ndef core.num.Usize.div_ceil := 0\n"
        sha = declaration("sha256", "def sha256.item := core.num.U64.MAX")
        ruint = "/-- [ruint::nlimbs] -/\ndef ruint.nlimbs := core.num.Usize.div_ceil\n"
        result = split_model(source(core, sha, ruint))
        self.assertNotIn("import FastSszRust.Core", result["FastSszRust/Sha256.lean"])
        self.assertIn("import FastSszRust.Core", result["FastSszRust/Ruint.lean"])

    def test_should_normalize_only_registry_source_locations(self):
        template = ("/-- [ruint::Uint]\n"
                    "    Source: '{home}/registry/src/index.crates.io-123/ruint-1.20.1/src/lib.rs', lines 1:0-2:0 -/\n"
                    "structure ruint.Uint where\n  value : Nat\n")
        first = split_model(source(template.format(home="/one/cargo")))
        second = split_model(source(template.format(home="/different/cache")))
        self.assertEqual(first, second)
        self.assertIn("cargo-registry/ruint-1.20.1/src/lib.rs", first["FastSszRust/Ruint.lean"])

    def test_should_reject_foreign_axioms_instead_of_partitioning_them(self):
        with self.assertRaisesRegex(ValueError, "unclassified"):
            split_model(source("/-- [ruint::Uint] -/\naxiom ruint.Uint : Type\n"))

    def test_should_preserve_mutual_blocks_within_one_module(self):
        block = "mutual\n" + declaration("tree", "def tree.a := tree.b")
        block += declaration("tree", "def tree.b := tree.a") + "end\n"
        result = split_model(source(block))
        self.assertIn(block, result["FastSszRust/Tree.lean"])

    def test_should_reject_unterminated_or_cross_module_mutual_blocks(self):
        with self.assertRaisesRegex(ValueError, "unterminated"):
            split_model(source("mutual\n" + declaration("tree", "def tree.a := 0")))
        block = "mutual\n" + declaration("one", "def one.a := two.b")
        block += declaration("two", "def two.b := one.a") + "end\n"
        with self.assertRaisesRegex(ValueError, "cross-module"):
            split_model(source(block))

    def test_should_ignore_strings_and_comments_when_discovering_dependencies(self):
        result = split_model(source(
            declaration("one", 'def one.a := "two.b"'),
            declaration("two", "def two.b := one.a"),
        ))
        self.assertNotIn("import FastSszRust.Two", result["FastSszRust/One.lean"])

    def test_should_reject_unrecognized_layout_instead_of_dropping_code(self):
        with self.assertRaises(ValueError):
            split_model("unrecognized Lean output")
        with self.assertRaises(ValueError):
            split_model(source("def unclassified := 1"))

    def test_should_reject_dependency_cycles(self):
        with self.assertRaisesRegex(ValueError, "cycle"):
            split_model(source(
                declaration("one", "def one.item := two.item"),
                declaration("two", "def two.item := one.item"),
            ))

    def test_should_reject_colliding_module_file_names(self):
        with self.assertRaisesRegex(ValueError, "collision"):
            split_model(source(
                declaration("one_two", "def one_two.item := 1"),
                declaration("one__two", "def one__two.item := 2"),
            ))


if __name__ == "__main__":
    unittest.main()
