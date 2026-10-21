"""Normal-return ownership checks before Aeneas erases drop glue."""
import copy
import unittest
from llbc_drops import assert_safe_drops


U8 = {"Literal": {"UInt": "U8"}}
PARAMETER = {"Var": {"Free": 0}}


def named(name, local=True):
    return {"name": [{"Ident": [part, 0]} for part in name.split("::")], "is_local": local}


def vector(element):
    return {"Adt": {"id": 0, "builtin": None, "generics": {"types": [element]}}}


def fixture(ty, kind="Precise"):
    return {"has_errors": False, "translated": {
        "options": {"precise_drops": True, "desugar_drops": False},
        "type_decls": [{"def_id": 0, "item_meta": named("alloc::vec::Vec", False)}],
        "trait_decls": [{"def_id": 0, "item_meta": named("core::ops::drop::Drop", False)}],
        "trait_impls": [{"def_id": 0, "src": "Destruct"}],
        "fun_decls": [{"def_id": 0, "item_meta": named("nyx_ssz::decode"), "src": "Normal",
                       "body": {"Ok": {"Switch": {"Drop": {"kind": kind, "place": {"ty": ty}}}}}}],
    }}


def structure(fields, custom_drop=False, local=True):
    ty = {"Adt": {"id": 1, "builtin": None, "generics": {"types": []}}}
    document = fixture(ty)
    document["translated"]["type_decls"].append({
        "def_id": 1, "item_meta": {**named("nyx_ssz::Bookkeeping", local), "opacity": "Transparent"},
        "generics": {"types": [], "const_generics": [], "trait_clauses": []},
        "kind": {"Struct": [{"ty": field} for field in fields]},
    })
    if custom_drop:
        document["translated"]["trait_impls"].append({
            "def_id": 1, "src": "Normal", "impl_trait": {"id": 0, "generics": {"types": [ty]}}})
    return document


class DropGateTests(unittest.TestCase):
    def test_should_accept_closed_standard_containers_without_user_destructors(self):
        for ty in (U8, vector(U8), vector(vector(U8)), {"Ref": [None, PARAMETER, "Shared"]}):
            with self.subTest(ty=ty):
                assert_safe_drops(fixture(ty))

    def test_should_accept_current_llbc_array_nodes_when_elements_have_no_user_destructor(self):
        assert_safe_drops(fixture(vector({"Array": [U8, {"Literal": 32}]})))
        with self.assertRaisesRegex(ValueError, "unmodeled normal-flow drop"):
            assert_safe_drops(fixture(vector({"Array": [PARAMETER, {"Literal": 32}]})))

    def test_should_accept_local_closed_structures_when_their_fields_are_safe_and_drop_is_absent(self):
        assert_safe_drops(structure([{"Ref": [None, PARAMETER, "Shared"]}, vector(U8)]))
        for document in (structure([vector(U8)], custom_drop=True),
                         structure([vector(PARAMETER)]), structure([vector(U8)], local=False),
                         structure([{"Adt": {"id": 1, "builtin": None, "generics": {"types": []}}}])):
            with self.subTest(document=document), self.assertRaisesRegex(ValueError, "unmodeled normal-flow drop"):
                assert_safe_drops(document)

    def test_should_reject_dropping_generic_values_or_their_owned_containers(self):
        for ty in (PARAMETER, vector(PARAMETER), {"TraitType": []}, {"FutureType": None}):
            with self.subTest(ty=ty), self.assertRaisesRegex(ValueError, "unmodeled normal-flow drop"):
                assert_safe_drops(fixture(ty))

    def test_should_reject_unknown_concrete_types_that_might_have_custom_destructors(self):
        document = fixture({"Adt": {"id": 1, "builtin": None, "generics": {"types": []}}})
        document["translated"]["type_decls"].append({
            "def_id": 1, "item_meta": named("nyx_ssz::CustomDrop")})
        with self.assertRaisesRegex(ValueError, "unmodeled normal-flow drop"):
            assert_safe_drops(document)

    def test_should_require_precise_drops_and_successful_extraction(self):
        for key, value in (("precise_drops", False), ("has_errors", True)):
            document = fixture(U8)
            if key == "has_errors":
                document[key] = value
            else:
                document["translated"]["options"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                assert_safe_drops(document)

    def test_should_reject_conditional_drops_not_elaborated_by_charon(self):
        with self.assertRaisesRegex(ValueError, "precise"):
            assert_safe_drops(fixture(U8, "Conditional"))

    def test_should_exclude_unwinding_and_compiler_generated_destructor_bodies(self):
        document = fixture(vector(PARAMETER))
        function = document["translated"]["fun_decls"][0]
        function["src"] = {"TraitImpl": {"impl_ref": {"id": 0}}}
        assert_safe_drops(document)
        function["src"] = "Normal"
        function["body"] = {"Ok": {"Call": {
            "call": {"func": {"Builtin": "noop"}}, "on_unwind": function["body"]}}}
        assert_safe_drops(document)

    def test_should_resolve_hash_consed_types_without_rewriting_the_artifact(self):
        document = fixture({"Deduplicated": 7})
        document["types"] = {"HashConsedValue": [7, vector(U8)]}
        original = copy.deepcopy(document)
        assert_safe_drops(document)
        self.assertEqual(document, original)
        document["types"]["HashConsedValue"][1] = vector(PARAMETER)
        with self.assertRaisesRegex(ValueError, "unmodeled normal-flow drop"):
            assert_safe_drops(document)

    def test_should_reject_missing_conflicting_or_cyclic_type_references(self):
        for definition in (None, {"HashConsedValue": [7, {"Deduplicated": 7}]},
                           [{"HashConsedValue": [7, U8]}, {"HashConsedValue": [7, PARAMETER]}]):
            document = fixture({"Deduplicated": 7})
            document["types"] = definition
            with self.subTest(definition=definition), self.assertRaises(ValueError):
                assert_safe_drops(document)

    def test_should_reject_explicit_drop_and_forget_calls_even_when_imported_under_an_alias(self):
        for callee in ("core::mem::drop", "core::mem::forget"):
            document = fixture(U8)
            document["translated"]["fun_decls"].append({
                "def_id": 1, "item_meta": named(callee, False), "body": None, "src": "Normal"})
            document["translated"]["fun_decls"][0]["body"] = {"Ok": {"Call": {"call": {
                "func": {"Regular": {"kind": {"Fun": {"Regular": 1}}}}}}}}
            with self.subTest(callee=callee), self.assertRaisesRegex(ValueError, "explicit discard"):
                assert_safe_drops(document)


if __name__ == "__main__":
    unittest.main()
