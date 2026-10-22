#!/usr/bin/env python3
"""Generate/check native metadata fixtures using the actual pinned Lean executable.

This is differential test data, not an extraction or proof gate. It never edits
pins, specifications, models, or generated Lean. Small declarations exhaust the
chosen malformed layout/name/field products; targeted Rust tests cover native MAX.
"""

import argparse
from pathlib import Path
import subprocess
import tempfile

import verify


OUTPUT = verify.ROOT / "crates/nyx-ssz/src/type_info/tests/reference_cases.rs"
ERRORS = {
    "UINT_WIDTH": "InvalidIntegerWidth", "VECTOR_EMPTY": "EmptyVector",
    "CONTAINER_EMPTY": "EmptyContainer", "BAD_DECLARATION": "BadDeclaration",
    "LAYOUT_WIDTH": "LayoutWidth", "LAYOUT_TRAILING_GAP": "LayoutTrailingGap",
    "LAYOUT_TOO_WIDE": "LayoutTooWide", "LAYOUT_FIELD_COUNT": "LayoutFieldCount",
    "UNION_EMPTY": "EmptyUnion", "UNION_SELECTOR_REPEATED": "UnionSelectorRepeated",
    "UNION_SELECTOR_RANGE": "UnionSelectorRange", "UNION_INCOMPATIBLE": "UnionIncompatible",
}
RUST = {"bool": "Boolean", "uint": "Uint", "byteVector": "ByteVector",
        "byteList": "ByteList", "bitVector": "BitVector", "bitList": "BitList",
        "progressiveBitList": "ProgressiveBitList", "vector": "Vector", "list": "List",
        "progressiveList": "ProgressiveList", "container": "Container",
        "progressiveContainer": "ProgressiveContainer", "compatibleUnion": "CompatibleUnion"}


def declarations():
    boolean, byte, bad = ("bool",), ("uint", 1), ("uint", 3)
    cases = [boolean] + [("uint", n) for n in (0, 1, 2, 3, 32)]
    cases += [(kind, n) for kind in ("byteVector", "byteList", "bitVector", "bitList")
              for n in (0, 1, 2, 8)]
    cases += [("progressiveBitList", n) for n in (None, 0, 1, 2)]
    children = [boolean, byte, bad, ("byteVector", 2), ("byteList", 2),
                ("progressiveBitList", None)]
    cases += [(kind, child, n) for kind in ("vector", "list")
              for child in children for n in (0, 1, 2)]
    cases += [("progressiveList", child, n) for child in children for n in (None, 0, 1)]
    names = [(), ("x",), ("y",), ("x", "x"), ("x", "y"), ("é",),
             ("e\u0301",), ("a\0b",), ("a\0c",), ("字段🦀",)]
    fields = [(), (boolean,), (byte,), (("byteList", 0),), (("byteVector", 2),),
              (("vector", byte, 2),), (boolean, byte)]
    cases += [("container", ns, fs) for ns in names for fs in fields]
    masks = [(), (False,), (True,), (False, True), (True, False), (True, True)]
    cases += [("progressiveContainer", mask, ns, fs) for mask in masks
              for ns in ((), ("x",), ("x", "x"), ("x", "y"))
              for fs in ((), (byte,), (boolean,), (byte, boolean))]
    selectors = [(), (1,), (2,), (0,), (128,), (1, 1), (1, 2), (1, 2, 3)]
    cases += [("compatibleUnion", ss, fs) for ss in selectors
              for fs in ((), (byte,), (boolean,), (byte, boolean), (byte, byte))]
    a = ("progressiveContainer", (True,), ("a",), (byte,))
    b = ("progressiveContainer", (False, True), ("b",), (byte,))
    c = ("progressiveContainer", (True,), ("c",), (byte,))
    cases += [a, b, c, ("compatibleUnion", (1, 2), (a, b)),
              ("compatibleUnion", (3, 4), (b, c)), ("compatibleUnion", (1, 2, 3), (a, b, c))]
    cases += [("container", ("nested",), (child,)) for child in cases[-6:]]
    return cases


def quote(text, rust):
    def escape(character):
        if ord(character) < 32:
            return f"\\u{{{ord(character):x}}}" if rust else f"\\u{ord(character):04x}"
        return "\\" + character if character in '\\"' else character
    return '"' + "".join(escape(character) for character in text) + '"'


def render(declaration, rust):
    kind, *args = declaration
    prefix = f"D::{RUST[kind]}" if rust else f".{kind}"
    if kind == "bool":
        return prefix
    if kind in ("vector", "list", "progressiveList"):
        values = [("&" if rust else "(") + render(args[0], rust) + ("" if rust else ")"),
                  capacity(args[1], rust) if kind == "progressiveList" else str(args[1])]
    elif kind == "progressiveBitList":
        values = [capacity(args[0], rust)]
    elif kind in ("container", "progressiveContainer", "compatibleUnion"):
        fields = [("&" if rust else "") + render(child, rust) for child in args[-1]]
        values = []
        if kind == "progressiveContainer":
            values.append(array([str(bit).lower() for bit in args[0]], rust))
        keys = [str(n) for n in args[0]] if kind == "compatibleUnion" else [quote(n, rust) for n in args[-2]]
        values += [array(keys, rust), array(fields, rust)]
    else:
        values = [str(args[0])]
    return prefix + ("(" + ", ".join(values) + ")" if rust else " " + " ".join(values))


def capacity(value, rust):
    if value is None:
        return "None" if rust else "none"
    return f"Some({value})" if rust else f"(some {value})"


def array(items, rust):
    return ("&[" if rust else "[") + ", ".join(items) + "]"


def lean_source(cases):
    declarations = ",\n".join(render(case, False) for case in cases)
    return """import Ssz.Type.Valid
import Ssz.Codec.Layout
open Ssz
set_option maxRecDepth 4096
set_option maxHeartbeats 0
private def cases : List Desc := [
""" + declarations + """
]
#eval show IO Unit from do
  for (declaration, index) in cases.zipIdx do
    let width := match declaration.fixedSize with
      | none => "variable"
      | some width => toString width
    let valid := match declaration.wellFormed with
      | .ok () => "OK"
      | .error error => error.reason
    let row := String.ofList (cases.map fun other => if isCompatible declaration other then '1' else '0')
    IO.println s!"{index}|{width}|{declaration.isBasic}|{valid}|{row}"
"""


def reference_rows(cases):
    pins = verify.load_pins()
    spec = verify.VERIFICATION / ".lake/packages/ssz"
    revision = verify.run(["git", "rev-parse", "HEAD"], cwd=spec, capture=True).strip()
    dirty = verify.run(["git", "status", "--porcelain"], cwd=spec, capture=True).strip()
    if revision != pins["specification"]["revision"] or dirty:
        raise ValueError("reference specification is not the clean pinned revision")
    with tempfile.TemporaryDirectory(prefix="nyx-descriptor-reference-") as temporary:
        source = Path(temporary) / "Metadata.lean"
        source.write_text(lean_source(cases))
        try:
            output = verify.run(["lake", "env", "lean", source], cwd=verify.VERIFICATION, capture=True)
        except subprocess.CalledProcessError as error:
            raise ValueError(f"pinned Lean metadata evaluation failed:\n{error.stdout}") from error
    rows = [row.split("|") for row in output.splitlines()]
    if len(rows) != len(cases):
        raise ValueError(f"unexpected reference output: {output[:1000]}")
    for index, row in enumerate(rows):
        if len(row) != 5 or row[0] != str(index) or len(row[-1]) != len(cases):
            raise ValueError(f"invalid reference row: {row}")
    return rows


def rust_fixture(cases, rows):
    source = ["// Test data from pinned Ssz.Desc executable; NOT an extracted model or proof.",
              "// Regenerate: python3 scripts/descriptor_reference.py write",
              "use super::{D, E};", "", "type ReferenceCase = (D, Option<usize>, bool, Result<(), E>);", "",
              "#[rustfmt::skip]",
              f"pub(super) static CASES: [ReferenceCase; {len(cases)}] = ["]
    for case, (_, width, basic, reason, _) in zip(cases, rows, strict=True):
        size = "None" if width == "variable" else f"Some({width})"
        valid = "Ok(())" if reason == "OK" else f"Err(E::{ERRORS[reason]})"
        source.append(f"    ({render(case, True)}, {size}, {basic}, {valid}),")
    source += ["];", "", "#[rustfmt::skip]",
               f"pub(super) const COMPATIBLE: [&str; {len(cases)}] = ["]
    source += [f'    "{row[-1]}",' for row in rows]
    return "\n".join(source + ["];", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "write"))
    arguments = parser.parse_args()
    cases = declarations()
    source = rust_fixture(cases, reference_rows(cases))
    if arguments.command == "write":
        OUTPUT.write_text(source)
    elif OUTPUT.read_text() != source:
        raise ValueError("native metadata test data differs from the actual pinned reference")
    print(f"Reference metadata: {len(cases)} declarations, {len(cases) ** 2} ordered compatibility pairs.")


if __name__ == "__main__":
    main()
