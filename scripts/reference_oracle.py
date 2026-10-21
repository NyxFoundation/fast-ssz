#!/usr/bin/env python3
"""Run only through the authenticated-source, isolated reference-vector wrapper."""

from functools import partial
import json
from pathlib import Path
import re
import sys

MAX_METADATA_BYTES = 1024 * 1024
PROGRESSIVE_FAMILIES = {"progressive_bitlist", "basic_progressive_list"}


def read_text(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError("oracle input must be a regular fixture file")
    with path.open("rb") as source:
        data = source.read(MAX_METADATA_BYTES + 1)
    if len(data) > MAX_METADATA_BYTES:
        raise ValueError("oracle metadata exceeds its size limit")
    return data.decode("ascii")


def decoded_root(decoder, encoded):
    result = decoder(encoded)
    if result.encode_bytes() != encoded:
        raise ValueError("current reference changes the fixture wire value")
    root = result.hash_tree_root()
    if not isinstance(root, bytes) or len(root) != 32:
        raise ValueError("current reference produced an invalid root")
    return "0x" + root.hex()


def root_record(directory, decoder, encoded):
    original = re.fullmatch(r"root:\s*['\"]0x([0-9a-f]{64})['\"]\s*",
                            read_text(directory / "meta.yaml"))
    if original is None:
        raise ValueError("unknown canonical progressive root metadata")
    return {"source_root": "0x" + original[1], "root": decoded_root(decoder, encoded)}


def bitlist_case(directory, decoder):
    value = re.fullmatch(r"['\"]0x([0-9a-f]*)['\"]\s*", read_text(directory / "value.yaml"))
    if value is None:
        raise ValueError("unknown canonical progressive bitlist metadata")
    return root_record(directory, decoder, bytes.fromhex(value[1]))


def primitive_bytes(primitive, values):
    if not isinstance(values, list):
        raise ValueError("expected a primitive sequence")
    if primitive == "bool":
        if any(type(value) is not bool for value in values):
            raise ValueError("expected Boolean observations")
        return bytes(values)
    if primitive not in {"uint8", "uint16", "uint32", "uint64", "uint128", "uint256"}:
        raise ValueError("unknown primitive width")
    width = int(primitive[4:]) // 8
    encoded = bytearray()
    for value in values:
        if isinstance(value, str) and re.fullmatch(r"[0-9]+", value):
            value = int(value)
        if type(value) is not int or not 0 <= value < 1 << (8 * width):
            raise ValueError("unsigned observation exceeds its primitive width")
        encoded.extend(value.to_bytes(width, "little"))
    return bytes(encoded)


def basic_primitive(directory, decoders):
    name = re.fullmatch(r"proglist_(bool|uint8|uint16|uint32|uint64|uint128|uint256)_[A-Za-z0-9_]+",
                        directory.name)
    if name is None or name[1] not in decoders:
        raise ValueError("unknown progressive primitive schema")
    return name[1]


def basic_list_case(directory, decoders):
    primitive = basic_primitive(directory, decoders)
    # The pinned flow-style YAML uses single-quoted large decimal integers.
    # Normalize only those tokens to JSON strings; no general YAML evaluation.
    text = re.sub(r"'([0-9]+)'", r'"\1"', read_text(directory / "value.yaml"))
    encoded = primitive_bytes(primitive, json.loads(text))
    return root_record(directory, decoders[primitive], encoded)


def fixture_directories(corpus, family, outcome):
    cases = sorted((corpus / family / outcome).iterdir())
    for case in cases:
        if case.is_symlink() or not case.is_dir() or not re.fullmatch(r"[A-Za-z0-9_]+", case.name):
            raise ValueError("unknown progressive fixture entry")
    return cases


def fixture_blob(case):
    path = case / "serialized.ssz_snappy"
    if path.is_symlink() or not path.is_file():
        raise ValueError("oracle input must be a regular fixture file")
    with path.open("rb") as source:
        data = source.read(64 * 1024 * 1024 + 1)
    if len(data) > 64 * 1024 * 1024:
        raise ValueError("oracle wire fixture exceeds its size limit")
    return data


def invalid_aliases(corpus):
    family = "basic_progressive_list"
    primitives = {"bool", "uint8", "uint16", "uint32", "uint64", "uint128", "uint256"}
    witnesses = {}
    for case in fixture_directories(corpus, family, "valid"):
        key = (basic_primitive(case, primitives), fixture_blob(case))
        witnesses.setdefault(key, f"{family}/valid/{case.name}")
    aliases = {}
    for case in fixture_directories(corpus, family, "invalid"):
        witness = witnesses.get((basic_primitive(case, primitives), fixture_blob(case)))
        if witness is not None:
            aliases[f"{family}/invalid/{case.name}"] = {"witness": witness}
    return aliases


def generate(corpus, reference_revision, corpus_revision, handlers):
    if not re.fullmatch(r"[0-9a-f]{40}", reference_revision) or not re.fullmatch(r"[0-9a-f]{40}", corpus_revision):
        raise ValueError("oracle revisions must be immutable")
    if not handlers or not set(handlers) <= PROGRESSIVE_FAMILIES:
        raise ValueError("unknown or empty progressive reference selection")
    roots = {}
    for family, handler in sorted(handlers.items()):
        cases = fixture_directories(corpus, family, "valid")
        if not cases:
            raise ValueError("empty progressive reference selection")
        for case in cases:
            roots[f"{family}/valid/{case.name}"] = handler(case)
    if "basic_progressive_list" in handlers:
        roots.update(invalid_aliases(corpus))
    return {"format_version": 2, "corpus_revision": corpus_revision,
            "reference_revision": reference_revision, "roots": roots}


def reference_handlers(families):
    if not families or len(set(families)) != len(families) or not set(families) <= PROGRESSIVE_FAMILIES:
        raise ValueError("unknown or repeated progressive reference family")
    handlers = {}
    if "progressive_bitlist" in families:
        from remerkleable.progressive import ProgressiveBitlist
        handlers["progressive_bitlist"] = partial(bitlist_case, decoder=ProgressiveBitlist.decode_bytes)
    if "basic_progressive_list" in families:
        from remerkleable import basic
        from remerkleable.progressive import ProgressiveList
        primitives = {"bool": basic.boolean, **{f"uint{width}": getattr(basic, f"uint{width}")
                      for width in (8, 16, 32, 64, 128, 256)}}
        decoders = {name: ProgressiveList[element].decode_bytes for name, element in primitives.items()}
        handlers["basic_progressive_list"] = partial(basic_list_case, decoders=decoders)
    return handlers


def main():
    if len(sys.argv) < 7:
        raise ValueError("oracle requires source, corpus, output, both revisions and explicit families")
    source, corpus, output = (Path(argument) for argument in sys.argv[1:4])
    reference_revision, corpus_revision = sys.argv[4:6]
    sys.path.insert(0, str(source))
    document = generate(corpus, reference_revision, corpus_revision, reference_handlers(sys.argv[6:]))
    output.write_text(json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n", encoding="ascii")
    records = list(document["roots"].values())
    aliases = sum("witness" in value for value in records)
    changed = sum("source_root" in value and value["source_root"] != value["root"] for value in records)
    print(f"Regenerated {len(records) - aliases} progressive roots from official reference {reference_revision}; "
          f"{changed} differ from the preserved source-corpus metadata.")
    if aliases:
        print(f"Rechecked {aliases} mislabeled invalid fixtures against same-type, byte-identical valid witnesses. "
              "The original labels and data are preserved. No cases were skipped.")


if __name__ == "__main__":
    try:
        main()
    except Exception:
        print("authenticated reference root generation failed", file=sys.stderr)
        sys.exit(1)
