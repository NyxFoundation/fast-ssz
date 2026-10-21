#!/usr/bin/env python3
"""Run only through the authenticated-source, isolated reference-vector wrapper."""

import json
from pathlib import Path
import re
import sys

MAX_METADATA_BYTES = 1024 * 1024


def read_text(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError("oracle input must be a regular fixture file")
    with path.open("rb") as source:
        data = source.read(MAX_METADATA_BYTES + 1)
    if len(data) > MAX_METADATA_BYTES:
        raise ValueError("oracle metadata exceeds its size limit")
    return data.decode("ascii")


def bitlist_case(directory, decoder):
    value = re.fullmatch(r"['\"]0x([0-9a-f]*)['\"]\s*", read_text(directory / "value.yaml"))
    original = re.fullmatch(r"root:\s*['\"]0x([0-9a-f]{64})['\"]\s*",
                            read_text(directory / "meta.yaml"))
    if value is None or original is None:
        raise ValueError("unknown canonical progressive bitlist metadata")
    encoded = bytes.fromhex(value[1])
    result = decoder(encoded)
    if result.encode_bytes() != encoded:
        raise ValueError("current reference changes the fixture wire value")
    root = result.hash_tree_root()
    if not isinstance(root, bytes) or len(root) != 32:
        raise ValueError("current reference produced an invalid root")
    return {"source_root": "0x" + original[1], "root": "0x" + root.hex()}


def generate(corpus, reference_revision, corpus_revision, decoder):
    if not re.fullmatch(r"[0-9a-f]{40}", reference_revision) or not re.fullmatch(r"[0-9a-f]{40}", corpus_revision):
        raise ValueError("oracle revisions must be immutable")
    directory = corpus / "progressive_bitlist" / "valid"
    roots = {}
    for case in sorted(directory.iterdir()):
        if case.is_symlink() or not case.is_dir() or not re.fullmatch(r"[A-Za-z0-9_]+", case.name):
            raise ValueError("unknown progressive fixture entry")
        roots[f"progressive_bitlist/valid/{case.name}"] = bitlist_case(case, decoder)
    if not roots:
        raise ValueError("empty progressive reference selection")
    return {"format_version": 1, "corpus_revision": corpus_revision,
            "reference_revision": reference_revision, "roots": roots}


def main():
    if len(sys.argv) != 6:
        raise ValueError("oracle requires source, corpus, output and both source revisions")
    source, corpus, output = (Path(argument) for argument in sys.argv[1:4])
    reference_revision, corpus_revision = sys.argv[4:6]
    sys.path.insert(0, str(source))
    from remerkleable.progressive import ProgressiveBitlist
    document = generate(corpus, reference_revision, corpus_revision, ProgressiveBitlist.decode_bytes)
    output.write_text(json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n", encoding="ascii")
    changed = sum(value["source_root"] != value["root"] for value in document["roots"].values())
    print(f"Regenerated {len(document['roots'])} progressive roots from official reference {reference_revision}; "
          f"{changed} differ from the preserved source-corpus metadata.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, UnicodeError, ImportError):
        print("authenticated reference root generation failed", file=sys.stderr)
        sys.exit(1)
