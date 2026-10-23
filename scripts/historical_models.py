"""Archive omitted Aeneas declarations without treating them as current proofs."""
from extracted_modules import NAMESPACE, declaration_units, declared_names


def split_generated(source):
    opening, closing = f"namespace {NAMESPACE}\n", f"\nend {NAMESPACE}"
    header, remainder = source.split(opening)
    body, tail = remainder.rsplit(closing, 1)
    if tail.strip():
        raise ValueError("unexpected generated model suffix")
    return header, declaration_units(body)


def archive_omitted(path, fresh):
    header, units = split_generated(path.read_text())
    names = declared_names(fresh)
    omitted = []
    for unit in units:
        declared = declared_names(unit)
        if declared & names and not declared <= names:
            raise ValueError("cannot split a shared generated declaration block")
        if not declared & names:
            omitted.append(unit)
    if not omitted:
        return
    module = path.stem
    destination = path.with_name(f"Historical{module}.lean")
    header = header.replace("import Aeneas\n", f"import Aeneas\nimport {NAMESPACE}.{module}\n")
    text = ("-- Historical pre-RustCrypto Aeneas declarations; not current-source certification.\n"
            + header + f"namespace {NAMESPACE}\n" + "".join(omitted) + f"\nend {NAMESPACE}\n")
    if destination.exists() and destination.read_text() != text:
        raise ValueError("historical model changes require explicit review")
    destination.write_text(text)
