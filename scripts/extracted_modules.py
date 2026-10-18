"""Partition Aeneas declarations without changing their text or Lean names."""
import re
from graphlib import CycleError, TopologicalSorter

NAMESPACE = "FastSszRust"
DOC = re.compile(r"^/-- \[fast_ssz::([a-z][a-z0-9_]*)::", re.MULTILINE)


def declaration_units(body):
    units, lines, depth = [], [], 0
    for line in body.splitlines(keepends=True):
        begins = DOC.match(line) or line.rstrip() == "mutual"
        if begins and depth == 0 and "".join(lines).strip():
            units.append("".join(lines))
            lines = []
        if line.rstrip() == "mutual":
            depth += 1
        elif line.rstrip() == "end" and depth:
            depth -= 1
        lines.append(line)
    if depth:
        raise ValueError("unterminated generated mutual block")
    if lines:
        units.append("".join(lines))
    if "".join(units) != body:
        raise ValueError("generated declaration text was lost")
    return units


def code_only(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    return re.sub(r'"(?:\\.|[^"\\])*"', '""', text)


def graph_order(dependencies):
    sorter = TopologicalSorter(dependencies)
    try:
        sorter.prepare()
    except CycleError as error:
        raise ValueError("generated declaration dependency cycle") from error
    order = []
    while sorter.is_active():
        ready = sorted(sorter.get_ready())
        order.extend(ready)
        sorter.done(*ready)
    return order


def dependency_order(groups):
    dependencies = {}
    for module, declarations in groups.items():
        code = code_only("".join(declarations))
        references = set(re.findall(r"(?<![\w.])([a-z][a-z0-9_]*)\.", code))
        dependencies[module] = (references & groups.keys()) - {module}
    return graph_order(dependencies), dependencies


def canonical_declarations(module, units):
    entries, owners = {}, {}
    pattern = r"(?m)^[ \t]*(?:def|abbrev|structure|inductive|class)\s+([\w]+(?:\.[\w]+)+)"
    for unit in units:
        names = set(re.findall(pattern, code_only(unit)))
        if not names or any(not name.startswith(module + ".") for name in names):
            raise ValueError("unclassified generated declaration names")
        if names & owners.keys():
            raise ValueError("duplicate generated declaration names")
        key = min(names)
        entries[key] = unit.strip("\n") + "\n\n"
        owners.update({name: key for name in names})
    dependencies = {key: set() for key in entries}
    for key, text in entries.items():
        references = re.findall(r"(?<![\w.])([\w]+(?:\.[\w]+)+)", code_only(text))
        for reference in references:
            while "." in reference:
                if reference in owners:
                    dependencies[key].add(owners[reference])
                    break
                reference = reference.rsplit(".", 1)[0]
        dependencies[key].discard(key)
    return [entries[key] for key in graph_order(dependencies)]


def split_model(source):
    marker, closing = f"namespace {NAMESPACE}\n", f"\nend {NAMESPACE}"
    if source.count(marker) != 1 or source.count(closing) != 1:
        raise ValueError("unexpected Aeneas namespace layout")
    header, remainder = source.split(marker)
    body, tail = remainder.rsplit(closing, 1)
    if tail.strip() or header.count("import Aeneas\n") != 1:
        raise ValueError("unexpected Aeneas header or trailing declarations")
    groups = {}
    for unit in declaration_units(body):
        modules = set(DOC.findall(unit))
        if len(modules) != 1:
            raise ValueError("unclassified or cross-module mutual declarations")
        groups.setdefault(modules.pop(), []).append(unit)
    names = {module: "".join(part.capitalize() for part in module.split("_")) for module in groups}
    if len(set(names.values())) != len(names):
        raise ValueError("generated module filename collision")
    groups = {module: canonical_declarations(module, units) for module, units in groups.items()}
    order, dependencies = dependency_order(groups)
    output = {}
    for module in order:
        imports = "".join(f"import {NAMESPACE}.{names[dependency]}\n"
                          for dependency in order if dependency in dependencies[module])
        prelude = header.replace("import Aeneas\n", "import Aeneas\n" + imports)
        output[f"{NAMESPACE}/{names[module]}.lean"] = (
            prelude + marker + "".join(groups[module]) + closing + "\n"
        )
    output[f"{NAMESPACE}.lean"] = (
        "-- Generated module entry point; declarations are unchanged Aeneas output.\n" +
        "".join(f"import {NAMESPACE}.{names[module]}\n" for module in order)
    )
    return output
