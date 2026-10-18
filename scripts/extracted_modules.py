"""Partition Aeneas declarations without changing their text or Lean names."""
import re

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


def dependency_order(groups):
    dependencies = {}
    for module, declarations in groups.items():
        code = re.sub(r"/-.*?-/", "", "".join(declarations), flags=re.DOTALL)
        code = re.sub(r'"(?:\\.|[^"\\])*"', '""', code)
        references = set(re.findall(r"(?<![\w.])([a-z][a-z0-9_]*)\.", code))
        dependencies[module] = (references & groups.keys()) - {module}
    order = []
    while len(order) != len(groups):
        ready = sorted(module for module in groups
                       if module not in order and dependencies[module] <= set(order))
        if not ready:
            raise ValueError("generated module dependency cycle")
        order.extend(ready)
    return order, dependencies


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
