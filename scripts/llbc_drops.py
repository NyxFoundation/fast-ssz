"""Reject normal-flow drops that Aeneas's destructor-erasing model cannot justify.

This checks emitted local Drop statements, not arbitrary foreign library models or
caller callbacks. Unwinding and compiler-generated drop glue are outside the API
normal-return contract. Only closed standard containers without user destructors
may be discarded inside that contract.
"""


def _nodes(value, skip_unwind=False):
    stack = [value]
    while stack:
        item = stack.pop()
        if isinstance(item, dict):
            yield item
            stack.extend(child for key, child in item.items()
                         if not (skip_unwind and key == "on_unwind"))
        elif isinstance(item, list):
            stack.extend(item)


def _interned(document):
    table = {}
    for node in _nodes(document):
        if "HashConsedValue" not in node:
            continue
        identifier, value = node["HashConsedValue"]
        if identifier in table and table[identifier] != value:
            raise ValueError("conflicting LLBC interned values")
        table[identifier] = value
    return table


def _resolve(value, table, trail):
    while isinstance(value, dict) and ("HashConsedValue" in value or "Deduplicated" in value):
        identifier = (value["HashConsedValue"][0] if "HashConsedValue" in value
                      else value["Deduplicated"])
        if identifier in trail or identifier not in table:
            raise ValueError("missing or cyclic LLBC type reference")
        trail = trail | {identifier}
        value = table[identifier]
    return value, trail


def _name(declaration):
    return "::".join(part["Ident"][0] for part in declaration["item_meta"]["name"] if "Ident" in part)


def _closed_standard_type(value, table, types, trail=frozenset()):
    ty, trail = _resolve(value, table, trail)
    if not isinstance(ty, dict):
        return False
    if "Literal" in ty or "Ref" in ty or "RawPtr" in ty:
        return True
    if "Adt" not in ty:
        return False
    adt = ty["Adt"]
    arguments = adt["generics"]["types"]
    if adt["builtin"] in ("Array", "Tuple"):
        return all(_closed_standard_type(arg, table, types, trail) for arg in arguments)
    declaration = types.get(adt["id"])
    return (declaration is not None and _name(declaration) == "alloc::vec::Vec"
            and len(arguments) == 1
            and _closed_standard_type(arguments[0], table, types, trail))


def _generated_destructor(function, implementations):
    source = function["src"]
    if not isinstance(source, dict) or "TraitImpl" not in source:
        return False
    identifier = source["TraitImpl"]["impl_ref"]["id"]
    return implementations[identifier]["src"] == "Destruct"


def _check_statement(node, table, types, functions):
    if "Drop" in node:
        drop = node["Drop"]
        if drop["kind"] != "Precise":
            raise ValueError("normal-flow drops must be precise")
        if not _closed_standard_type(drop["place"]["ty"], table, types):
            raise ValueError("unmodeled normal-flow drop; return owned state instead")
    if "Call" not in node:
        return
    pointer = node["Call"]["call"]["func"]
    kind = pointer.get("Regular", {}).get("kind", {}).get("Fun", {})
    identifier = kind.get("Regular")
    if identifier is not None and _name(functions[identifier]) in ("core::mem::drop", "core::mem::forget"):
        raise ValueError("explicit discard call is outside the ownership contract")


def assert_safe_drops(document):
    """Validate the precise LLBC before backend translation, without modifying it."""
    translated = document["translated"]
    options = translated["options"]
    if (document.get("has_errors") is not False or options.get("precise_drops") is not True
            or options.get("desugar_drops") is not False):
        raise ValueError("ownership audit requires successful precise, undesugared LLBC")
    table = _interned(document)
    types = {item["def_id"]: item for item in translated["type_decls"] if item}
    implementations = {item["def_id"]: item for item in translated["trait_impls"] if item}
    functions = {item["def_id"]: item for item in translated["fun_decls"] if item}
    for function in functions.values():
        if not function["item_meta"]["is_local"] or _generated_destructor(function, implementations):
            continue
        for node in _nodes(function["body"], skip_unwind=True):
            _check_statement(node, table, types, functions)
