"""Inventory public traits and require proved, concretely extracted local instances."""
import json
from pathlib import Path
import re
from extracted_modules import NAMESPACE, declaration_units, declared_names

IDENTIFIER = r"[A-Za-z_][A-Za-z_0-9]*"
IMPLEMENTATION = re.compile(
    rf"^/-- Trait implementation: \[[^\n]*\{{impl ({IDENTIFIER}(?:::{IDENTIFIER})*)\s"
)


def qualified(value, separator):
    return isinstance(value, str) and all(
        re.fullmatch(IDENTIFIER, part) for part in value.split(separator)
    )


def validate_contract(contract):
    if not isinstance(contract, dict) or set(contract) != {"rust", "law", "members", "instances"}:
        raise ValueError("invalid trait contract fields")
    if not qualified(contract["rust"], "::") or not qualified(contract["law"], "."):
        raise ValueError("invalid trait contract identifier")
    if (contract["rust"], contract["law"]) != (
            "nyx_ssz::codec::Ssz", "NyxSszVerification.CodecLaw"):
        raise ValueError("unsupported trait correctness law")
    members = contract["members"]
    if not isinstance(members, dict) or not members:
        raise ValueError("nonempty trait member inventory required")
    if any(not qualified(name, "::") or kind not in ("function", "assoc_const")
           for name, kind in members.items()):
        raise ValueError("unsupported trait member")
    instances = contract["instances"]
    if not isinstance(instances, list) or not instances:
        raise ValueError("nonempty trait instance inventory required")
    for instance in instances:
        validate_instance(instance)
    for field in ("type", "lean", "proof"):
        if len({instance[field] for instance in instances}) != len(instances):
            raise ValueError("duplicate trait instance")


def validate_instance(instance):
    if not isinstance(instance, dict) or set(instance) != {"type", "lean", "proof"}:
        raise ValueError("invalid trait instance fields")
    if not qualified(instance["type"], "::"):
        raise ValueError("unsupported trait instance type")
    if not qualified(instance["lean"], ".") or not qualified(instance["proof"], "."):
        raise ValueError("invalid trait instance identifier")


def load_contracts(path):
    contracts = json.loads(Path(path).read_text())
    if not isinstance(contracts, list):
        raise ValueError("trait contracts must be a list")
    for contract in contracts:
        validate_contract(contract)
    if len({contract["rust"] for contract in contracts}) != len(contracts):
        raise ValueError("duplicate trait contract")
    return contracts


def member_inventory(index, identifiers):
    members = {}
    for identifier in identifiers:
        item = index[str(identifier)]
        if item["name"] in members or len(item["inner"]) != 1:
            raise ValueError("ambiguous trait member")
        members[item["name"]] = next(iter(item["inner"]))
    return members


def instance_type(value):
    if set(value) == {"primitive"}:
        return value["primitive"]
    if set(value) == {"resolved_path"} and value["resolved_path"]["args"] is None:
        return value["resolved_path"]["path"]
    raise ValueError("trait instance type needs proof inventory support")


def validate_implementations(index, declaration, contract):
    discovered, items = [], set()
    for identifier in declaration["implementations"]:
        implementation = index[str(identifier)]["inner"]["impl"]
        discovered.append(instance_type(implementation["for"]))
        if member_inventory(index, implementation["items"]) != contract["members"]:
            raise ValueError("trait implementation member inventory differs")
        items.update(str(value) for value in implementation["items"])
    expected = [instance["type"] for instance in contract["instances"]]
    if sorted(discovered) != sorted(expected):
        raise ValueError("trait implementation inventory differs")
    return items


def validate_traits(document, contracts):
    registered = {contract["rust"]: contract for contract in contracts}
    reserved = set()
    index = document.get("index", {})
    for identifier, item in index.items():
        declaration = item["inner"].get("trait")
        if item.get("crate_id") != 0 or item.get("visibility") != "public" or declaration is None:
            continue
        name = "::".join(document["paths"].get(identifier, {}).get("path", []))
        if name not in registered:
            raise ValueError("public trait has no registered correctness contract")
        contract = registered.pop(name)
        if member_inventory(index, declaration["items"]) != contract["members"]:
            raise ValueError("trait declaration member inventory differs")
        reserved.update(str(value) for value in declaration["items"])
        reserved.update(validate_implementations(index, declaration, contract))
    if registered:
        raise ValueError("registered trait is not a public declaration")
    return reserved


def assert_extracted_instances(artifacts, contracts):
    registered = {contract["rust"] for contract in contracts}
    expected = {instance["lean"] for contract in contracts for instance in contract["instances"]}
    discovered = set()
    for source in artifacts.values():
        for unit in declaration_units(source):
            match = IMPLEMENTATION.match(unit.lstrip())
            if match is None or not match[1].startswith("nyx_ssz::"):
                continue
            names = declared_names(unit)
            if match[1] not in registered or len(names) != 1:
                raise ValueError("unregistered or ambiguous extracted trait instance")
            discovered.update(f"{NAMESPACE}.{name}" for name in names)
    if discovered != expected:
        raise ValueError("extracted trait dictionary inventory differs")
