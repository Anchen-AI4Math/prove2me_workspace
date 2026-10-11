#!/usr/bin/env python3
"""Pure validation primitives for schema-v2 structural kernel snapshots.

This module is intentionally independent of the ordinary theorem/definition
provider validator.  It rejects recursor evidence that omits reduction-rule
field counts or RHS expressions.
"""

from __future__ import annotations

import copy
import json
from collections.abc import Iterable
from typing import Any


STD3 = {"Classical.choice", "Quot.sound", "propext"}
STRUCTURAL_KINDS = {"inductive", "ctor", "rec"}
SUPPORTED_KINDS = {"theorem", "def", *STRUCTURAL_KINDS}
KERNEL_METADATA_SCHEMA = "lean-4.33.1-ConstantInfo-complete-v1"
ROW_KEYS = {
    "schemaVersion", "kernelMetadataSchema", "sourceName", "resolvedName",
    "sourceModule", "declGraphSha256", "declGraphRowSha256", "graphKind",
    "envKind", "ownerKind", "ownerId", "commandUnit", "familyRoot",
    "levelParams", "closedType", "closedValue", "type", "value", "axioms",
    "kindMetadata", "familyReferences", "transitiveNames",
}
REQUEST_KEYS = {
    "source_name", "source_module", "graph_kind", "decl_graph_sha256",
    "decl_graph_row_sha256", "owner_kind", "owner_id", "command_unit",
    "family_root",
}
REFERENCE_KEYS = {"name", "module", "envKind"}
METADATA_KEYS = {
    "theorem": {"proofValueExported"},
    "def": {"valueExported", "safety"},
    "inductive": {
        "numParams", "numIndices", "all", "constructors", "numNested",
        "isRecursive", "isUnsafe", "isReflexive",
    },
    "ctor": {"inductive", "constructorIndex", "numParams", "numFields", "isUnsafe"},
    "rec": {
        "all", "numParams", "numIndices", "numMotives", "numMinors",
        "rules", "supportsK", "isUnsafe",
    },
}


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def forbidden_open_tag(value: Any) -> str | None:
    if isinstance(value, list):
        if value and isinstance(value[0], str) and value[0] in {"fvar", "mvar"}:
            return value[0]
        for item in value:
            found = forbidden_open_tag(item)
            if found:
                return found
    elif isinstance(value, dict):
        for item in value.values():
            found = forbidden_open_tag(item)
            if found:
                return found
    return None


def canonical_expr(value: Any, level_params: list[str]) -> Any:
    _assert(len(level_params) == len(set(level_params))
            and all(isinstance(item, str) for item in level_params),
            "Level parameter list is invalid")
    indices = {name: index for index, name in enumerate(level_params)}

    def walk(node: Any) -> Any:
        if not isinstance(node, list):
            return node
        if len(node) == 2 and node[0] == "param":
            _assert(node[1] in indices, f"Unknown universe parameter: {node[1]}")
            return ["param", indices[node[1]]]
        return [walk(item) for item in node]

    return walk(value)


def expression_names(value: Any) -> set[str]:
    names: set[str] = set()

    def walk(node: Any) -> None:
        if isinstance(node, list):
            if len(node) >= 2 and node[0] in {"const", "projection"} and isinstance(node[1], str):
                names.add(node[1])
            for item in node:
                walk(item)
        elif isinstance(node, dict):
            for item in node.values():
                walk(item)

    walk(value)
    return names


def _family_name(root: str, name: str) -> bool:
    return name == root or name.startswith(root + ".")


def _validate_reference_rows(rows: Any, *, family_root: str, module: str,
                             graph: dict[str, dict[str, Any]], label: str) -> list[str]:
    _assert(isinstance(rows, list), f"{label} must be a list")
    names: list[str] = []
    for item in rows:
        _assert(isinstance(item, dict) and set(item) == REFERENCE_KEYS,
                f"{label} has an invalid reference row")
        name = item["name"]
        _assert(isinstance(name, str) and _family_name(family_root, name),
                f"{label} crosses the family boundary: {name}")
        _assert(item["module"] == module, f"{label} has a wrong actual module owner: {name}")
        _assert(name in graph and item["envKind"] == graph[name]["kind"],
                f"{label} kind is not authenticated by decl_graph: {name}")
        names.append(name)
    _assert(names == sorted(set(names)), f"{label} is not sorted and duplicate-free")
    return names


def validate_row_basic(row: dict[str, Any], request: dict[str, Any],
                       owner: dict[str, Any], graph: dict[str, dict[str, Any]],
                       graph_sha256: str, *, expected_module: str | None = None) -> dict[str, Any]:
    _assert(set(row) == ROW_KEYS, f"Unexpected structural row schema: {request.get('source_name')}")
    _assert(set(request) == REQUEST_KEYS, f"Unexpected structural request schema: {request.get('source_name')}")
    name = request["source_name"]
    _assert(row["schemaVersion"] == 2 and row["kernelMetadataSchema"] == KERNEL_METADATA_SCHEMA,
            f"Structural kernel schema mismatch: {name}")
    _assert(row["sourceName"] == row["resolvedName"] == owner["source_name"] == name,
            f"Exact public structural Name mismatch: {name}")
    _assert(name in graph, f"Structural Name is absent from decl_graph: {name}")
    graph_row = graph[name]
    expected = {
        "source_module": graph_row["module"] if expected_module is None else expected_module,
        "graph_kind": graph_row["kind"],
        "decl_graph_sha256": graph_sha256,
        "decl_graph_row_sha256": graph_row["_row_sha256"],
        "owner_kind": owner["owner_kind"],
        "owner_id": owner["owner_id"],
        "command_unit": owner["command_unit"],
        "family_root": owner["family_root"],
    }
    for key, value in expected.items():
        _assert(request[key] == value, f"Structural request differs: {name}: {key}")
    row_mapping = {
        "source_module": "sourceModule", "graph_kind": "graphKind",
        "decl_graph_sha256": "declGraphSha256", "decl_graph_row_sha256": "declGraphRowSha256",
        "owner_kind": "ownerKind", "owner_id": "ownerId", "command_unit": "commandUnit",
        "family_root": "familyRoot",
    }
    for request_key, row_key in row_mapping.items():
        _assert(row[row_key] == request[request_key],
                f"Structural row/request mismatch: {name}: {row_key}")
    kind = row["graphKind"]
    _assert(kind in SUPPORTED_KINDS and row["envKind"] == kind,
            f"Unsupported or mismatched structural env kind: {name}: {kind}")
    _assert(row["closedType"] is True and row["type"] is not None
            and forbidden_open_tag(row["type"]) is None,
            f"Structural type is absent or open: {name}")
    canonical_expr(row["type"], row["levelParams"])

    metadata = row["kindMetadata"]
    _assert(isinstance(metadata, dict) and set(metadata) == METADATA_KEYS[kind],
            f"Incomplete ConstantInfo metadata: {name}: {kind}")
    if kind == "def":
        _assert(row["closedValue"] is True and row["value"] is not None
                and metadata["valueExported"] is True
                and isinstance(metadata["safety"], str)
                and forbidden_open_tag(row["value"]) is None,
                f"Definition value metadata is incomplete: {name}")
        canonical_expr(row["value"], row["levelParams"])
    elif kind == "theorem":
        _assert(row["closedValue"] is None and row["value"] is None
                and metadata == {"proofValueExported": False},
                f"Theorem proof value policy failed: {name}")
    else:
        _assert(row["closedValue"] is None and row["value"] is None,
                f"Structural ConstantInfo must not use a definition value slot: {name}")
    if kind == "inductive":
        _assert(all(isinstance(metadata[key], int) and metadata[key] >= 0
                    for key in ("numParams", "numIndices", "numNested"))
                and all(isinstance(metadata[key], bool)
                        for key in ("isRecursive", "isUnsafe", "isReflexive"))
                and all(isinstance(metadata[key], list)
                        for key in ("all", "constructors")),
                f"InductiveVal metadata types are invalid: {name}")
    elif kind == "ctor":
        _assert(isinstance(metadata["inductive"], str)
                and all(isinstance(metadata[key], int) and metadata[key] >= 0
                        for key in ("constructorIndex", "numParams", "numFields"))
                and isinstance(metadata["isUnsafe"], bool),
                f"ConstructorVal metadata types are invalid: {name}")
    elif kind == "rec":
        _assert(all(isinstance(metadata[key], int) and metadata[key] >= 0
                    for key in ("numParams", "numIndices", "numMotives", "numMinors"))
                and isinstance(metadata["all"], list)
                and isinstance(metadata["rules"], list)
                and all(isinstance(metadata[key], bool) for key in ("supportsK", "isUnsafe")),
                f"RecursorVal metadata types are invalid: {name}")
        _assert(metadata["numMinors"] == len(metadata["rules"]),
                f"Recursor minor/rule count mismatch: {name}")
        for rule in metadata["rules"]:
            _assert(isinstance(rule, dict) and set(rule) == {"ctor", "nfields", "rhs"}
                    and isinstance(rule["ctor"], str)
                    and isinstance(rule["nfields"], int) and rule["nfields"] >= 0
                    and rule["rhs"] is not None
                    and forbidden_open_tag(rule["rhs"]) is None,
                    f"Recursor rule lacks ctor/nfields/full RHS: {name}")
            canonical_expr(rule["rhs"], row["levelParams"])

    axioms = row["axioms"]
    _assert(isinstance(axioms, list) and axioms == sorted(set(axioms))
            and all(isinstance(item, str) for item in axioms) and set(axioms) <= STD3,
            f"Structural row axioms are not deterministic Std3: {name}")
    expected_family_refs = {
        ref for ref in expression_names(row["type"]) if _family_name(row["familyRoot"], ref)
    }
    if kind == "rec":
        for rule in metadata["rules"]:
            expected_family_refs.update(
                ref for ref in expression_names(rule["rhs"]) if _family_name(row["familyRoot"], ref))
    actual_family_refs = _validate_reference_rows(
        row["familyReferences"], family_root=row["familyRoot"], module=row["sourceModule"],
        graph=graph, label=f"familyReferences:{name}")
    _assert(actual_family_refs == sorted(expected_family_refs),
            f"Family type/rule reference inventory differs: {name}")
    transitive = _validate_reference_rows(
        row["transitiveNames"], family_root=row["familyRoot"], module=row["sourceModule"],
        graph=graph, label=f"transitiveNames:{name}")
    if kind not in STRUCTURAL_KINDS:
        _assert(transitive == [], f"Ordinary declaration has structural closure metadata: {name}")
    return {
        "source_name": name,
        "kind": kind,
        "module": row["sourceModule"],
        "command_unit": row["commandUnit"],
        "family_root": row["familyRoot"],
        "axioms": axioms,
        "std3_only": True,
        "kernel_metadata_complete": kind not in STRUCTURAL_KINDS or bool(metadata),
        "recursor_rules_complete": kind != "rec" or all("rhs" in rule and "nfields" in rule for rule in metadata["rules"]),
    }


def direct_structural_names(row: dict[str, Any]) -> list[str]:
    metadata = row["kindMetadata"]
    kind = row["graphKind"]
    if kind == "inductive":
        return list(metadata["all"]) + list(metadata["constructors"])
    if kind == "ctor":
        return [metadata["inductive"]]
    if kind == "rec":
        return list(metadata["all"]) + [rule["ctor"] for rule in metadata["rules"]]
    return []


def expected_transitive_names(name: str, rows: dict[str, dict[str, Any]]) -> list[str]:
    pending = [name, *direct_structural_names(rows[name])]
    seen: set[str] = set()
    while pending:
        current = pending.pop(0)
        if current in seen:
            continue
        _assert(current in rows, f"Structural closure escapes captured family: {name}: {current}")
        seen.add(current)
        pending.extend(direct_structural_names(rows[current]))
    return sorted(seen)


def validate_family_relationships(rows: dict[str, dict[str, Any]], family: dict[str, Any]) -> dict[str, Any]:
    root = family["family_root"]
    names = family["source_names"]
    _assert(sorted(rows) == sorted(names), f"Family row coverage differs: {root}")
    kinds = {kind: sorted(name for name, row in rows.items() if row["graphKind"] == kind)
             for kind in SUPPORTED_KINDS}
    _assert(len(kinds["inductive"]) == len(kinds["ctor"]) == len(kinds["rec"]) == 1,
            f"Family does not contain exactly one inductive/ctor/rec: {root}")
    inductive_name, ctor_name, rec_name = kinds["inductive"][0], kinds["ctor"][0], kinds["rec"][0]
    _assert(inductive_name == root, f"Family root is not the inductive Name: {root}")
    inductive = rows[inductive_name]["kindMetadata"]
    constructor = rows[ctor_name]["kindMetadata"]
    recursor = rows[rec_name]["kindMetadata"]
    _assert(inductive["all"] == [inductive_name]
            and inductive["constructors"] == [ctor_name]
            and constructor["inductive"] == inductive_name
            and constructor["constructorIndex"] == 0
            and constructor["numParams"] == inductive["numParams"]
            and recursor["all"] == [inductive_name]
            and recursor["numParams"] == inductive["numParams"]
            and recursor["numIndices"] == inductive["numIndices"]
            and recursor["numMotives"] == len(recursor["all"])
            and [rule["ctor"] for rule in recursor["rules"]] == [ctor_name]
            and recursor["rules"][0]["nfields"] == constructor["numFields"],
            f"Inductive/constructor/recursor relationship mismatch: {root}")
    for name in (inductive_name, ctor_name, rec_name):
        actual = [item["name"] for item in rows[name]["transitiveNames"]]
        _assert(actual == expected_transitive_names(name, rows),
                f"Transitive structural closure mismatch: {name}")
    structure_unit_names = sorted(
        name for name, row in rows.items() if row["commandUnit"] == family["structure_unit"])
    _assert(structure_unit_names == sorted(family["units"][0]["graph_names"]),
            f"Atomic structure graph CI coverage differs: {root}")
    return {
        "family_root": root,
        "rows": len(rows),
        "inductive": inductive_name,
        "constructor": ctor_name,
        "recursor": rec_name,
        "constructor_fields": constructor["numFields"],
        "recursor_rules": len(recursor["rules"]),
        "recursor_rule_rhs_complete": True,
        "atomic_graph_ci_coverage_exact": True,
        "transitive_names_and_actual_module_owners_checked": True,
    }


def compare_rows(source: dict[str, Any], generated: dict[str, Any],
                 source_module: str, generated_module: str) -> None:
    name = source["sourceName"]
    _assert(generated["sourceName"] == name and generated["resolvedName"] == name,
            f"Generated structural Name differs: {name}")
    _assert(source["sourceModule"] == source_module and generated["sourceModule"] == generated_module,
            f"Structural source/generated module owner differs: {name}")
    for key in ("schemaVersion", "kernelMetadataSchema", "declGraphSha256",
                "declGraphRowSha256", "graphKind", "envKind", "ownerKind", "ownerId",
                "commandUnit", "familyRoot", "closedType", "closedValue", "axioms"):
        _assert(source[key] == generated[key], f"Structural row field differs: {name}: {key}")
    source_levels, generated_levels = source["levelParams"], generated["levelParams"]
    _assert(canonical_expr(source["type"], source_levels)
            == canonical_expr(generated["type"], generated_levels),
            f"Structural kernel type differs: {name}")
    if source["value"] is None or generated["value"] is None:
        _assert(source["value"] is generated["value"], f"Structural value presence differs: {name}")
    else:
        _assert(canonical_expr(source["value"], source_levels)
                == canonical_expr(generated["value"], generated_levels),
                f"Structural definition value differs: {name}")
    source_metadata = copy.deepcopy(source["kindMetadata"])
    generated_metadata = copy.deepcopy(generated["kindMetadata"])
    if source["graphKind"] == "rec":
        for rule in source_metadata["rules"]:
            rule["rhs"] = canonical_expr(rule["rhs"], source_levels)
        for rule in generated_metadata["rules"]:
            rule["rhs"] = canonical_expr(rule["rhs"], generated_levels)
    _assert(source_metadata == generated_metadata,
            f"Complete structural ConstantInfo metadata differs: {name}")
    for key in ("familyReferences", "transitiveNames"):
        old = [{**item, "module": source_module} for item in source[key]]
        new = [{**item, "module": source_module if item["module"] == generated_module else item["module"]}
               for item in generated[key]]
        _assert(old == new, f"Structural reference/module-owner evidence differs: {name}: {key}")


def negative_fixture_results() -> dict[str, bool]:
    """Run incomplete rows through the same validator used for certificates."""
    graph_sha = "g" * 64
    row_sha = "r" * 64
    graph = {
        "X": {"kind": "inductive", "module": "M", "_row_sha256": "i" * 64},
        "X.mk": {"kind": "ctor", "module": "M", "_row_sha256": "c" * 64},
        "X.rec": {"kind": "rec", "module": "M", "_row_sha256": row_sha},
    }
    request = {
        "source_name": "X.rec", "source_module": "M", "graph_kind": "rec",
        "decl_graph_sha256": graph_sha, "decl_graph_row_sha256": row_sha,
        "owner_kind": "inline", "owner_id": "M:0", "command_unit": "M:0",
        "family_root": "X",
    }
    owner = {**request}
    base_row = {
        "schemaVersion": 2,
        "kernelMetadataSchema": KERNEL_METADATA_SCHEMA,
        "sourceName": "X.rec", "resolvedName": "X.rec", "sourceModule": "M",
        "declGraphSha256": graph_sha, "declGraphRowSha256": row_sha,
        "graphKind": "rec", "envKind": "rec", "ownerKind": "inline",
        "ownerId": "M:0", "commandUnit": "M:0", "familyRoot": "X",
        "levelParams": [], "closedType": True, "closedValue": None,
        "type": ["const", "X", []], "value": None, "axioms": [],
        "kindMetadata": {
            "all": ["X"], "numParams": 0, "numIndices": 0, "numMotives": 1,
            "numMinors": 1, "rules": [{"ctor": "X.mk", "nfields": 0,
                                          "rhs": ["const", "X.mk", []]}],
            "supportsK": False, "isUnsafe": False,
        },
        "familyReferences": [
            {"name": "X", "module": "M", "envKind": "inductive"},
            {"name": "X.mk", "module": "M", "envKind": "ctor"},
        ],
        "transitiveNames": [
            {"name": "X", "module": "M", "envKind": "inductive"},
            {"name": "X.mk", "module": "M", "envKind": "ctor"},
            {"name": "X.rec", "module": "M", "envKind": "rec"},
        ],
    }

    def rejects(mutator) -> bool:
        row = copy.deepcopy(base_row)
        mutator(row)
        try:
            validate_row_basic(row, request, owner, graph, graph_sha)
            return False
        except (KeyError, TypeError, ValueError):
            return True

    return {
        "type_only_rejected": rejects(lambda row: row.__setitem__("kindMetadata", {})),
        "missing_rules_rejected": rejects(lambda row: row["kindMetadata"].pop("rules")),
        "missing_rule_nfields_rejected": rejects(lambda row: row["kindMetadata"]["rules"][0].pop("nfields")),
        "missing_rule_rhs_rejected": rejects(lambda row: row["kindMetadata"]["rules"][0].pop("rhs")),
        "null_rule_rhs_rejected": rejects(lambda row: row["kindMetadata"]["rules"][0].__setitem__("rhs", None)),
    }


def canonical_row_sha256(row: dict[str, Any]) -> str:
    import hashlib
    return hashlib.sha256(json.dumps(
        row, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")).hexdigest()
