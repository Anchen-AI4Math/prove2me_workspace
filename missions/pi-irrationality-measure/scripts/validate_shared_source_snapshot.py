#!/usr/bin/env python3
"""Validate shared original-source snapshot shards without invoking Lean."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from typing import Any


TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parent.parent
VERIFICATION = TASK / "verification"
CORE = VERIFICATION / "SharedSourceSnapshotCore.inc"
RUNTIME = VERIFICATION / "lean-runtime.json"
DECL_GRAPH = VERIFICATION / "decl_graph.jsonl"
SOURCE_MANIFEST = TASK / "source" / "manifest.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}
FULL_AST_INVENTORIES = [
    VERIFICATION / "ast-unit-inventory.json",
    VERIFICATION / "ast-scope-inventory.json",
    VERIFICATION / "ast-import-inventory.json",
    VERIFICATION / "ast-wrapper-inventory.json",
]

ROW_KEYS = {
    "schemaVersion", "sourceName", "sourceModule", "declGraphSha256",
    "declGraphRowSha256", "graphKind", "envKind", "ownerKind", "ownerId",
    "commandUnit", "levelParams", "closedType", "closedValue", "type",
    "value", "axioms", "kindMetadata",
}
REQUEST_KEYS = {
    "source_name", "source_module", "graph_kind", "decl_graph_sha256",
    "decl_graph_row_sha256", "owner_kind", "owner_id", "command_unit",
}


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def read_json(path: Path, label: str) -> Any:
    if not path.is_file():
        raise ValueError(f"Missing {label}: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def task_path(relative: str, label: str) -> Path:
    path = (TASK / relative).resolve()
    if not path.is_relative_to(TASK) or not path.is_file():
        raise ValueError(f"{label} is not a task file: {relative}")
    return path


def workspace_path(relative: str, label: str) -> Path:
    path = (WORKSPACE / relative).resolve()
    if not path.is_relative_to(WORKSPACE) or not path.is_file():
        raise ValueError(f"{label} is not a workspace file: {relative}")
    return path


def task_relative(path: Path) -> str:
    return path.resolve().relative_to(TASK).as_posix()


def ast_module_entries(modules: Any, label: str) -> list[tuple[str, dict[str, Any]]]:
    if isinstance(modules, dict):
        entries = [(key, value) for key, value in modules.items() if isinstance(key, str) and isinstance(value, dict)]
    elif isinstance(modules, list):
        entries = []
        for row in modules:
            if not isinstance(row, dict):
                continue
            name = row.get("module")
            if not isinstance(name, str):
                source = row.get("source")
                if isinstance(source, str) and source.endswith(".lean"):
                    name = source[:-5].replace("/", ".")
            if isinstance(name, str):
                entries.append((name, row))
    else:
        raise ValueError(f"AST inventory modules have invalid shape: {label}")
    names = [name for name, _ in entries]
    if len(names) != len(set(names)):
        raise ValueError(f"AST inventory repeats modules: {label}")
    return entries


def workspace_relative(path: Path) -> str:
    return path.resolve().relative_to(WORKSPACE).as_posix()


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def request_lean(record: dict[str, Any]) -> str:
    fields = [
        ("sourceName", record["source_name"]),
        ("expectedModule", record["source_module"]),
        ("graphKind", record["graph_kind"]),
        ("declGraphSha256", record["decl_graph_sha256"]),
        ("declGraphRowSha256", record["decl_graph_row_sha256"]),
        ("ownerKind", record["owner_kind"]),
        ("ownerId", record["owner_id"]),
        ("commandUnit", record["command_unit"]),
    ]
    body = ",\n      ".join(f"{key} := {lean_string(value)}" for key, value in fields)
    return "    {\n      " + body + "\n    }"


def expected_lean(core: str, requests: list[dict[str, Any]], output: str) -> bytes:
    request_text = ",\n".join(request_lean(record) for record in requests)
    text = (
        "import Lean\n"
        "import OAI.NumberTheory.PiExponent.Main\n\n"
        + core.rstrip()
        + "\n\nopen PiExponentSharedSourceSnapshot\n\n"
        + "def sharedSourceRequests : Array SourceRequest := #[\n"
        + request_text
        + "\n  ]\n\n"
        + "run_meta do\n"
        + f"  exportSourceSnapshotJsonl sharedSourceRequests {lean_string(output)}\n"
    )
    return text.encode("utf-8")


def load_graph() -> tuple[dict[str, dict[str, Any]], str]:
    raw = DECL_GRAPH.read_bytes()
    graph_sha = sha_bytes(raw)
    result: dict[str, dict[str, Any]] = {}
    for line_number, raw_line in enumerate(raw.splitlines(), 1):
        if not raw_line.strip():
            continue
        row = json.loads(raw_line)
        name = row["name"]
        if name in result:
            raise ValueError(f"Duplicate decl_graph name: {name}")
        row["_line_number"] = line_number
        row["_row_sha256"] = sha_bytes(raw_line)
        result[name] = row
    return result, graph_sha


def unit_index(plan: dict[str, Any]) -> dict[str, dict[str, Any]]:
    units = plan.get("units")
    if not isinstance(units, list):
        raise ValueError("Plan has no units array")
    result: dict[str, dict[str, Any]] = {}
    for unit in units:
        uid = unit.get("id") if isinstance(unit, dict) else None
        if not isinstance(uid, str) or uid in result:
            raise ValueError("Invalid or duplicate unit id")
        result[uid] = unit
    return result


def expected_owners(
    unit_plan: dict[str, Any], artifact_plan: dict[str, Any], graph: dict[str, dict[str, Any]]
) -> dict[str, dict[str, str]]:
    units = unit_index(unit_plan)
    owners: dict[str, dict[str, str]] = {}

    def add(name: str, uid: str, owner_kind: str, owner_id: str) -> None:
        if name in owners:
            raise ValueError(f"Multiple plan owners for {name}")
        unit = units[uid]
        row = graph.get(name)
        if row is None or row.get("module") != unit.get("module"):
            raise ValueError(f"Plan/graph module mismatch for {name}")
        if row.get("kind") not in set(unit.get("graph_kinds", [])):
            raise ValueError(f"Plan/graph kind mismatch for {name}")
        owners[name] = {
            "source_name": name,
            "source_module": row["module"],
            "source_sha256": unit["source_sha256"],
            "graph_kind": row["kind"],
            "owner_kind": owner_kind,
            "owner_id": owner_id,
            "command_unit": uid,
        }

    bundles = artifact_plan.get("definition_bundles")
    nodes = artifact_plan.get("nodes")
    if not isinstance(bundles, dict) or not isinstance(nodes, dict):
        raise ValueError("Artifact plan lacks definition_bundles or nodes")
    for bundle_id, bundle in bundles.items():
        for uid in bundle.get("units", []):
            unit = units.get(uid)
            if unit is None or unit.get("category") not in {"definition", "definition_embedded"}:
                raise ValueError(f"Invalid definition owner unit: {uid}")
            for name in unit.get("graph_names", []):
                add(name, uid, "definition_bundle", bundle_id)
    for node_id, node in nodes.items():
        unit = units.get(node_id)
        name = node.get("theorem_name_before_platform_renames") if isinstance(node, dict) else None
        if unit is None or unit.get("category") != "node" or name not in unit.get("graph_names", []):
            raise ValueError(f"Invalid node owner: {node_id}")
        add(name, node_id, "node", node_id)
    return owners


def expected_complete_source_owners(
    unit_plan: dict[str, Any], graph: dict[str, dict[str, Any]]
) -> dict[str, dict[str, Any]]:
    """Bind each original source Name to its unique exact AST command owner."""
    units = unit_index(unit_plan)
    if len(units) != 5786:
        raise ValueError(f"Complete source plan must contain 5786 command units, got {len(units)}")
    owners: dict[str, dict[str, Any]] = {}
    categories = {"definition", "definition_embedded", "inline", "node"}
    for uid, unit in sorted(units.items()):
        category = unit.get("category")
        names = unit.get("graph_names")
        kinds = unit.get("graph_kinds")
        if (category not in categories or not isinstance(names, list) or not names
                or not isinstance(kinds, list) or not all(isinstance(k, str) for k in kinds)
                or len(names) != len(set(names))):
            raise ValueError(f"Invalid complete-source AST command unit: {uid}")
        if unit.get("id") != uid or not isinstance(unit.get("module"), str):
            raise ValueError(f"Invalid exact AST owner identity: {uid}")
        private_token = unit.get("privateTok")
        start = unit.get("start")
        end = unit.get("end")
        if (not isinstance(unit.get("source_sha256"), str)
                or not isinstance(start, dict) or not isinstance(start.get("offset"), int)
                or not isinstance(end, dict) or not isinstance(end.get("offset"), int)
                or start["offset"] >= end["offset"]):
            raise ValueError(f"AST unit lacks source hash or exact byte span: {uid}")
        for name in names:
            row = graph.get(name)
            if row is None or row.get("module") != unit["module"] or row.get("kind") not in kinds:
                raise ValueError(f"AST owner/decl_graph module or kind mismatch: {name}")
            private_name = name.startswith("_private.")
            if private_name != (private_token is not None):
                raise ValueError(f"Private graph name and AST private token disagree: {name}")
            if name in owners:
                raise ValueError(f"Source declaration has multiple exact AST owners: {name}")
            owners[name] = {
                "source_name": name,
                "source_module": unit["module"],
                "source_sha256": unit["source_sha256"],
                "graph_kind": row["kind"],
                "owner_kind": category,
                "owner_id": uid,
                "command_unit": uid,
                "source_category": category,
                "source_private": private_name,
                "source_name_resolution": (
                    "exact-graph-Name.toString-private" if private_name
                    else "exact-graph-Name.toString-public"
                ),
                "unit_name_text": unit.get("nameText"),
                "unit_start_offset": start["offset"],
                "unit_end_offset": end["offset"],
            }
    if len(owners) != 6148:
        raise ValueError(f"Complete source plan must cover 6148 unique graph names, got {len(owners)}")
    return owners


def complete_source_coverage_qa(unit_plan: dict[str, Any], owners: dict[str, Any]) -> dict[str, Any]:
    names = set(owners)
    root_path = VERIFICATION.parent / "verification" / "provider-plans" / "all-shared-public" / "provider-roots.jsonl"
    root_rows = [json.loads(line) for line in root_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    root_names = [decl["name"] for row in root_rows for decl in row.get("interface", [])
                  if decl.get("is_private") is False and isinstance(decl.get("name"), str)]
    if len(set(root_names)) != 357 or not set(root_names).issubset(names):
        raise ValueError("Complete source owner catalog misses one or more of the 357 shared roots")
    variant_dir = VERIFICATION / "provider-plans" / "all-shared-public"
    variant_units = unit_index(read_json(variant_dir / "platform-unit-plan-provider-variant.json", "provider variant unit plan"))
    variant_artifact = read_json(variant_dir / "platform-artifact-plan-provider-variant.json", "provider variant artifact plan")
    bundles = variant_artifact.get("definition_bundles")
    if not isinstance(bundles, dict):
        raise ValueError("Provider variant artifact plan has no definition bundles")
    provider_names: set[str] = set()
    for bundle in bundles.values():
        for uid in bundle.get("units", []):
            unit = variant_units.get(uid)
            if unit is None:
                raise ValueError(f"Provider variant bundle references unknown unit {uid}")
            provider_names.update(unit.get("graph_names", []))
    if len(provider_names) != 4867 or not provider_names.issubset(names):
        raise ValueError("Complete source owner catalog misses one or more of the 4867 provider names")
    staged_dir = VERIFICATION / "providers-complete-preview" / "all-shared-safe-leaves" / "Definitions"
    manifests = sorted(staged_dir.glob("*.manifest.json"))
    unit_lookup = unit_index(read_json(VERIFICATION / "platform-unit-plan-preview.json", "base unit plan"))
    staged_names: list[str] = []
    for path in manifests:
        manifest = read_json(path, "staged safe-provider manifest")
        for uid in manifest.get("selected_units", []):
            if uid not in unit_lookup:
                raise ValueError(f"Staged safe provider references unknown unit {uid}")
            staged_names.extend(unit_lookup[uid].get("graph_names", []))
    if (len(manifests) != 29 or len(staged_names) != 174 or len(set(staged_names)) != 174
            or not set(staged_names).issubset(names)):
        raise ValueError("Complete source owner catalog misses staged safe-provider declarations")
    return {
        "all_shared_public_roots": {
            "path": task_relative(root_path), "sha256": sha(root_path),
            "expected": 357, "actual": len(set(root_names)), "all_included": True,
        },
        "provider_variant_definition_names": {
            "unit_plan": task_relative(variant_dir / "platform-unit-plan-provider-variant.json"),
            "unit_plan_sha256": sha(variant_dir / "platform-unit-plan-provider-variant.json"),
            "artifact_plan": task_relative(variant_dir / "platform-artifact-plan-provider-variant.json"),
            "artifact_plan_sha256": sha(variant_dir / "platform-artifact-plan-provider-variant.json"),
            "expected": 4867, "actual": len(provider_names), "all_included": True,
        },
        "staged_safe_provider_bundles": {
            "bundle_count": len(manifests), "declaration_count": len(staged_names),
            "unique_declaration_count": len(set(staged_names)), "all_included": True,
            "manifests": [{"path": task_relative(path), "sha256": sha(path)} for path in manifests],
        },
    }


def validate_manifest_inputs(manifest: dict[str, Any]) -> dict[str, str]:
    inputs = manifest.get("input_hashes")
    if not isinstance(inputs, dict) or not inputs:
        raise ValueError("Snapshot manifest has no input_hashes")
    checked: dict[str, str] = {}
    for relative, expected in sorted(inputs.items()):
        path = task_path(relative, "manifest input")
        actual = sha(path)
        if actual != expected:
            raise ValueError(f"Manifest input hash changed: {relative}")
        checked[relative] = actual
    return checked


def validate_runtime(manifest: dict[str, Any], preflight: dict[str, Any]) -> dict[str, Any]:
    runtime = read_json(RUNTIME, "Lean runtime")
    runtime_sha = sha(RUNTIME)
    if manifest.get("runtime_sha256") != runtime_sha:
        raise ValueError("Manifest runtime hash changed")
    if (preflight.get("runtime_sha256") != runtime_sha
            or preflight.get("runtime_sha256_after") != runtime_sha
            or preflight.get("runtime_unchanged") is not True):
        raise ValueError("Preflight runtime certificate is stale")
    executable = Path(runtime.get("executable", "")).resolve()
    if not executable.is_file() or sha(executable) != runtime.get("executable_sha256"):
        raise ValueError("Pinned Lean executable changed")
    if (preflight.get("lean_executable_sha256") != runtime["executable_sha256"]
            or preflight.get("lean_executable_sha256_after") != runtime["executable_sha256"]):
        raise ValueError("Preflight Lean executable certificate is stale")
    pins = runtime.get("project_hashes")
    if not isinstance(pins, dict) or not pins:
        raise ValueError("Runtime has no project hashes")
    for relative, expected in pins.items():
        if sha(workspace_path(relative, "runtime project pin")) != expected:
            raise ValueError(f"Runtime project pin changed: {relative}")
        for key in ("runtime_project_pins", "runtime_project_pins_after"):
            evidence = preflight.get(key, {}).get(relative, {})
            if evidence.get("matches") is not True or evidence.get("actual_sha256") != expected:
                raise ValueError(f"Preflight runtime project pin is stale: {relative}")
    return {
        "runtime_sha256": runtime_sha,
        "lean_executable_sha256": runtime["executable_sha256"],
        "project_hashes": pins,
    }


def validate_preflight(
    lean_path: Path, manifest_path: Path, manifest: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, Any]]:
    path = lean_path.with_suffix(lean_path.suffix + ".preflight.json")
    preflight = read_json(path, "Root staged preflight")
    lean_sha = sha(lean_path)
    manifest_sha = sha(manifest_path)
    if not all([
        preflight.get("success") is True,
        preflight.get("exit_code") == 0,
        preflight.get("timed_out") is False,
        preflight.get("source_unchanged") is True,
        preflight.get("manifest_unchanged") is True,
        preflight.get("source_certificate_stable") is True,
        preflight.get("input_certificates_stable") is True,
        preflight.get("dependencies_stable_during_compile") is True,
    ]):
        raise ValueError(f"Preflight did not pass strict stability gates: {path}")
    seconds = preflight.get("seconds")
    timeout = preflight.get("timeout_seconds")
    if not isinstance(seconds, (int, float)) or not 0 < seconds <= timeout <= 300:
        raise ValueError("Preflight exceeded the 300-second file budget")
    if (preflight.get("source_sha256_before") != lean_sha
            or preflight.get("source_sha256_after") != lean_sha):
        raise ValueError("Preflight source hash changed")
    if (preflight.get("manifest_sha256_before") != manifest_sha
            or preflight.get("manifest_sha256_after") != manifest_sha):
        raise ValueError("Preflight manifest hash changed")
    if preflight.get("imports") != manifest.get("imports"):
        raise ValueError("Preflight imports differ from the shard manifest")
    expected_inputs = manifest["input_hashes"]
    for key in ("manifest_input_hashes_before", "manifest_input_hashes_after"):
        evidence = preflight.get(key)
        if not isinstance(evidence, dict) or set(evidence) != set(expected_inputs):
            raise ValueError(f"Preflight input set differs: {key}")
        for relative, expected in expected_inputs.items():
            item = evidence[relative]
            if (item.get("matches") is not True or item.get("expected_sha256") != expected
                    or item.get("actual_sha256") != expected):
                raise ValueError(f"Preflight input certificate differs: {relative}")
    for dependency in preflight.get("dependency_oleans", []):
        dep_path = Path(dependency["path"])
        if (not dep_path.is_file() or sha(dep_path) != dependency.get("sha256_before")
                or dependency.get("sha256_after") != dependency.get("sha256_before")
                or dependency.get("stable_during_compile") is not True):
            raise ValueError(f"Imported OLean changed: {dep_path}")
    log_path = task_path(preflight["log"], "preflight log")
    log_sha = sha(log_path)
    if log_sha != preflight.get("log_sha256") or log_sha != preflight.get("stdout_and_stderr_sha256"):
        raise ValueError("Preflight log hash changed")
    runtime = validate_runtime(manifest, preflight)
    summary = {
        "path": task_relative(path),
        "sha256": sha(path),
        "seconds": seconds,
        "timeout_seconds": timeout,
        "exit_code": 0,
        "log": task_relative(log_path),
        "log_sha256": log_sha,
        "source_sha256": lean_sha,
        "manifest_sha256": manifest_sha,
        "dependency_oleans": len(preflight.get("dependency_oleans", [])),
    }
    return summary, runtime


def normalize_kernel(row: dict[str, Any], field: str) -> Any:
    params = row.get("levelParams")
    if not isinstance(params, list) or not all(isinstance(name, str) for name in params):
        raise ValueError(f"Invalid levelParams for {row.get('sourceName', row.get('name'))}")
    if len(params) != len(set(params)):
        raise ValueError(f"Repeated level parameter for {row.get('sourceName', row.get('name'))}")
    levels = {name: index for index, name in enumerate(params)}

    def walk(value: Any) -> Any:
        if not isinstance(value, list):
            return value
        if len(value) == 2 and value[0] == "param":
            if value[1] not in levels:
                raise ValueError(f"Unknown level parameter {value[1]}")
            return ["param", levels[value[1]]]
        return [walk(item) for item in value]

    return walk(row[field])


def forbidden_open_expr_tag(value: Any) -> str | None:
    if isinstance(value, list):
        if value and isinstance(value[0], str) and value[0] in {"fvar", "mvar"}:
            return value[0]
        for item in value:
            found = forbidden_open_expr_tag(item)
            if found:
                return found
    elif isinstance(value, dict):
        for item in value.values():
            found = forbidden_open_expr_tag(item)
            if found:
                return found
    return None


def validate_raw_sources(
    owner_rows: list[dict[str, Any]], source_manifest: dict[str, Any]
) -> list[dict[str, str]]:
    source_files = source_manifest.get("files")
    if not isinstance(source_files, dict):
        raise ValueError("Immutable source manifest has no files object")
    modules: dict[str, dict[str, str]] = {}
    for owner in owner_rows:
        module = owner["source_module"]
        port_path = task_path(owner["source_file"], "port raw source")
        expected_port = TASK / "port" / "lean" / Path(*module.split(".")).with_suffix(".lean")
        if port_path != expected_port.resolve():
            raise ValueError(f"Owner points at the wrong port raw source: {module}")
        port_sha = sha(port_path)
        if port_sha != owner["source_sha256"]:
            raise ValueError(f"Port raw source changed: {module}")
        source_key = "lean/" + "/".join(module.split(".")) + ".lean"
        source_record = source_files.get(source_key)
        original_path = TASK / "source" / source_key
        if not isinstance(source_record, dict) or not original_path.is_file():
            raise ValueError(f"Missing immutable raw source: {module}")
        original_sha = sha(original_path)
        if (original_sha != source_record.get("sha256")
                or original_path.stat().st_size != source_record.get("bytes")):
            raise ValueError(f"Immutable raw source changed: {module}")
        modules[module] = {
            "module": module,
            "port_source": task_relative(port_path),
            "port_source_sha256": port_sha,
            "immutable_source": task_relative(original_path),
            "immutable_source_sha256": original_sha,
        }
    return [modules[name] for name in sorted(modules)]


def validate_row(
    row: dict[str, Any], raw_line: bytes, request: dict[str, Any], owner: dict[str, str],
    graph: dict[str, dict[str, Any]], graph_sha: str
) -> dict[str, Any]:
    if set(row) != ROW_KEYS or set(request) != REQUEST_KEYS:
        raise ValueError(f"Unexpected row/request schema for {request.get('source_name')}")
    name = request["source_name"]
    if row["sourceName"] != name or owner["source_name"] != name:
        raise ValueError(f"Source name changed in shared IR: {name}")
    graph_row = graph.get(name)
    if graph_row is None:
        raise ValueError(f"Output name is absent from decl_graph: {name}")
    expected = {
        "source_module": graph_row["module"],
        "graph_kind": graph_row["kind"],
        "decl_graph_sha256": graph_sha,
        "decl_graph_row_sha256": graph_row["_row_sha256"],
        "owner_kind": owner["owner_kind"],
        "owner_id": owner["owner_id"],
        "command_unit": owner["command_unit"],
    }
    for key, value in expected.items():
        if request[key] != value:
            raise ValueError(f"Request mismatch for {name}: {key}")
    row_fields = {
        "source_module": "sourceModule", "graph_kind": "graphKind",
        "decl_graph_sha256": "declGraphSha256",
        "decl_graph_row_sha256": "declGraphRowSha256", "owner_kind": "ownerKind",
        "owner_id": "ownerId", "command_unit": "commandUnit",
    }
    for request_key, row_key in row_fields.items():
        if row[row_key] != request[request_key]:
            raise ValueError(f"Output/request mismatch for {name}: {row_key}")
    if row["envKind"] != row["graphKind"] or row["schemaVersion"] != 1:
        raise ValueError(f"Environment kind/schema mismatch for {name}")
    if row["closedType"] is not True or row["type"] is None:
        raise ValueError(f"Type closure missing for {name}")
    if forbidden_open_expr_tag(row["type"]):
        raise ValueError(f"Open variable tag remains in type for {name}")
    kind = row["graphKind"]
    if kind == "def":
        if row["closedValue"] is not True or row["value"] is None:
            raise ValueError(f"Definition value missing or open for {name}")
        if forbidden_open_expr_tag(row["value"]):
            raise ValueError(f"Open variable tag remains in value for {name}")
        if row["kindMetadata"].get("valueExported") is not True:
            raise ValueError(f"Definition metadata does not certify its value: {name}")
    elif kind == "theorem":
        if row["value"] is not None or row["closedValue"] is not None:
            raise ValueError(f"Theorem proof value was exported: {name}")
        if row["kindMetadata"] != {"proofValueExported": False}:
            raise ValueError(f"Theorem proof metadata is invalid: {name}")
    elif kind in {"inductive", "ctor", "rec"}:
        if row["value"] is not None or row["closedValue"] is not None or not row["kindMetadata"]:
            raise ValueError(f"Kernel declaration metadata/value policy failed: {name}")
    else:
        raise ValueError(f"Unsupported shared snapshot kind: {name}: {kind}")
    axioms = row["axioms"]
    if (not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms)
            or axioms != sorted(set(axioms)) or not set(axioms) <= STD3):
        raise ValueError(f"Non-Std3 or nondeterministic axiom list for {name}: {axioms}")
    normalize_kernel(row, "type")
    if row["value"] is not None:
        normalize_kernel(row, "value")
    return {
        "source_name": name,
        "module": row["sourceModule"],
        "kind": kind,
        "owner_kind": row["ownerKind"],
        "owner_id": row["ownerId"],
        "command_unit": row["commandUnit"],
        "jsonl_line_sha256": sha_bytes(raw_line),
        "canonical_row_sha256": sha_bytes(json.dumps(
            row, sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ).encode("utf-8")),
        "level_param_count": len(row["levelParams"]),
        "closed_type": True,
        "closed_value": row["closedValue"],
        "theorem_value_omitted": kind != "theorem" or row["value"] is None,
        "axioms": axioms,
        "std3_only": True,
    }


def certified_references() -> tuple[dict[str, dict[str, Any]], list[dict[str, Any]]]:
    references: dict[str, dict[str, Any]] = {}
    evidence: list[dict[str, Any]] = []
    definition_dirs = [
        VERIFICATION / "definition-validation" / "Def_OAI_NumberTheory_PiExponent_Analysis_Collision",
        VERIFICATION / "definition-validation" / "Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticCollision",
    ]
    for directory in definition_dirs:
        validation_path = directory / "validation.json"
        snapshot_path = directory / "original-definitions.json"
        prepare_path = directory / "prepare-record.json"
        validation = read_json(validation_path, "certified definition validation")
        snapshot = read_json(snapshot_path, "certified original definition snapshot")
        prepare = read_json(prepare_path, "definition prepare record")
        if not all([
            validation.get("validated") is True,
            validation.get("kernel_types_and_values_equal") is True,
            validation.get("standard_axioms_only") is True,
        ]):
            raise ValueError(f"Definition reference is not certified: {directory.name}")
        if (prepare.get("validation_sha256") != sha(validation_path)
                or validation.get("type_value_snapshots", {}).get("original-definitions.json") != sha(snapshot_path)
                or prepare.get("kernel_type_value_snapshots", {}).get("original-definitions.json") != sha(snapshot_path)):
            raise ValueError(f"Definition reference hash chain changed: {directory.name}")
        if validation.get("provided_names") != [row["name"] for row in snapshot]:
            raise ValueError(f"Definition reference name set changed: {directory.name}")
        for row in snapshot:
            references[row["name"]] = row
        evidence.append({
            "kind": "definition_bundle",
            "directory": task_relative(directory),
            "validation_sha256": sha(validation_path),
            "original_snapshot_sha256": sha(snapshot_path),
            "provided_names": validation["provided_names"],
        })

    node_dir = VERIFICATION / "nodes-preview" / "OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le"
    validation_path = node_dir / "validation.json"
    manifest_path = node_dir / "manifest.json"
    snapshot_path = node_dir / "original-type.json"
    validation = read_json(validation_path, "certified node validation")
    manifest = read_json(manifest_path, "certified node manifest")
    snapshot = read_json(snapshot_path, "certified original node snapshot")
    if not all([
        validation.get("validated") is True,
        validation.get("local_standalone_validated") is True,
        validation.get("kernel_types_equal") is True,
        validation.get("standard_axioms_only") is True,
        validation.get("only_universe_parameter_display_names_normalized") is True,
    ]):
        raise ValueError("Node reference is not certified")
    if (manifest.get("validation_sha256") != sha(validation_path)
            or validation.get("original_type_sha256") != sha(snapshot_path)):
        raise ValueError("Node reference hash chain changed")
    for row in snapshot:
        references[row["name"]] = row
    evidence.append({
        "kind": "node",
        "directory": task_relative(node_dir),
        "validation_sha256": sha(validation_path),
        "original_snapshot_sha256": sha(snapshot_path),
        "provided_names": [row["name"] for row in snapshot],
    })
    return references, evidence


def compare_references(
    rows: dict[str, dict[str, Any]], references: dict[str, dict[str, Any]]
) -> list[dict[str, Any]]:
    comparisons: list[dict[str, Any]] = []
    for name in sorted(set(rows) & set(references)):
        current = rows[name]
        reference = references[name]
        if len(current["levelParams"]) != len(reference["levelParams"]):
            raise ValueError(f"Certified reference level arity changed: {name}")
        if normalize_kernel(current, "type") != normalize_kernel(reference, "type"):
            raise ValueError(f"Certified reference type changed: {name}")
        fields = ["type"]
        if current["graphKind"] == "def":
            if normalize_kernel(current, "value") != normalize_kernel(reference, "value"):
                raise ValueError(f"Certified reference value changed: {name}")
            fields.append("value")
        elif current["graphKind"] == "theorem" and current["value"] is not None:
            raise ValueError(f"Shared theorem unexpectedly contains proof value: {name}")
        comparisons.append({
            "source_name": name,
            "fields_equal": fields,
            "normalization": "universe parameter display names only",
            "level_param_count_equal": True,
            "shared_theorem_value_is_none": current["graphKind"] != "theorem" or current["value"] is None,
        })
    expected_common = {
        "OAI.PiExponent.holomorphicError",
        "OAI.PiExponent.AnalyticCollision.exponentialMonomial",
        "OAI.PiExponent.AnalyticCollision.rowTest",
        "OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le",
    }
    if {item["source_name"] for item in comparisons} != expected_common:
        raise ValueError("Pilot/certified-reference intersection is incomplete")
    return comparisons


def validate_shard(
    manifest_path: Path, plan_owners: dict[str, dict[str, str]], graph: dict[str, dict[str, Any]],
    graph_sha: str, source_manifest: dict[str, Any], extraction_state: dict[str, Any],
    complete_source: bool = False
) -> tuple[dict[str, Any], dict[str, dict[str, Any]], list[dict[str, Any]]]:
    manifest = read_json(manifest_path, "snapshot shard manifest")
    lean_path = workspace_path(manifest["output"], "snapshot Lean source")
    if lean_path.with_suffix(".manifest.json") != manifest_path.resolve():
        raise ValueError("Manifest is not the sidecar of its Lean source")
    if sha(lean_path) != manifest.get("output_sha256"):
        raise ValueError("Snapshot Lean source changed")
    inputs = validate_manifest_inputs(manifest)
    request_path = task_path(manifest["request_manifest"], "request manifest")
    owner_path = task_path(manifest["owner_manifest"], "owner manifest")
    request_doc = read_json(request_path, "request manifest")
    owner_doc = read_json(owner_path, "owner manifest")
    lineage = owner_doc.get("lineage")
    if not isinstance(lineage, dict) or lineage.get("source_commit") != source_manifest.get("commit"):
        raise ValueError("Owner manifest source lineage differs from the immutable source manifest")
    name_maps = manifest.get("name_mapping_inputs")
    if complete_source:
        if name_maps is not None:
            raise ValueError("Complete-source certificate must not claim a platform rename dependency")
        if (manifest.get("source_only") is not True or manifest.get("source_version") != 875
                or manifest.get("certificate_class") != "complete-source-original-kernel-snapshot-only"):
            raise ValueError("Shard does not identify as the full original-source-only certificate")
        catalog_rel = manifest.get("owner_catalog")
        catalog_sha = manifest.get("owner_catalog_sha256")
        if (not isinstance(catalog_rel, str) or not isinstance(catalog_sha, str)
                or manifest.get("input_hashes", {}).get(catalog_rel) != catalog_sha
                or sha(task_path(catalog_rel, "complete-source owner catalog")) != catalog_sha):
            raise ValueError("Complete-source owner catalog hash chain is invalid")
        if (owner_doc.get("source_version") != 875 or owner_doc.get("owner_catalog") != catalog_rel
                or owner_doc.get("owner_catalog_sha256") != catalog_sha):
            raise ValueError("Shard owner manifest does not bind to the full 875 owner catalog")
    else:
        if not isinstance(name_maps, dict) or not name_maps:
            raise ValueError("Shard manifest has no pinned local-consumer name maps")
        for relative, expected in name_maps.items():
            if manifest["input_hashes"].get(relative) != expected or sha(task_path(relative, "name map")) != expected:
                raise ValueError(f"Pinned local-consumer name map changed: {relative}")
    if manifest.get("shared_ir_name_domain") != "original-source-names":
        raise ValueError("Shared IR does not declare its original source Name domain")
    requests = request_doc.get("requests")
    owner_rows = owner_doc.get("owners")
    if not isinstance(requests, list) or not isinstance(owner_rows, list):
        raise ValueError("Request/owner manifest has no rows")
    request_names = [row.get("source_name") for row in requests]
    owner_names = [row.get("source_name") for row in owner_rows]
    if (request_names != sorted(request_names) or request_names != owner_names
            or len(request_names) != len(set(request_names))
            or len(request_names) != manifest.get("expected_rows")):
        raise ValueError("Request/owner name set or order changed")
    for owner_row in owner_rows:
        planned = plan_owners.get(owner_row["source_name"])
        if planned is None:
            raise ValueError(f"Requested name is not owned by the plan: {owner_row['source_name']}")
        for key, expected in planned.items():
            if owner_row.get(key) != expected:
                raise ValueError(f"Owner manifest differs from plan: {owner_row['source_name']}: {key}")
        module_key = "/".join(owner_row["source_module"].split(".")) + ".lean"
        stage2 = extraction_state.get("stage2", {}).get(module_key)
        if not isinstance(stage2, dict):
            raise ValueError(f"Owner has no extraction-state facts: {owner_row['source_name']}")
        facts = workspace_path(owner_row["stage2_facts"], "owner Stage 2 facts")
        if (owner_row.get("stage2_facts_sha256") != stage2.get("facts_sha256")
                or workspace_relative(facts) != stage2.get("facts")
                or sha(facts) != stage2.get("facts_sha256")):
            raise ValueError(f"Owner Stage 2 facts differ from extraction-state: {owner_row['source_name']}")
    expected_source = expected_lean(CORE.read_text(encoding="utf-8"), requests, manifest["snapshot_jsonl"])
    if lean_path.read_bytes() != expected_source:
        raise ValueError("Staged Lean source is not the exact core/request composition")
    preflight, runtime = validate_preflight(lean_path, manifest_path, manifest)
    raw_sources = validate_raw_sources(owner_rows, source_manifest)
    output_path = workspace_path(manifest["snapshot_jsonl"], "snapshot JSONL")
    raw_lines = [line for line in output_path.read_bytes().splitlines() if line.strip()]
    if len(raw_lines) != len(requests):
        raise ValueError("Snapshot JSONL row count differs from requests")
    rows: dict[str, dict[str, Any]] = {}
    row_evidence: list[dict[str, Any]] = []
    for raw_line, request in zip(raw_lines, requests, strict=True):
        row = json.loads(raw_line)
        name = request["source_name"]
        if name in rows:
            raise ValueError(f"Duplicate JSONL source name: {name}")
        evidence = validate_row(row, raw_line, request, plan_owners[name], graph, graph_sha)
        rows[name] = row
        row_evidence.append(evidence)
    shard = {
        "manifest": task_relative(manifest_path),
        "manifest_sha256": sha(manifest_path),
        "lean_source": task_relative(lean_path),
        "lean_source_sha256": sha(lean_path),
        "request_manifest": task_relative(request_path),
        "request_manifest_sha256": sha(request_path),
        "owner_manifest": task_relative(owner_path),
        "owner_manifest_sha256": sha(owner_path),
        "jsonl": task_relative(output_path),
        "jsonl_sha256": sha(output_path),
        "rows": len(rows),
        "manifest_inputs": inputs,
        "raw_sources": raw_sources,
        "preflight": preflight,
        "runtime": runtime,
        "row_certificates": row_evidence,
    }
    return shard, rows, owner_rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--pilot", action="store_true", help="Validate preview pilot shards as non-final evidence")
    mode.add_argument("--final", action="store_true", help="Validate a complete set of final-plan shards")
    mode.add_argument("--complete-source", action="store_true", help="Validate all original-source rows from the complete provisional 875-module plan")
    args = parser.parse_args()
    pilot = args.pilot
    complete_source = args.complete_source
    mode_name = "pilot" if pilot else ("complete-source" if complete_source else "final")
    directory = VERIFICATION / "shared-source-snapshot" / mode_name
    pattern = "SharedSourceSnapshotPilot_*.manifest.json" if pilot else "SharedSourceSnapshot_*.manifest.json"
    manifests = sorted(directory.glob(pattern))
    if not manifests:
        raise ValueError(f"No shared snapshot manifests found in {directory}")
    unit_plan_path = VERIFICATION / ("platform-unit-plan-preview.json" if (pilot or complete_source) else "platform-unit-plan.json")
    artifact_plan_path = VERIFICATION / ("platform-artifact-plan-preview.json" if (pilot or complete_source) else "platform-artifact-plan.json")
    unit_plan = read_json(unit_plan_path, "unit plan")
    artifact_plan = read_json(artifact_plan_path, "artifact plan")
    extraction_state = read_json(VERIFICATION / "extraction-state.json", "extraction state")
    if complete_source:
        if not all([
            unit_plan.get("complete_extraction") is True,
            artifact_plan.get("complete_extraction") is True,
            unit_plan.get("ready_for_generation") is False,
            artifact_plan.get("ready_for_generation") is False,
            unit_plan.get("provisional") is True,
            artifact_plan.get("provisional") is True,
            unit_plan.get("source_declarations_pending_ast") == [],
            extraction_state.get("complete") is True,
            isinstance(extraction_state.get("stage2"), dict)
            and len(extraction_state["stage2"]) == 875,
        ]):
            raise ValueError("Complete-source requires complete provisional source plans, zero pending source AST owners, and 875 Stage 2 modules")
        expected_modules: set[str] | None = None
        ast_source_hashes: dict[str, str] = {}
        for inventory_path in FULL_AST_INVENTORIES:
            inventory = read_json(inventory_path, "complete AST inventory")
            modules = inventory.get("modules")
            if inventory.get("complete_extraction") is not True or not isinstance(modules, (list, dict)):
                raise ValueError(f"Full AST inventory is incomplete: {inventory_path.name}")
            module_entries = ast_module_entries(modules, inventory_path.name)
            names = {name for name, _ in module_entries}
            if len(names) != 875 or len(module_entries) != 875:
                raise ValueError(f"Full AST inventory does not cover 875 modules: {inventory_path.name}")
            if expected_modules is None:
                expected_modules = names
            elif names != expected_modules:
                raise ValueError(f"Full AST inventory module sets differ: {inventory_path.name}")
            if inventory_path.name == "ast-unit-inventory.json":
                for module, row in module_entries:
                    source_sha = row.get("source_sha256")
                    if not isinstance(source_sha, str):
                        raise ValueError("AST unit inventory lacks module source hashes")
                    ast_source_hashes[module] = source_sha
        stage2_modules = {key.removesuffix(".lean").replace("/", ".") for key in extraction_state["stage2"]}
        if expected_modules != stage2_modules:
            raise ValueError("AST inventory module set differs from complete Stage 2 module set")
        source_manifest = read_json(SOURCE_MANIFEST, "immutable source manifest")
        source_files = source_manifest.get("files")
        if not isinstance(source_files, dict) or len(source_files) != 875:
            raise ValueError("Immutable source manifest does not cover 875 source files")
        for relative, record in source_files.items():
            immutable_file = TASK / "source" / Path(*relative.split("/"))
            if (not isinstance(record, dict) or not immutable_file.is_file()
                    or sha(immutable_file) != record.get("sha256")
                    or immutable_file.stat().st_size != record.get("bytes")):
                raise ValueError(f"Immutable source file hash is stale: {relative}")
        validated_port = read_json(VERIFICATION / "validated-port-manifest.json", "validated port manifest")
        port_hashes = validated_port.get("port_files_sha256")
        if (validated_port.get("port_modules") != 875 or not isinstance(port_hashes, dict)
                or len(port_hashes) != 875
                or {key[:-5].replace("/", ".") for key in port_hashes if key.endswith(".lean")} != expected_modules):
            raise ValueError("Validated port manifest does not bind the exact complete 875 module set")
        for module in sorted(expected_modules or []):
            key = "/".join(module.split(".")) + ".lean"
            stage_record = extraction_state["stage2"].get(key)
            port_file = TASK / "port" / "lean" / Path(*module.split(".")).with_suffix(".lean")
            if not isinstance(stage_record, dict) or not port_file.is_file():
                raise ValueError(f"Missing complete-source module evidence: {module}")
            port_sha = sha(port_file)
            if port_sha != ast_source_hashes.get(module) or port_sha != port_hashes.get(key):
                raise ValueError(f"Full port bytes differ from AST/validated-port evidence: {module}")
            facts_file = workspace_path(stage_record.get("facts", ""), "complete-source Stage 2 facts")
            if sha(facts_file) != stage_record.get("facts_sha256"):
                raise ValueError(f"Full Stage 2 facts hash is stale: {module}")
    elif not pilot and not all([
        unit_plan.get("complete_extraction") is True,
        unit_plan.get("ready_for_generation") is True,
        artifact_plan.get("complete_extraction") is True,
        artifact_plan.get("ready_for_generation") is True,
        extraction_state.get("complete") is True,
    ]):
        raise ValueError("Final certificate requires frozen complete final plans and extraction facts")
    graph, graph_sha = load_graph()
    owners = (
        expected_complete_source_owners(unit_plan, graph)
        if complete_source else expected_owners(unit_plan, artifact_plan, graph)
    )
    source_manifest = read_json(SOURCE_MANIFEST, "immutable source manifest")
    validated_port_path = VERIFICATION / "validated-port-manifest.json"
    validated_port = read_json(validated_port_path, "validated port manifest")
    if (validated_port.get("source_commit") != source_manifest.get("commit")
            or validated_port.get("original_files_sha256_verified") in {None, False, 0}
            or validated_port.get("build", {}).get("exit_code") != 0):
        raise ValueError("Validated full-port lineage does not protect this source commit")
    all_rows: dict[str, dict[str, Any]] = {}
    all_owner_rows: list[dict[str, Any]] = []
    shards: list[dict[str, Any]] = []
    for manifest_path in manifests:
        manifest = read_json(manifest_path, "snapshot shard manifest")
        expected_mode = mode_name
        if manifest.get("mode") != expected_mode:
            raise ValueError(f"Shard mode mismatch: {manifest_path}")
        if pilot and (manifest.get("pilot_validated") is not False
                      or manifest.get("usable_as_final_source_certificate") is not False):
            raise ValueError("Pilot manifest may not claim final certificate status")
        shard, rows, owner_rows = validate_shard(
            manifest_path, owners, graph, graph_sha, source_manifest, extraction_state, complete_source
        )
        duplicate = set(all_rows) & set(rows)
        if duplicate:
            raise ValueError("Names occur in multiple shards: " + ", ".join(sorted(duplicate)))
        all_rows.update(rows)
        all_owner_rows.extend(owner_rows)
        shards.append(shard)
    if not pilot and set(all_rows) != set(owners):
        missing = sorted(set(owners) - set(all_rows))
        extra = sorted(set(all_rows) - set(owners))
        raise ValueError(f"Final shard coverage differs from frozen plans; missing={missing}, extra={extra}")

    complete_source_catalog: dict[str, Any] | None = None
    if complete_source:
        catalog_path = directory / "CompleteSource875.owners.json"
        complete_source_catalog = read_json(catalog_path, "complete-source owner catalog")
        expected_inventory_pins = [
            {"path": task_relative(path), "sha256": sha(path), "module_count": 875}
            for path in FULL_AST_INVENTORIES
        ]
        expected_readiness = {
            "unit_ready_for_generation": unit_plan.get("ready_for_generation"),
            "artifact_ready_for_generation": artifact_plan.get("ready_for_generation"),
            "unit_provisional": unit_plan.get("provisional"),
            "artifact_provisional": artifact_plan.get("provisional"),
        }
        expected_coverage_qa = complete_source_coverage_qa(unit_plan, owners)
        if (complete_source_catalog.get("artifact_kind") != "complete-original-source-owner-catalog"
                or complete_source_catalog.get("source_version") != 875
                or complete_source_catalog.get("source_module_count") != 875
                or complete_source_catalog.get("owner_unit_count") != 5786
                or complete_source_catalog.get("owner_count") != len(owners)
                or complete_source_catalog.get("unit_plan") != task_relative(unit_plan_path)
                or complete_source_catalog.get("unit_plan_sha256") != sha(unit_plan_path)
                or complete_source_catalog.get("artifact_plan") != task_relative(artifact_plan_path)
                or complete_source_catalog.get("artifact_plan_sha256") != sha(artifact_plan_path)
                or complete_source_catalog.get("decl_graph_sha256") != graph_sha
                or complete_source_catalog.get("ast_inventory") != expected_inventory_pins
                or complete_source_catalog.get("plan_readiness") != expected_readiness
                or complete_source_catalog.get("coverage_qa") != expected_coverage_qa
                or [row.get("source_name") for row in complete_source_catalog.get("owners", [])] != sorted(owners)):
            raise ValueError("Frozen complete-source owner catalog differs from the current complete plans")
        for owner_row in complete_source_catalog["owners"]:
            expected = owners.get(owner_row["source_name"])
            if expected is None or any(owner_row.get(key) != value for key, value in expected.items()):
                raise ValueError(f"Frozen complete-source owner row differs from plan: {owner_row.get('source_name')}")

    if pilot:
        references, reference_evidence = certified_references()
        comparisons = compare_references(all_rows, references)
    else:
        reference_evidence, comparisons = [], []
    root_name = "OAI.PiExponent.pi_eventual_lower_bound"
    root = all_rows.get(root_name)
    planned_root = owners.get(root_name)
    graph_root = graph.get(root_name)
    if pilot:
        if root is None or planned_root is None or graph_root is None:
            raise ValueError("Pilot lacks the Main lower-bound root")
        if not all([
            root["sourceName"] == root_name,
            root["sourceModule"] == "OAI.NumberTheory.PiExponent.Main",
            root["graphKind"] == "theorem",
            root["ownerKind"] == "node",
            root["ownerId"] == planned_root["owner_id"],
            graph_root["name"] == root_name,
            graph_root["module"] == root["sourceModule"],
            root_name in unit_plan.get("source_targets", []),
            root["value"] is None,
        ]):
            raise ValueError("Main root did not preserve its source-graph name/owner/type boundary")

    measured_seconds = [shard["preflight"]["seconds"] for shard in shards]
    report = {
        "schema_version": 1,
        "at_utc": datetime.now(timezone.utc).isoformat(),
        "mode": mode_name,
        "validated": True,
        "usable_as_final_source_certificate": not pilot and not complete_source,
        "source_only_original_kernel_certificate": complete_source,
        "platform_name_type_comparison_required": complete_source,
        "validation_scope": (
            "Six-row preview pilot only; it is not a final source certificate."
            if pilot else
            "Every unique original source Name owned by the frozen complete provisional 875-module plan; this certifies only original-source kernel rows, not platform closure or generated-provider equivalence."
            if complete_source else
            "Every unique original source Name owned by the frozen complete final artifact plans."
        ),
        "checks": {
            "manifest_inputs_current": True,
            "immutable_and_port_raw_sources_current": True,
            "decl_graph_and_per_row_graph_hashes_current": True,
            "request_owner_and_output_name_sets_exact": True,
            "staged_source_is_exact_core_request_composition": True,
            "runtime_and_preflight_evidence_current": True,
            "preflight_log_and_output_current": True,
            "modules_kinds_and_closed_terms_valid": True,
            "theorem_values_omitted": True,
            "standard_axioms_only": True,
        },
        "source_commit": source_manifest.get("commit"),
        "immutable_source_manifest_sha256": sha(SOURCE_MANIFEST),
        "validated_port_manifest_sha256": sha(validated_port_path),
        "decl_graph_sha256": graph_sha,
        "snapshot_core_sha256": sha(CORE),
        "validator_sha256": sha(Path(__file__).resolve()),
        "unit_plan": task_relative(unit_plan_path),
        "unit_plan_sha256": sha(unit_plan_path),
        "artifact_plan": task_relative(artifact_plan_path),
        "artifact_plan_sha256": sha(artifact_plan_path),
        "source_version": 875 if complete_source else None,
        "plan_readiness": None if not complete_source else complete_source_catalog.get("plan_readiness"),
        "owner_catalog": None if not complete_source else {
            "path": task_relative(directory / "CompleteSource875.owners.json"),
            "sha256": sha(directory / "CompleteSource875.owners.json"),
            "owner_count": len(owners),
        },
        "provided_names": sorted(all_rows),
        "row_count": len(all_rows),
        "shards": shards,
        "certified_reference_evidence": reference_evidence,
        "certified_reference_comparisons": comparisons,
        "comparison_normalization": "universe parameter display names only",
        "main_root": None if not pilot else {
            "source_graph_name": graph_root["name"],
            "expected_name": root_name,
            "output_name": root["sourceName"],
            "source_module": root["sourceModule"],
            "owner_kind": root["ownerKind"],
            "owner_id": root["ownerId"],
            "command_unit": root["commandUnit"],
            "original_name_preserved": True,
            "theorem_value_omitted": True,
            "type_canonical_sha256": sha_bytes(json.dumps(
                normalize_kernel(root, "type"), separators=(",", ":"), ensure_ascii=False
            ).encode("utf-8")),
        },
        "performance": {
            "measured_shards": len(shards),
            "measured_rows": len(all_rows),
            "preflight_seconds": measured_seconds,
            "max_preflight_seconds": max(measured_seconds),
            "measurement_scope": (
                "Each number covers Root staged preflight of the whole shard, including cold import "
                "of OAI.NumberTheory.PiExponent.Main, environment indexing, axiom collection, JSONL "
                "serialization, and certificate bookkeeping."
            ),
            "full_scale_claim": False,
            "reason": (
                "The 179.390855-second pilot measured six rows. It does not establish that thousands "
                "of rows fit in one 300-second process."
            ),
        },
        "final_certificate_design": {
            "plan_gate": (
                "--final requires complete_extraction=true and ready_for_generation=true in both "
                "final plans plus extraction-state.complete=true."
            ),
            "coverage_gate": "Every frozen-plan owner appears exactly once across all shards.",
            "per_row_gate": (
                "The same graph row hash, original name, module, kind, owner, closed type/value, "
                "theorem-value omission, and Std3 checks used by this pilot."
            ),
            "mapping_gate": (
                "The shared certificate remains in original source Names; each local consumer must "
                "validate its pinned rename map independently."
            ),
            "adaptive_budgeting": (
                "Measure representative shards with Root preflight. If a shard times out or approaches "
                "the 300-second cap, split its deterministic sorted name interval and retry both halves. "
                "Never delete, truncate, duplicate, reorder across the catalog, or alter row payloads."
            ),
            "per_shard_timeout_seconds": 300,
        },
    }
    output = directory / ("pilot-validation.json" if pilot else ("complete-source-validation.json" if complete_source else "final-validation.json"))
    temporary = output.with_name(output.name + ".tmp")
    temporary.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    temporary.replace(output)
    print(json.dumps({
        "validated": True,
        "mode": report["mode"],
        "usable_as_final_source_certificate": report["usable_as_final_source_certificate"],
        "source_only_original_kernel_certificate": complete_source,
        "rows": report["row_count"],
        "max_preflight_seconds": report["performance"]["max_preflight_seconds"],
        "output": task_relative(output),
        "output_sha256": sha(output),
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
