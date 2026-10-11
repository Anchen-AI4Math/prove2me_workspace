#!/usr/bin/env python3
"""Stage a shared, original-name source snapshot exporter without running Lean.

Preview mode is intentionally restricted to a subset selected with
--pilot-names or --limit.  Final mode consumes only complete final plans and
complete Stage 2 facts.  Each emitted Lean shard imports the immutable source
Main once and writes one JSON object per requested declaration.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parent.parent
VERIFICATION = TASK / "verification"
GENERATOR_SCRIPT = Path(__file__).resolve()
VALIDATOR_SCRIPT = VERIFICATION.parent / "scripts" / "validate_shared_source_snapshot.py"
CORE = VERIFICATION / "SharedSourceSnapshotCore.inc"
DECL_GRAPH = VERIFICATION / "decl_graph.jsonl"
EXTRACTION_STATE = VERIFICATION / "extraction-state.json"
RUNTIME = VERIFICATION / "lean-runtime.json"
VALIDATED_PORT = VERIFICATION / "validated-port-manifest.json"
SOURCE_MANIFEST = TASK / "source" / "manifest.json"
SOURCE_RENAMES = TASK / "platform" / "source-theorem-name-overrides.json"
DEPRIVATE_RENAMES = TASK / "platform" / "deprivate-name-overrides.json"
UPLOAD_ROUTE = TASK / "platform" / "upload-route.json"

PREVIEW_UNIT_PLAN = VERIFICATION / "platform-unit-plan-preview.json"
PREVIEW_ARTIFACT_PLAN = VERIFICATION / "platform-artifact-plan-preview.json"
FINAL_UNIT_PLAN = VERIFICATION / "platform-unit-plan.json"
FINAL_ARTIFACT_PLAN = VERIFICATION / "platform-artifact-plan.json"
FULL_AST_INVENTORIES = [
    VERIFICATION / "ast-unit-inventory.json",
    VERIFICATION / "ast-scope-inventory.json",
    VERIFICATION / "ast-import-inventory.json",
    VERIFICATION / "ast-wrapper-inventory.json",
]
ALL_SHARED_ROOTS = VERIFICATION.parent / "verification" / "provider-plans" / "all-shared-public" / "provider-roots.jsonl"
PROVIDER_VARIANT_UNIT_PLAN = VERIFICATION / "provider-plans" / "all-shared-public" / "platform-unit-plan-provider-variant.json"
PROVIDER_VARIANT_ARTIFACT_PLAN = VERIFICATION / "provider-plans" / "all-shared-public" / "platform-artifact-plan-provider-variant.json"
PROVIDER_VARIANT_MANIFEST = VERIFICATION / "provider-plans" / "all-shared-public" / "provider-plan-manifest.json"
COMPLETE_PREVIEW_BUNDLE_DIR = VERIFICATION / "providers-complete-preview" / "all-shared-safe-leaves" / "Definitions"

IMPORTS = ["Lean", "OAI.NumberTheory.PiExponent.Main"]
ALLOWED_GRAPH_KINDS = {"theorem", "def", "inductive", "ctor", "rec"}

PILOT_EXAMPLE = (
    "OAI.PiExponent.holomorphicError "
    "OAI.PiExponent.Collision.collisionRemainder "
    "OAI.PiExponent.AnalyticCollision.exponentialMonomial "
    "OAI.PiExponent.AnalyticCollision.rowTest "
    "OAI.PiExponent.Collision.sum_weight_ge_of_low_count_le "
    "OAI.PiExponent.pi_eventual_lower_bound"
)


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha_file(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def read_json(path: Path, label: str) -> dict[str, Any]:
    if not path.is_file():
        raise ValueError(f"Missing {label}: {path}")
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{label} must contain a JSON object: {path}")
    return value


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


def resolve_workspace_path(value: str, label: str) -> Path:
    path = (WORKSPACE / value).resolve()
    if not path.is_relative_to(WORKSPACE) or not path.is_file():
        raise ValueError(f"{label} is not a workspace file: {value}")
    return path


def lean_string(value: str) -> str:
    # JSON string escapes are accepted by Lean string literals for these
    # generated ASCII paths, names and hashes.
    return json.dumps(value, ensure_ascii=True)


def load_decl_graph() -> tuple[dict[str, dict[str, Any]], str]:
    raw = DECL_GRAPH.read_bytes()
    graph_sha = sha_bytes(raw)
    rows: dict[str, dict[str, Any]] = {}
    for line_number, raw_line in enumerate(raw.splitlines(), 1):
        if not raw_line.strip():
            continue
        row = json.loads(raw_line)
        name = row.get("name")
        if not isinstance(name, str) or not name:
            raise ValueError(f"decl_graph line {line_number} has no declaration name")
        if name in rows:
            raise ValueError(f"Duplicate declaration in decl_graph: {name}")
        row["_row_sha256"] = sha_bytes(raw_line)
        row["_line_number"] = line_number
        rows[name] = row
    return rows, graph_sha


def unit_index(plan: dict[str, Any]) -> dict[str, dict[str, Any]]:
    units = plan.get("units")
    if not isinstance(units, list):
        raise ValueError("Unit plan has no units array")
    result: dict[str, dict[str, Any]] = {}
    for unit in units:
        if not isinstance(unit, dict) or not isinstance(unit.get("id"), str):
            raise ValueError("Unit plan contains an invalid unit")
        uid = unit["id"]
        if uid in result:
            raise ValueError(f"Duplicate unit id: {uid}")
        result[uid] = unit
    return result


def graph_names_and_kinds(unit: dict[str, Any]) -> tuple[list[str], set[str]]:
    names = unit.get("graph_names")
    kinds = unit.get("graph_kinds")
    # graph_kinds is the set of kinds present in the command unit, rather than
    # a positionally aligned list.  Per-name kinds come from authoritative
    # decl_graph rows below.
    if not isinstance(names, list) or not isinstance(kinds, list):
        raise ValueError(f"Unit has invalid graph_names/graph_kinds: {unit.get('id')}")
    if not all(isinstance(name, str) for name in names) or not all(isinstance(kind, str) for kind in kinds):
        raise ValueError(f"Unit has a non-string graph name or kind: {unit.get('id')}")
    if len(names) != len(set(names)):
        raise ValueError(f"Unit repeats a graph name: {unit.get('id')}")
    return names, set(kinds)


def collect_owned_names(
    units: dict[str, dict[str, Any]], artifact_plan: dict[str, Any]
) -> dict[str, dict[str, Any]]:
    owners: dict[str, dict[str, Any]] = {}

    def add(name: str, unit: dict[str, Any], owner_kind: str, owner_id: str) -> None:
        uid = unit["id"]
        _, unit_kinds = graph_names_and_kinds(unit)
        record = {
            "source_name": name,
            "_unit_graph_kinds": sorted(unit_kinds),
            "source_module": unit.get("module"),
            "source_sha256": unit.get("source_sha256"),
            "command_unit": uid,
            "owner_kind": owner_kind,
            "owner_id": owner_id,
            "unit_category": unit.get("category"),
        }
        if name in owners:
            prior = owners[name]
            raise ValueError(
                f"Source declaration has multiple plan owners: {name}: "
                f"{prior['owner_kind']}:{prior['owner_id']} and {owner_kind}:{owner_id}"
            )
        owners[name] = record

    bundles = artifact_plan.get("definition_bundles")
    if not isinstance(bundles, dict):
        raise ValueError("Artifact plan has no definition_bundles object")
    for bundle_id, bundle in sorted(bundles.items()):
        if not isinstance(bundle, dict) or not isinstance(bundle.get("units"), list):
            raise ValueError(f"Invalid definition bundle: {bundle_id}")
        for uid in bundle["units"]:
            if uid not in units:
                raise ValueError(f"Definition bundle references an unknown unit: {uid}")
            unit = units[uid]
            if unit.get("category") not in {"definition", "definition_embedded"}:
                raise ValueError(f"Definition bundle references a non-definition unit: {uid}")
            names, _ = graph_names_and_kinds(unit)
            for name in names:
                add(name, unit, "definition_bundle", bundle_id)

    nodes = artifact_plan.get("nodes")
    if not isinstance(nodes, dict):
        raise ValueError("Artifact plan has no nodes object")
    for node_id, node in sorted(nodes.items()):
        if node_id not in units or not isinstance(node, dict):
            raise ValueError(f"Node references an unknown unit: {node_id}")
        unit = units[node_id]
        if unit.get("category") != "node":
            raise ValueError(f"Node artifact references a non-node unit: {node_id}")
        source_name = node.get("theorem_name_before_platform_renames")
        if not isinstance(source_name, str):
            raise ValueError(f"Node has no original theorem name: {node_id}")
        names, kinds = graph_names_and_kinds(unit)
        if source_name not in names or "theorem" not in kinds:
            raise ValueError(f"Node original theorem is not its theorem graph name: {node_id}")
        add(source_name, unit, "node", node_id)

    return owners


def collect_complete_source_owners(
    units: dict[str, dict[str, Any]], graph_rows: dict[str, dict[str, Any]]
) -> dict[str, dict[str, Any]]:
    """Use every original AST command unit as the unique source owner, including inline/private units."""
    owners: dict[str, dict[str, Any]] = {}
    for uid, unit in sorted(units.items()):
        names, unit_kinds = graph_names_and_kinds(unit)
        category = unit.get("category")
        if category not in {"definition", "definition_embedded", "inline", "node"}:
            raise ValueError(f"Unsupported complete-source command category {category}: {uid}")
        if unit.get("id") != uid or not isinstance(unit.get("module"), str):
            raise ValueError(f"Invalid complete-source AST owner identity: {uid}")
        if not unit.get("source_sha256"):
            raise ValueError(f"AST owner has no source hash: {uid}")
        for name in names:
            graph = graph_rows.get(name)
            if graph is None:
                raise ValueError(f"AST owner declaration is absent from decl_graph: {name}")
            if graph.get("module") != unit["module"] or graph.get("kind") not in unit_kinds:
                raise ValueError(f"AST owner and graph module/kind differ for {name}")
            if name in owners:
                raise ValueError(f"Complete-source declaration has multiple AST owners: {name}")
            private_name = name.startswith("_private.")
            if private_name != (unit.get("privateTok") is not None):
                raise ValueError(f"Private graph name and AST private token disagree: {name}")
            owners[name] = {
                "source_name": name,
                "_unit_graph_kinds": sorted(unit_kinds),
                "source_module": unit["module"],
                "source_sha256": unit["source_sha256"],
                "command_unit": uid,
                "owner_kind": category,
                "owner_id": uid,
                "source_category": category,
                "source_private": bool(unit.get("privateTok")),
                "source_name_resolution": "exact-graph-Name.toString-private" if private_name else "exact-graph-Name.toString-public",
                "unit_name_text": unit.get("nameText"),
                "unit_start_offset": (unit.get("start") or {}).get("offset"),
                "unit_end_offset": (unit.get("end") or {}).get("offset"),
            }
    if len(units) != 5786 or len(owners) != 6148:
        raise ValueError(f"Complete-source plan coverage mismatch: units={len(units)}, unique names={len(owners)}")
    return owners


def complete_source_coverage_qa(units: dict[str, dict[str, Any]], owners: dict[str, dict[str, Any]]) -> dict[str, Any]:
    names = set(owners)
    root_rows = [json.loads(line) for line in ALL_SHARED_ROOTS.read_text(encoding="utf-8").splitlines() if line.strip()]
    root_names = [decl["name"] for row in root_rows for decl in row.get("interface", [])
                  if decl.get("is_private") is False and isinstance(decl.get("name"), str)]
    if len(set(root_names)) != 357 or not set(root_names).issubset(names):
        raise ValueError("Complete-source owner set does not include all 357 all-shared public roots")

    variant_unit_doc = read_json(PROVIDER_VARIANT_UNIT_PLAN, "provider-variant unit plan")
    variant_artifact_doc = read_json(PROVIDER_VARIANT_ARTIFACT_PLAN, "provider-variant artifact plan")
    variant_units = unit_index(variant_unit_doc)
    definitions = variant_artifact_doc.get("definition_bundles")
    if not isinstance(definitions, dict):
        raise ValueError("Provider-variant artifact plan has no definition bundles")
    definition_names: set[str] = set()
    for bundle in definitions.values():
        for uid in bundle.get("units", []):
            unit = variant_units.get(uid)
            if unit is None:
                raise ValueError(f"Provider-variant definition bundle references unknown unit: {uid}")
            definition_names.update(unit.get("graph_names", []))
    if len(definition_names) != 4867 or not definition_names.issubset(names):
        raise ValueError("Complete-source owner set does not include all 4,867 provider-variant Definition names")

    bundle_manifests = sorted(COMPLETE_PREVIEW_BUNDLE_DIR.glob("*.manifest.json"))
    staged_names: list[str] = []
    for manifest_path in bundle_manifests:
        manifest = read_json(manifest_path, "staged safe-provider manifest")
        for uid in manifest.get("selected_units", []):
            unit = units.get(uid)
            if unit is None:
                raise ValueError(f"Staged safe-provider manifest references unknown source unit: {uid}")
            staged_names.extend(unit.get("graph_names", []))
    if len(bundle_manifests) != 29 or len(staged_names) != 174 or len(set(staged_names)) != 174:
        raise ValueError("Current staged-safe bundle set is not the expected 29 bundles/174 unique declarations")
    if not set(staged_names).issubset(names):
        raise ValueError("Complete-source owner set does not include all staged-safe provider declarations")
    return {
        "all_shared_public_roots": {
            "path": task_relative(ALL_SHARED_ROOTS), "sha256": sha_file(ALL_SHARED_ROOTS),
            "expected": 357, "actual": len(set(root_names)), "all_included": True,
        },
        "provider_variant_definition_names": {
            "unit_plan": task_relative(PROVIDER_VARIANT_UNIT_PLAN),
            "unit_plan_sha256": sha_file(PROVIDER_VARIANT_UNIT_PLAN),
            "artifact_plan": task_relative(PROVIDER_VARIANT_ARTIFACT_PLAN),
            "artifact_plan_sha256": sha_file(PROVIDER_VARIANT_ARTIFACT_PLAN),
            "expected": 4867, "actual": len(definition_names), "all_included": True,
        },
        "staged_safe_provider_bundles": {
            "bundle_count": len(bundle_manifests), "declaration_count": len(staged_names),
            "unique_declaration_count": len(set(staged_names)), "all_included": True,
            "manifests": [{"path": task_relative(p), "sha256": sha_file(p)} for p in bundle_manifests],
        },
    }


def source_file_for_module(module: str) -> Path:
    return TASK / "port" / "lean" / Path(*module.split(".")).with_suffix(".lean")


def stage2_key_for_module(module: str) -> str:
    return "/".join(module.split(".")) + ".lean"


def validate_owner(
    owner: dict[str, Any], graph_rows: dict[str, dict[str, Any]], graph_sha: str,
    extraction_state: dict[str, Any]
) -> dict[str, Any]:
    name = owner["source_name"]
    graph = graph_rows.get(name)
    if graph is None:
        raise ValueError(f"Planned declaration is absent from decl_graph: {name}")
    graph_kind = graph.get("kind")
    if graph_kind not in ALLOWED_GRAPH_KINDS:
        raise ValueError(f"Unsupported graph kind for shared snapshot: {name}: {graph_kind}")
    if graph_kind not in owner["_unit_graph_kinds"]:
        raise ValueError(f"Unit/graph kind mismatch for {name}")
    if graph.get("module") != owner["source_module"]:
        raise ValueError(f"Plan/graph module mismatch for {name}")
    module = owner["source_module"]
    if not isinstance(module, str) or not module:
        raise ValueError(f"Missing source module for {name}")
    source_file = source_file_for_module(module)
    if not source_file.is_file():
        raise ValueError(f"Missing port source for {name}: {source_file}")
    actual_source_sha = sha_file(source_file)
    if actual_source_sha != owner["source_sha256"]:
        raise ValueError(f"Unit source hash is stale for {name}")

    stage2 = extraction_state.get("stage2")
    stage_record = stage2.get(stage2_key_for_module(module)) if isinstance(stage2, dict) else None
    if not isinstance(stage_record, dict):
        raise ValueError(f"No Stage 2 facts for source module: {module}")
    facts_value = stage_record.get("facts")
    facts_sha = stage_record.get("facts_sha256")
    if not isinstance(facts_value, str) or not isinstance(facts_sha, str):
        raise ValueError(f"Incomplete Stage 2 facts record for source module: {module}")
    facts_file = resolve_workspace_path(facts_value, "Stage 2 facts")
    if sha_file(facts_file) != facts_sha:
        raise ValueError(f"Stage 2 facts hash is stale for source module: {module}")

    result = dict(owner)
    result.pop("_unit_graph_kinds")
    result.update({
        "graph_kind": graph_kind,
        "source_file": task_relative(source_file),
        "decl_graph_sha256": graph_sha,
        "decl_graph_row_sha256": graph["_row_sha256"],
        "decl_graph_line": graph["_line_number"],
        "stage2_facts": workspace_relative(facts_file),
        "stage2_facts_sha256": facts_sha,
    })
    return result


def require_final_inputs(
    unit_plan: dict[str, Any], artifact_plan: dict[str, Any], extraction_state: dict[str, Any]
) -> None:
    if unit_plan.get("complete_extraction") is not True or unit_plan.get("ready_for_generation") is not True:
        raise ValueError("Final unit plan is not complete and ready for generation")
    if artifact_plan.get("complete_extraction") is not True or artifact_plan.get("ready_for_generation") is not True:
        raise ValueError("Final artifact plan is not complete and ready for generation")
    if extraction_state.get("complete") is not True:
        raise ValueError("Stage 2 extraction-state is not complete")


def require_complete_source_inputs(
    unit_plan: dict[str, Any], artifact_plan: dict[str, Any], extraction_state: dict[str, Any]
) -> dict[str, Any]:
    """Gate source-only extraction on the full original inventory, not platform readiness."""
    if (unit_plan.get("complete_extraction") is not True
            or artifact_plan.get("complete_extraction") is not True
            or extraction_state.get("complete") is not True):
        raise ValueError("Complete-source mode requires complete source plans and Stage 2 facts")
    if not isinstance(unit_plan.get("provisional"), bool) or not isinstance(artifact_plan.get("provisional"), bool):
        raise ValueError("Complete-source mode requires explicit plan readiness/provisional flags")
    if unit_plan.get("ready_for_generation") is True or artifact_plan.get("ready_for_generation") is True:
        # Preserve the distinction: this mode is specifically source-only and must
        # not be mistaken for a platform-ready final artifact plan.
        raise ValueError("Use the ordinary final generator when platform plans are ready")
    if unit_plan.get("source_declarations_pending_ast") != []:
        raise ValueError("Complete-source mode has pending source declarations")

    stage2 = extraction_state.get("stage2")
    if not isinstance(stage2, dict) or len(stage2) != 875:
        raise ValueError("Complete-source mode requires exactly 875 Stage 2 module records")
    inventories: list[dict[str, Any]] = []
    expected_modules: set[str] | None = None
    source_hashes: dict[str, str] = {}
    for path in FULL_AST_INVENTORIES:
        doc = read_json(path, "full AST inventory")
        modules = doc.get("modules")
        if doc.get("complete_extraction") is not True or not isinstance(modules, (list, dict)):
            raise ValueError(f"AST inventory is not complete: {path.name}")
        module_entries = ast_module_entries(modules, path.name)
        module_names = {name for name, _ in module_entries}
        if len(module_names) != 875 or len(module_entries) != 875:
            raise ValueError(f"AST inventory does not contain exactly 875 unique modules: {path.name}")
        if expected_modules is None:
            expected_modules = module_names
        elif module_names != expected_modules:
            raise ValueError(f"AST inventory module coverage differs: {path.name}")
        inventories.append({"path": task_relative(path), "sha256": sha_file(path), "module_count": len(module_names)})
        if path.name == "ast-unit-inventory.json":
            for module, row in module_entries:
                source_sha = row.get("source_sha256")
                if not isinstance(source_sha, str):
                    raise ValueError("AST unit inventory lacks per-module source hashes")
                source_hashes[module] = source_sha
    assert expected_modules is not None
    stage2_modules = {key.removesuffix(".lean").replace("/", ".") for key in stage2}
    if stage2_modules != expected_modules:
        raise ValueError("Stage 2 module coverage differs from the complete 875-module AST inventories")

    source_manifest = read_json(SOURCE_MANIFEST, "source manifest")
    source_files = source_manifest.get("files")
    if not isinstance(source_files, dict):
        raise ValueError("Immutable source manifest has no files object")
    if len(source_files) != 875:
        raise ValueError("Immutable source manifest does not cover exactly 875 source files")
    validated_port = read_json(VALIDATED_PORT, "validated port manifest")
    port_hashes = validated_port.get("port_files_sha256")
    if (validated_port.get("port_modules") != 875 or not isinstance(port_hashes, dict)
            or len(port_hashes) != 875):
        raise ValueError("Validated port manifest does not cover exactly 875 Lean modules")
    if {key[:-5].replace("/", ".") for key in port_hashes if key.endswith(".lean")} != expected_modules:
        raise ValueError("Validated port module set differs from the complete AST inventory")
    for relative, record in source_files.items():
        original_path = TASK / "source" / Path(*relative.split("/"))
        if not original_path.is_file() or not isinstance(record, dict):
            raise ValueError(f"Missing immutable source file: {relative}")
        if sha_file(original_path) != record.get("sha256") or original_path.stat().st_size != record.get("bytes"):
            raise ValueError(f"Immutable source file hash is stale: {relative}")
    checked_sources: list[dict[str, str]] = []
    for module in sorted(expected_modules):
        key = stage2_key_for_module(module)
        stage_record = stage2.get(key)
        port_key = key
        source_file = source_file_for_module(module)
        if not isinstance(stage_record, dict) or not source_file.is_file():
            raise ValueError(f"Missing full source/Stage 2 record for {module}")
        actual_sha = sha_file(source_file)
        if actual_sha != source_hashes.get(module) or actual_sha != port_hashes.get(port_key):
            raise ValueError(f"Full source bytes differ from immutable/Stage 2 manifests: {module}")
        facts_value = stage_record.get("facts")
        facts_sha = stage_record.get("facts_sha256")
        if not isinstance(facts_value, str) or not isinstance(facts_sha, str):
            raise ValueError(f"Missing Stage 2 facts record for {module}")
        facts_path = resolve_workspace_path(facts_value, "Stage 2 facts")
        if sha_file(facts_path) != facts_sha:
            raise ValueError(f"Stage 2 facts hash is stale for {module}")
        checked_sources.append({"module": module, "source_sha256": actual_sha, "facts_sha256": facts_sha})
    return {
        "source_version": 875,
        "module_count": 875,
        "source_inventory": inventories,
        "source_file_rows": checked_sources,
        "unit_plan_ready_for_generation": unit_plan.get("ready_for_generation"),
        "artifact_plan_ready_for_generation": artifact_plan.get("ready_for_generation"),
        "unit_plan_provisional": unit_plan.get("provisional"),
        "artifact_plan_provisional": artifact_plan.get("provisional"),
    }


def validate_source_lineage() -> dict[str, Any]:
    source = read_json(SOURCE_MANIFEST, "source manifest")
    validated = read_json(VALIDATED_PORT, "validated port manifest")
    if validated.get("source_commit") != source.get("commit"):
        raise ValueError("Validated port and immutable source manifest commits differ")
    if validated.get("original_files_sha256_verified") in {None, False, 0}:
        raise ValueError("Validated port manifest does not certify original file hashes")
    build = validated.get("build")
    if not isinstance(build, dict) or build.get("exit_code") != 0:
        raise ValueError("Validated port manifest does not contain a successful full build")
    return {
        "source_repository": validated.get("source_repository"),
        "source_commit": validated.get("source_commit"),
        "mathlib_rev": validated.get("mathlib_rev"),
        "full_build_exit_code": 0,
        "original_files_sha256_verified": validated.get("original_files_sha256_verified"),
    }


def choose_subset(
    owners: dict[str, dict[str, Any]], pilot_names: list[str] | None, limit: int | None,
    preview: bool
) -> list[dict[str, Any]]:
    if preview and not pilot_names and limit is None:
        raise ValueError("--preview requires --pilot-names or --limit; preview output must stay a non-final subset")
    if not preview and (pilot_names or limit is not None):
        raise ValueError("Subset selectors are preview-only; final mode must cover every planned owner")
    if pilot_names and limit is not None:
        raise ValueError("Use either --pilot-names or --limit, not both")
    names = sorted(owners)
    if pilot_names:
        requested: list[str] = []
        for item in pilot_names:
            requested.extend(part for part in item.split(",") if part)
        missing = sorted(set(requested) - set(owners))
        if missing:
            raise ValueError("Pilot names are not owned by the current plans: " + ", ".join(missing))
        names = sorted(set(requested))
    elif limit is not None:
        if limit <= 0:
            raise ValueError("--limit must be positive")
        names = names[:limit]
    if not names:
        raise ValueError("The selected shared snapshot is empty")
    return [owners[name] for name in names]


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


def render_lean(core: str, records: list[dict[str, Any]], jsonl_path: Path) -> str:
    requests = ",\n".join(request_lean(record) for record in records)
    output = workspace_relative(jsonl_path)
    return (
        "import Lean\n"
        "import OAI.NumberTheory.PiExponent.Main\n\n"
        + core.rstrip()
        + "\n\nopen PiExponentSharedSourceSnapshot\n\n"
        + "def sharedSourceRequests : Array SourceRequest := #[\n"
        + requests
        + "\n  ]\n\n"
        + "run_meta do\n"
        + f"  exportSourceSnapshotJsonl sharedSourceRequests {lean_string(output)}\n"
    )


def atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_bytes(data)
    temporary.replace(path)


def write_json(path: Path, value: Any) -> None:
    atomic_write(path, (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8"))


def chunks(records: list[dict[str, Any]], size: int) -> list[list[dict[str, Any]]]:
    if size <= 0 or size >= len(records):
        return [records]
    return [records[start:start + size] for start in range(0, len(records), size)]


def base_input_hashes(unit_plan_path: Path, artifact_plan_path: Path) -> dict[str, str]:
    paths = [
        CORE, DECL_GRAPH, EXTRACTION_STATE, RUNTIME, VALIDATED_PORT, SOURCE_MANIFEST,
        SOURCE_RENAMES, DEPRIVATE_RENAMES, UPLOAD_ROUTE, unit_plan_path, artifact_plan_path,
    ]
    return {task_relative(path): sha_file(path) for path in paths}


def complete_source_input_hashes(unit_plan_path: Path, artifact_plan_path: Path) -> dict[str, str]:
    paths = [CORE, DECL_GRAPH, EXTRACTION_STATE, RUNTIME, VALIDATED_PORT, SOURCE_MANIFEST,
             unit_plan_path, artifact_plan_path, GENERATOR_SCRIPT, VALIDATOR_SCRIPT, *FULL_AST_INVENTORIES,
             ALL_SHARED_ROOTS, PROVIDER_VARIANT_UNIT_PLAN, PROVIDER_VARIANT_ARTIFACT_PLAN,
             PROVIDER_VARIANT_MANIFEST, *sorted(COMPLETE_PREVIEW_BUNDLE_DIR.glob("*.manifest.json"))]
    return {task_relative(path): sha_file(path) for path in paths}


def emit_shards(
    records: list[dict[str, Any]], preview: bool, shard_size: int,
    unit_plan_path: Path, artifact_plan_path: Path, lineage: dict[str, Any],
    complete_source: dict[str, Any] | None = None
) -> list[dict[str, Any]]:
    core = CORE.read_text(encoding="utf-8")
    mode = "pilot" if preview else ("complete-source" if complete_source else "final")
    output_dir = VERIFICATION / "shared-source-snapshot" / mode
    output_dir.mkdir(parents=True, exist_ok=True)
    runtime_sha = sha_file(RUNTIME)
    common_inputs = (
        complete_source_input_hashes(unit_plan_path, artifact_plan_path)
        if complete_source else base_input_hashes(unit_plan_path, artifact_plan_path)
    )
    owner_catalog_path: Path | None = None
    if complete_source:
        owner_catalog_path = output_dir / "CompleteSource875.owners.json"
        write_json(owner_catalog_path, {
            "schema_version": 1,
            "artifact_kind": "complete-original-source-owner-catalog",
            "source_version": 875,
            "source_module_count": complete_source["module_count"],
            "owner_count": len(records),
            "owner_unit_count": complete_source["owner_unit_count"],
            "unit_plan": task_relative(unit_plan_path),
            "unit_plan_sha256": sha_file(unit_plan_path),
            "artifact_plan": task_relative(artifact_plan_path),
            "artifact_plan_sha256": sha_file(artifact_plan_path),
            "decl_graph_sha256": sha_file(DECL_GRAPH),
            "ast_inventory": complete_source["source_inventory"],
            "plan_readiness": {
                "unit_ready_for_generation": complete_source["unit_plan_ready_for_generation"],
                "artifact_ready_for_generation": complete_source["artifact_plan_ready_for_generation"],
                "unit_provisional": complete_source["unit_plan_provisional"],
                "artifact_provisional": complete_source["artifact_plan_provisional"],
            },
            "coverage_qa": complete_source["coverage_qa"],
            "owners": records,
        })
        common_inputs[task_relative(owner_catalog_path)] = sha_file(owner_catalog_path)
    results: list[dict[str, Any]] = []
    for shard_index, shard in enumerate(chunks(records, shard_size)):
        stem = ("SharedSourceSnapshotPilot" if preview else "SharedSourceSnapshot") + f"_{shard_index:03d}"
        lean_path = output_dir / f"{stem}.lean"
        request_path = output_dir / f"{stem}.requests.json"
        owner_path = output_dir / f"{stem}.owners.json"
        jsonl_path = output_dir / f"{stem}.jsonl"
        manifest_path = output_dir / f"{stem}.manifest.json"

        request_doc = {
            "schema_version": 1,
            "mode": mode,
            "shared_ir_name_domain": "original-source-names",
            "requests": [{
                key: record[key] for key in (
                    "source_name", "source_module", "graph_kind", "decl_graph_sha256",
                    "decl_graph_row_sha256", "owner_kind", "owner_id", "command_unit"
                )
            } for record in shard],
        }
        owner_doc = {
            "schema_version": 1,
            "mode": mode,
            "lineage": lineage,
            "owners": shard,
        }
        if complete_source:
            request_doc["source_version"] = 875
            owner_doc.update({
                "source_version": 875,
                "owner_catalog": task_relative(owner_catalog_path),
                "owner_catalog_sha256": sha_file(owner_catalog_path),
            })
        write_json(request_path, request_doc)
        write_json(owner_path, owner_doc)
        atomic_write(lean_path, render_lean(core, shard, jsonl_path).encode("utf-8"))

        inputs = dict(common_inputs)
        inputs[task_relative(request_path)] = sha_file(request_path)
        inputs[task_relative(owner_path)] = sha_file(owner_path)
        for record in shard:
            source_file = TASK / record["source_file"]
            inputs[record["source_file"]] = sha_file(source_file)
            facts_file = resolve_workspace_path(record["stage2_facts"], "Stage 2 facts")
            inputs[task_relative(facts_file)] = sha_file(facts_file)

        manifest: dict[str, Any] = {
            "schema_version": 1,
            "artifact_kind": "shared-original-source-snapshot-exporter",
            "mode": mode,
            "certificate_class": (
                "pilot-nonfinal" if preview else
                "complete-source-original-kernel-snapshot-only" if complete_source else
                "final-source-candidate"
            ),
            "output": workspace_relative(lean_path),
            "output_sha256": sha_file(lean_path),
            "imports": IMPORTS,
            "runtime_sha256": runtime_sha,
            "input_hashes": dict(sorted(inputs.items())),
            "snapshot_jsonl": workspace_relative(jsonl_path),
            "request_manifest": task_relative(request_path),
            "owner_manifest": task_relative(owner_path),
            "expected_rows": len(shard),
            "shared_ir_name_domain": "original-source-names",
            "consumer_rule": (
                "This certificate covers only the original-source environment Names, kernel types, "
                "full definition values, theorem type-only rows, and axioms. Platform renames, "
                "private-name handling, and generated-provider comparisons require separate certificates."
                if complete_source else
                "Apply and validate name maps locally when comparing a generated artifact; "
                "this source IR contains only original environment Names."
            ),
            "validation_evidence": "external Root staged preflight and JSONL validator required",
            "preflight": {
                "timeout_seconds": 300,
                "command": (
                    "python scripts/preflight_staged_module.py "
                    f"{lean_path.relative_to(VERIFICATION).as_posix()} "
                    f"--root {output_dir.relative_to(VERIFICATION).as_posix()} --timeout-seconds 300"
                ),
            },
        }
        if complete_source:
            manifest.update({
                "source_version": 875,
                "source_only": True,
                "plan_readiness": {
                    "unit_ready_for_generation": complete_source["unit_plan_ready_for_generation"],
                    "artifact_ready_for_generation": complete_source["artifact_plan_ready_for_generation"],
                    "unit_provisional": complete_source["unit_plan_provisional"],
                    "artifact_provisional": complete_source["artifact_plan_provisional"],
                },
                "owner_catalog": task_relative(owner_catalog_path),
                "owner_catalog_sha256": sha_file(owner_catalog_path),
            })
        else:
            manifest["name_mapping_inputs"] = {
                task_relative(SOURCE_RENAMES): sha_file(SOURCE_RENAMES),
                task_relative(DEPRIVATE_RENAMES): sha_file(DEPRIVATE_RENAMES),
            }
        if preview:
            manifest["pilot_validated"] = False
            manifest["usable_as_final_source_certificate"] = False
        write_json(manifest_path, manifest)
        results.append({
            "index": shard_index,
            "lean": task_relative(lean_path),
            "manifest": task_relative(manifest_path),
            "jsonl": workspace_relative(jsonl_path),
            "rows": len(shard),
            "preflight_command": manifest["preflight"]["command"],
        })
    return results


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--preview", action="store_true",
        help="Use incomplete preview plans and emit a non-final pilot subset.",
    )
    parser.add_argument(
        "--complete-source", action="store_true",
        help="Emit the full 875-module original-source snapshot from complete provisional plans; does not certify platform readiness.",
    )
    parser.add_argument(
        "--pilot-names", nargs="+", metavar="SOURCE_NAME",
        help=f"Exact original source names (comma-separated values also accepted). Example: {PILOT_EXAMPLE}",
    )
    parser.add_argument(
        "--limit", type=int,
        help="Preview-only deterministic limit after sorting original source names.",
    )
    parser.add_argument(
        "--shard-size", type=int, default=0,
        help="Maximum rows per staged Lean exporter; 0 emits one shard. Each shard needs its own <=300s preflight.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.preview and args.complete_source:
        raise ValueError("--preview and --complete-source are mutually exclusive")
    if args.shard_size < 0:
        raise ValueError("--shard-size cannot be negative")
    unit_plan_path = PREVIEW_UNIT_PLAN if (args.preview or args.complete_source) else FINAL_UNIT_PLAN
    artifact_plan_path = PREVIEW_ARTIFACT_PLAN if (args.preview or args.complete_source) else FINAL_ARTIFACT_PLAN
    unit_plan = read_json(unit_plan_path, "unit plan")
    artifact_plan = read_json(artifact_plan_path, "artifact plan")
    extraction_state = read_json(EXTRACTION_STATE, "extraction state")
    complete_source_evidence = None
    if args.complete_source:
        complete_source_evidence = require_complete_source_inputs(unit_plan, artifact_plan, extraction_state)
    elif not args.preview:
        require_final_inputs(unit_plan, artifact_plan, extraction_state)
    lineage = validate_source_lineage()
    graph_rows, graph_sha = load_decl_graph()
    units = unit_index(unit_plan)
    if args.complete_source:
        owners = collect_complete_source_owners(units, graph_rows)
        complete_source_evidence["owner_unit_count"] = len(units)
        complete_source_evidence["coverage_qa"] = complete_source_coverage_qa(units, owners)
    else:
        owners = collect_owned_names(units, artifact_plan)
    selected = choose_subset(owners, args.pilot_names, args.limit, args.preview)
    validated = [validate_owner(owner, graph_rows, graph_sha, extraction_state) for owner in selected]
    shards = emit_shards(
        validated, args.preview, args.shard_size, unit_plan_path, artifact_plan_path, lineage,
        complete_source_evidence
    )
    report = {
        "artifact_kind": "complete-original-source-generation-report" if args.complete_source else "shared-source-generation-report",
        "mode": "pilot" if args.preview else ("complete-source" if args.complete_source else "final"),
        "lean_started": False,
        "selected_rows": len(validated),
        "shards": shards,
    }
    if args.complete_source:
        write_json(VERIFICATION / "shared-source-snapshot" / "complete-source" / "generation-report.json", report)
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
