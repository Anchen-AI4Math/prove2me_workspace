#!/usr/bin/env python3
"""Revalidate and consume the complete original-source snapshot certificate.

This module never invokes Lean.  It deliberately replays the complete shard,
input, preflight, OLean, graph, owner-catalog, raw-source, row-schema, and Std3
checks on every use.  A report boolean is therefore not a trust shortcut.
Pilot certificates and partial shard sets are always rejected.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import validate_shared_source_snapshot as shared


TASK = Path(__file__).resolve().parents[1]
VERIFICATION = TASK / "verification"
COMPLETE_DIR = VERIFICATION / "shared-source-snapshot" / "complete-source"
EXPECTED_CERTIFICATE = COMPLETE_DIR / "complete-source-validation.json"


def _read(path: Path, label: str) -> Any:
    return shared.read_json(path, label)


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _strict_preflight_oleans(manifest_path: Path, lean_path: Path) -> dict[str, Any]:
    """Strengthen the shared validator with exact live OLean resolution checks."""
    manifest = _read(manifest_path, "shared-source shard manifest")
    sidecar = lean_path.with_suffix(lean_path.suffix + ".preflight.json")
    preflight = _read(sidecar, "shared-source preflight sidecar")
    _assert(preflight.get("source") == shared.task_relative(lean_path)
            and preflight.get("manifest") == shared.task_relative(manifest_path)
            and preflight.get("module_root") == shared.task_relative(COMPLETE_DIR)
            and preflight.get("actual_module_identity") == lean_path.stem,
            "Shared-source preflight path/module identity changed")
    before = preflight.get("source_certificate")
    after = preflight.get("source_certificate_after")
    _assert(isinstance(before, dict) and before == after,
            "Shared-source preflight source certificate changed")
    source_evidence = before.get("source")
    _assert(isinstance(source_evidence, dict)
            and source_evidence.get("sha256") == shared.sha(lean_path)
            and source_evidence.get("expected_sha256") == shared.sha(lean_path)
            and source_evidence.get("matches") is True,
            "Shared-source preflight does not bind the exact shard source")

    search_roots = [Path(item).resolve() for item in preflight.get("effective_lean_path", [])]
    _assert(search_roots, "Shared-source preflight has no effective LEAN_PATH")
    seen: set[str] = set()
    dependency_evidence = preflight.get("dependency_oleans")
    _assert(isinstance(dependency_evidence, list) and dependency_evidence,
            "Shared-source preflight has no dependency OLean evidence")
    for dependency in dependency_evidence:
        module = dependency.get("module")
        path = Path(dependency.get("path", "")).resolve()
        digest = dependency.get("sha256_after")
        _assert(isinstance(module, str) and module and path.is_file()
                and digest == dependency.get("sha256_before")
                and digest == shared.sha(path)
                and dependency.get("stable_during_compile") is True,
                f"Shared-source dependency OLean is stale: {module}")
        relative = Path(*module.split(".")).with_suffix(".olean")
        first = next((root / relative for root in search_roots if (root / relative).is_file()), None)
        _assert(first is not None and first.resolve() == path,
                f"Shared-source dependency OLean is not the first LEAN_PATH match: {module}")
        recorded_root = Path(dependency.get("resolved_search_root", "")).resolve()
        _assert(recorded_root in search_roots and (recorded_root / relative).resolve() == path,
                f"Shared-source dependency OLean search root changed: {module}")
        seen.add(module)
    _assert(set(manifest.get("imports", [])) <= seen,
            "Shared-source preflight lacks OLean evidence for an exact import")
    _assert(preflight.get("mode") == "modecheck"
            and preflight.get("output_olean") is None
            and preflight.get("output_olean_sha256") is None,
            "Shared-source preflight used an unexpected compilation mode")
    return {
        "preflight": shared.task_relative(sidecar),
        "preflight_sha256": shared.sha(sidecar),
        "dependency_olean_count": len(dependency_evidence),
        "exact_import_oleans_present": True,
        "first_search_path_resolution_verified": True,
    }


def _validate_catalog(catalog_path: Path, owners: dict[str, dict[str, str]],
                      graph_sha: str, unit_plan_path: Path, artifact_plan_path: Path,
                      unit_plan: dict[str, Any], artifact_plan: dict[str, Any]) -> dict[str, Any]:
    catalog = _read(catalog_path, "complete-source owner catalog")
    inventories = [
        {"path": shared.task_relative(path), "sha256": shared.sha(path), "module_count": 875}
        for path in shared.FULL_AST_INVENTORIES
    ]
    readiness = {
        "unit_ready_for_generation": unit_plan.get("ready_for_generation"),
        "artifact_ready_for_generation": artifact_plan.get("ready_for_generation"),
        "unit_provisional": unit_plan.get("provisional"),
        "artifact_provisional": artifact_plan.get("provisional"),
    }
    coverage_qa = shared.complete_source_coverage_qa(unit_plan, owners)
    _assert(catalog.get("artifact_kind") == "complete-original-source-owner-catalog"
            and catalog.get("source_version") == 875
            and catalog.get("source_module_count") == 875
            and catalog.get("owner_count") == len(owners)
            and catalog.get("owner_unit_count") == 5786
            and catalog.get("unit_plan") == shared.task_relative(unit_plan_path)
            and catalog.get("unit_plan_sha256") == shared.sha(unit_plan_path)
            and catalog.get("artifact_plan") == shared.task_relative(artifact_plan_path)
            and catalog.get("artifact_plan_sha256") == shared.sha(artifact_plan_path)
            and catalog.get("decl_graph_sha256") == graph_sha
            and catalog.get("ast_inventory") == inventories
            and catalog.get("plan_readiness") == readiness
            and catalog.get("coverage_qa") == coverage_qa,
            "Complete-source owner catalog lineage differs from current 875 plans")
    rows = catalog.get("owners")
    _assert(isinstance(rows, list)
            and [item.get("source_name") for item in rows] == sorted(owners),
            "Complete-source owner catalog name coverage/order changed")
    for row in rows:
        expected = owners[row["source_name"]]
        _assert(all(row.get(key) == value for key, value in expected.items()),
                f"Complete-source owner row differs from plan: {row['source_name']}")
    return {"path": shared.task_relative(catalog_path), "sha256": shared.sha(catalog_path),
            "owner_count": len(rows), "owner_unit_count": 5786,
            "plan_readiness": readiness, "coverage_qa": coverage_qa}


def validate_complete_source_cache(certificate_path: Path,
                                   original_requests: list[dict[str, Any]]) -> dict[str, Any]:
    """Return authenticated source rows for exactly the requested provider names."""
    certificate_path = certificate_path.resolve()
    _assert(certificate_path == EXPECTED_CERTIFICATE.resolve(),
            "Only the complete-source certificate at its canonical path is accepted")
    _assert("pilot" not in certificate_path.parts, "Pilot shared-source certificates are forbidden")
    certificate = _read(certificate_path, "complete-source validation report")
    _assert(certificate.get("validated") is True
            and certificate.get("mode") == "complete-source"
            and certificate.get("source_only_original_kernel_certificate") is True
            and certificate.get("platform_name_type_comparison_required") is True
            and certificate.get("usable_as_final_source_certificate") is False
            and certificate.get("source_version") == 875,
            "Certificate is not a complete original-source-only kernel certificate")
    checks = certificate.get("checks")
    _assert(isinstance(checks, dict) and checks and all(value is True for value in checks.values()),
            "Complete-source report does not record every strict check")

    unit_plan_path = VERIFICATION / "platform-unit-plan-preview.json"
    artifact_plan_path = VERIFICATION / "platform-artifact-plan-preview.json"
    unit_plan = _read(unit_plan_path, "complete unit plan")
    artifact_plan = _read(artifact_plan_path, "complete artifact plan")
    extraction = _read(VERIFICATION / "extraction-state.json", "complete extraction state")
    _assert(extraction.get("complete") is True and len(extraction.get("stage2", {})) == 875,
            "Shared-source cache requires the complete 875 extraction")
    _assert(unit_plan.get("complete_extraction") is True
            and artifact_plan.get("complete_extraction") is True
            and unit_plan.get("source_declarations_pending_ast") == [],
            "Shared-source cache plans do not have complete AST ownership")
    graph, graph_sha = shared.load_graph()
    owners = shared.expected_complete_source_owners(unit_plan, graph)
    source_manifest = _read(shared.SOURCE_MANIFEST, "immutable source manifest")
    validated_port_path = VERIFICATION / "validated-port-manifest.json"
    validated_port = _read(validated_port_path, "validated port manifest")
    _assert(validated_port.get("source_commit") == source_manifest.get("commit")
            and validated_port.get("original_files_sha256_verified") == 875
            and validated_port.get("build", {}).get("exit_code") == 0,
            "Complete-source lineage lacks a successful immutable 875-source build")
    _assert(certificate.get("source_commit") == source_manifest.get("commit")
            and certificate.get("immutable_source_manifest_sha256") == shared.sha(shared.SOURCE_MANIFEST)
            and certificate.get("validated_port_manifest_sha256") == shared.sha(validated_port_path)
            and certificate.get("decl_graph_sha256") == graph_sha
            and certificate.get("snapshot_core_sha256") == shared.sha(shared.CORE)
            and certificate.get("validator_sha256") == shared.sha(Path(shared.__file__).resolve())
            and certificate.get("unit_plan") == shared.task_relative(unit_plan_path)
            and certificate.get("unit_plan_sha256") == shared.sha(unit_plan_path)
            and certificate.get("artifact_plan") == shared.task_relative(artifact_plan_path)
            and certificate.get("artifact_plan_sha256") == shared.sha(artifact_plan_path),
            "Complete-source report top-level hashes are stale")

    catalog_path = COMPLETE_DIR / "CompleteSource875.owners.json"
    catalog_evidence = _validate_catalog(
        catalog_path, owners, graph_sha, unit_plan_path, artifact_plan_path, unit_plan, artifact_plan)
    _assert(certificate.get("owner_catalog") == {
        "path": shared.task_relative(catalog_path),
        "sha256": shared.sha(catalog_path),
        "owner_count": len(owners),
    }, "Complete-source report owner-catalog witness changed")

    manifests = sorted(COMPLETE_DIR.glob("SharedSourceSnapshot_*.manifest.json"))
    _assert(manifests and len(manifests) == len(certificate.get("shards", [])),
            "Complete-source shard manifest set is partial")
    rows: dict[str, dict[str, Any]] = {}
    shard_evidence: list[dict[str, Any]] = []
    olean_evidence: list[dict[str, Any]] = []
    for manifest_path in manifests:
        manifest = _read(manifest_path, "complete-source shard manifest")
        _assert(manifest.get("mode") == "complete-source", "Non-complete shard in source cache")
        shard, shard_rows, _ = shared.validate_shard(
            manifest_path, owners, graph, graph_sha, source_manifest, extraction, True)
        _assert(not (set(rows) & set(shard_rows)), "Duplicate source name across cache shards")
        rows.update(shard_rows)
        shard_evidence.append(shard)
        lean_path = shared.workspace_path(manifest["output"], "complete-source Lean source")
        olean_evidence.append(_strict_preflight_oleans(manifest_path, lean_path))
    _assert(set(rows) == set(owners)
            and certificate.get("provided_names") == sorted(owners)
            and certificate.get("row_count") == len(owners),
            "Complete-source row coverage differs from all 875 plan owners")
    _assert(certificate.get("shards") == shard_evidence,
            "Complete-source report shard evidence differs from live full revalidation")

    performance = certificate.get("performance", {})
    seconds = [item["preflight"]["seconds"] for item in shard_evidence]
    _assert(performance.get("measured_shards") == len(shard_evidence)
            and performance.get("measured_rows") == len(rows)
            and performance.get("preflight_seconds") == seconds
            and performance.get("max_preflight_seconds") == max(seconds)
            and all(0 < value <= 300 for value in seconds),
            "Complete-source report performance/300-second evidence changed")

    requested_names = [item.get("source_graph_name") for item in original_requests]
    _assert(len(requested_names) == len(set(requested_names)),
            "Provider original request list repeats a source name")
    selected: list[dict[str, Any]] = []
    selected_evidence: list[dict[str, Any]] = []
    for request in original_requests:
        name = request.get("source_graph_name")
        row = rows.get(name)
        owner = owners.get(name)
        _assert(row is not None and owner is not None,
                f"Provider request is absent from complete-source cache: {name}")
        _assert(request.get("expected_module") == row["sourceModule"] == owner["source_module"]
                and request.get("expected_kind") == row["graphKind"] == owner["graph_kind"]
                and request.get("expected_public_name") == name
                and request.get("expected_user_name") == name
                and request.get("source_was_private") is False
                and request.get("command_unit") == row["commandUnit"] == owner["command_unit"]
                and request.get("decl_graph_sha256") == row["declGraphSha256"] == graph_sha
                and request.get("decl_graph_row_sha256") == row["declGraphRowSha256"],
                f"Provider original request does not match cached source owner: {name}")
        selected.append(row)
        selected_evidence.append({
            "source_name": name,
            "source_module": row["sourceModule"],
            "graph_kind": row["graphKind"],
            "command_unit": row["commandUnit"],
            "type_canonical_sha256": shared.sha_bytes(json.dumps(
                shared.normalize_kernel(row, "type"), separators=(",", ":"), ensure_ascii=False
            ).encode("utf-8")),
            "value_canonical_sha256": None if row["value"] is None else shared.sha_bytes(json.dumps(
                shared.normalize_kernel(row, "value"), separators=(",", ":"), ensure_ascii=False
            ).encode("utf-8")),
            "axioms": row["axioms"],
            "std3_only": set(row["axioms"]) <= shared.STD3,
        })
    return {
        "rows": selected,
        "evidence": {
            "strategy": "complete-source-cache; original snapshot compile skipped",
            "certificate": shared.task_relative(certificate_path),
            "certificate_sha256": shared.sha(certificate_path),
            "source_commit": certificate["source_commit"],
            "source_version": 875,
            "full_catalog_rows_revalidated": len(rows),
            "full_shards_revalidated": len(shard_evidence),
            "owner_catalog": catalog_evidence,
            "preflight_olean_evidence": olean_evidence,
            "selected_rows": selected_evidence,
            "theorem_values_omitted": True,
            "definition_values_complete": True,
            "std3_only": True,
            "platform_readiness_claimed": False,
        },
    }
