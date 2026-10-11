#!/usr/bin/env python3
"""Stage the exact original-source snapshot needed by the 29 safe provider leaves.

This is a deliberately partial, source-only certificate.  It uses the frozen
6,148-name complete owner catalog as authenticated metadata, but exports only
the 174 public declarations requested by the current provider snapshots.  It
never starts Lean.  The default is one shard; use --shard-size only after an
actual 300-second preflight requires deterministic splitting.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import generate_shared_source_snapshot as base
import validate_shared_source_snapshot as shared


TASK = Path(__file__).resolve().parents[1]
VERIFICATION = TASK / "verification"
DIRECTORY = VERIFICATION / "shared-source-snapshot" / "provider-subset"
FULL_CATALOG = VERIFICATION / "shared-source-snapshot" / "complete-source" / "CompleteSource875.owners.json"
BUNDLE_ROOT = VERIFICATION / "providers-complete-preview" / "all-shared-safe-leaves"
DEFINITIONS = BUNDLE_ROOT / "Definitions"
SNAPSHOTS = BUNDLE_ROOT / "snapshots"
UNIT_PLAN = VERIFICATION / "platform-unit-plan-preview.json"
ARTIFACT_PLAN = VERIFICATION / "platform-artifact-plan-preview.json"
EXTRACTION = VERIFICATION / "extraction-state.json"
SUBSET_CATALOG = DIRECTORY / "ProviderSourceSubset174.catalog.json"
GENERATION_REPORT = DIRECTORY / "generation-report.json"
VALIDATOR = TASK / "scripts" / "validate_provider_source_subset_snapshot.py"
CONSUMER = TASK / "scripts" / "provider_source_subset_cache.py"
EXPECTED_BUNDLES = 29
EXPECTED_ROWS = 174
REQUEST_FIELDS = (
    "source_name", "source_module", "graph_kind", "decl_graph_sha256",
    "decl_graph_row_sha256", "owner_kind", "owner_id", "command_unit",
)


def write_json(path: Path, value: Any) -> None:
    base.write_json(path, value)


def _catalog_rows(expected: dict[str, dict[str, Any]], unit_plan: dict[str, Any],
                  complete: dict[str, Any]) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    catalog = base.read_json(FULL_CATALOG, "complete 6,148-name owner catalog")
    rows = catalog.get("owners")
    expected_readiness = {
        "unit_ready_for_generation": complete["unit_plan_ready_for_generation"],
        "artifact_ready_for_generation": complete["artifact_plan_ready_for_generation"],
        "unit_provisional": complete["unit_plan_provisional"],
        "artifact_provisional": complete["artifact_plan_provisional"],
    }
    expected_coverage = shared.complete_source_coverage_qa(unit_plan, expected)
    if (catalog.get("artifact_kind") != "complete-original-source-owner-catalog"
            or catalog.get("source_version") != 875
            or catalog.get("source_module_count") != 875
            or catalog.get("owner_count") != 6148
            or catalog.get("owner_unit_count") != 5786
            or catalog.get("unit_plan") != base.task_relative(UNIT_PLAN)
            or catalog.get("unit_plan_sha256") != base.sha_file(UNIT_PLAN)
            or catalog.get("artifact_plan") != base.task_relative(ARTIFACT_PLAN)
            or catalog.get("artifact_plan_sha256") != base.sha_file(ARTIFACT_PLAN)
            or catalog.get("decl_graph_sha256") != base.sha_file(base.DECL_GRAPH)
            or catalog.get("ast_inventory") != complete["source_inventory"]
            or catalog.get("plan_readiness") != expected_readiness
            or catalog.get("coverage_qa") != expected_coverage
            or not isinstance(rows, list)
            or len(rows) != 6148):
        raise ValueError("Complete owner catalog header is stale or incomplete")
    indexed: dict[str, dict[str, Any]] = {}
    for row in rows:
        name = row.get("source_name") if isinstance(row, dict) else None
        if not isinstance(name, str) or name in indexed or name not in expected:
            raise ValueError("Complete owner catalog has an invalid or duplicate source name")
        if any(row.get(key) != value for key, value in expected[name].items()):
            raise ValueError(f"Complete owner catalog differs from current AST owner: {name}")
        indexed[name] = row
    if set(indexed) != set(expected):
        raise ValueError("Complete owner catalog does not exactly cover the 6,148 current source names")
    return catalog, indexed


def build_basis() -> dict[str, Any]:
    unit_plan = base.read_json(UNIT_PLAN, "complete unit plan")
    artifact_plan = base.read_json(ARTIFACT_PLAN, "complete artifact plan")
    extraction = base.read_json(EXTRACTION, "complete extraction state")
    complete = base.require_complete_source_inputs(unit_plan, artifact_plan, extraction)
    graph, graph_sha = base.load_decl_graph()
    expected = shared.expected_complete_source_owners(unit_plan, graph)
    full_catalog, catalog_index = _catalog_rows(expected, unit_plan, complete)
    raw_owners = base.collect_complete_source_owners(base.unit_index(unit_plan), graph)
    if set(raw_owners) != set(expected):
        raise ValueError("Generator and validator complete-owner reconstructions differ")

    bundle_manifests = sorted(DEFINITIONS.glob("*.manifest.json"))
    if len(bundle_manifests) != EXPECTED_BUNDLES:
        raise ValueError(f"Expected 29 safe provider manifests, got {len(bundle_manifests)}")
    selected_requests: dict[str, dict[str, Any]] = {}
    bundle_coverage: list[dict[str, Any]] = []
    units = base.unit_index(unit_plan)
    for manifest_path in bundle_manifests:
        manifest = base.read_json(manifest_path, "safe provider manifest")
        stem = manifest_path.name.removesuffix(".manifest.json")
        request_path = SNAPSHOTS / stem / "snapshot-requests.json"
        request_doc = base.read_json(request_path, "provider snapshot requests")
        original = request_doc.get("original")
        generated = request_doc.get("generated")
        selected_units = manifest.get("selected_units")
        if (not isinstance(original, list) or not isinstance(generated, list)
                or not isinstance(selected_units, list) or len(original) != len(generated)):
            raise ValueError(f"Invalid provider request boundary: {stem}")
        unit_names: list[str] = []
        for uid in selected_units:
            unit = units.get(uid)
            if unit is None:
                raise ValueError(f"Provider manifest references unknown unit: {uid}")
            unit_names.extend(unit.get("graph_names", []))
        request_names = [item.get("source_graph_name") for item in original]
        if len(request_names) != len(set(request_names)) or set(request_names) != set(unit_names):
            raise ValueError(f"Provider original requests differ from selected AST units: {stem}")
        for old, new in zip(original, generated, strict=True):
            name = old.get("source_graph_name")
            owner = catalog_index.get(name)
            if owner is None or name in selected_requests or owner.get("source_private") is not False:
                raise ValueError(f"Provider subset name is absent, duplicate, or private: {name}")
            if not all([
                old.get("expected_user_name") == name,
                old.get("expected_public_name") == name,
                old.get("expected_module") == owner["source_module"],
                old.get("expected_kind") == owner["graph_kind"],
                old.get("source_was_private") is False,
                old.get("command_unit") == owner["command_unit"],
                old.get("decl_graph_sha256") == graph_sha,
                old.get("decl_graph_row_sha256") == graph[name]["_row_sha256"],
                new.get("source_graph_name") == name,
                new.get("expected_public_name") == name,
                new.get("command_unit") == owner["command_unit"],
                new.get("decl_graph_sha256") == graph_sha,
                new.get("decl_graph_row_sha256") == graph[name]["_row_sha256"],
            ]):
                raise ValueError(f"Provider request does not match authenticated source owner: {name}")
            selected_requests[name] = old
        bundle_coverage.append({
            "stem": stem,
            "source_module": manifest.get("source_module"),
            "platform_module": manifest.get("platform_module"),
            "provider_manifest": base.task_relative(manifest_path),
            "provider_manifest_sha256": base.sha_file(manifest_path),
            "snapshot_requests": base.task_relative(request_path),
            "snapshot_requests_sha256": base.sha_file(request_path),
            "source_names": sorted(request_names),
            "row_count": len(request_names),
        })
    if len(selected_requests) != EXPECTED_ROWS:
        raise ValueError(f"Expected 174 unique provider source requests, got {len(selected_requests)}")

    validated = [
        base.validate_owner(raw_owners[name], graph, graph_sha, extraction)
        for name in sorted(selected_requests)
    ]
    for row in validated:
        expected_row = expected[row["source_name"]]
        if any(row.get(key) != value for key, value in expected_row.items()):
            raise ValueError(f"Validated source row differs from complete owner catalog: {row['source_name']}")
    return {
        "unit_plan": unit_plan,
        "artifact_plan": artifact_plan,
        "extraction": extraction,
        "complete": complete,
        "graph": graph,
        "graph_sha256": graph_sha,
        "full_catalog": full_catalog,
        "full_catalog_sha256": base.sha_file(FULL_CATALOG),
        "records": validated,
        "bundle_coverage": bundle_coverage,
        "lineage": base.validate_source_lineage(),
    }


def _common_inputs(basis: dict[str, Any]) -> dict[str, str]:
    paths = [
        base.CORE, base.DECL_GRAPH, base.EXTRACTION_STATE, base.RUNTIME,
        base.VALIDATED_PORT, base.SOURCE_MANIFEST, UNIT_PLAN, ARTIFACT_PLAN,
        FULL_CATALOG, Path(__file__).resolve(), VALIDATOR, CONSUMER,
        Path(base.__file__).resolve(), Path(shared.__file__).resolve(),
        *base.FULL_AST_INVENTORIES,
    ]
    for bundle in basis["bundle_coverage"]:
        paths.append(TASK / bundle["provider_manifest"])
        paths.append(TASK / bundle["snapshot_requests"])
    return {base.task_relative(path): base.sha_file(path) for path in paths}


def emit(basis: dict[str, Any], shard_size: int) -> dict[str, Any]:
    DIRECTORY.mkdir(parents=True, exist_ok=True)
    records = basis["records"]
    catalog = {
        "schema_version": 1,
        "artifact_kind": "provider-source-subset-catalog",
        "certificate_scope": "partial-source-only-exact-provider-request-set",
        "source_version": 875,
        "partial": True,
        "platform_ready": False,
        "usable_as_full_source_certificate": False,
        "full_owner_catalog": base.task_relative(FULL_CATALOG),
        "full_owner_catalog_sha256": basis["full_catalog_sha256"],
        "full_owner_count": 6148,
        "subset_owner_count": len(records),
        "provider_bundle_count": len(basis["bundle_coverage"]),
        "unit_plan": base.task_relative(UNIT_PLAN),
        "unit_plan_sha256": base.sha_file(UNIT_PLAN),
        "artifact_plan": base.task_relative(ARTIFACT_PLAN),
        "artifact_plan_sha256": base.sha_file(ARTIFACT_PLAN),
        "decl_graph_sha256": basis["graph_sha256"],
        "bundle_coverage": basis["bundle_coverage"],
        "owners": records,
    }
    write_json(SUBSET_CATALOG, catalog)
    common_inputs = _common_inputs(basis)
    common_inputs[base.task_relative(SUBSET_CATALOG)] = base.sha_file(SUBSET_CATALOG)
    runtime_sha = base.sha_file(base.RUNTIME)
    core = base.CORE.read_text(encoding="utf-8")
    shards: list[dict[str, Any]] = []
    for index, rows in enumerate(base.chunks(records, shard_size)):
        stem = f"ProviderSourceSubset_{index:03d}"
        lean_path = DIRECTORY / f"{stem}.lean"
        request_path = DIRECTORY / f"{stem}.requests.json"
        owner_path = DIRECTORY / f"{stem}.owners.json"
        jsonl_path = DIRECTORY / f"{stem}.jsonl"
        manifest_path = DIRECTORY / f"{stem}.manifest.json"
        request_doc = {
            "schema_version": 1,
            "mode": "provider-source-subset",
            "certificate_scope": "partial-source-only-exact-provider-request-set",
            "shared_ir_name_domain": "original-source-names",
            "requests": [{key: row[key] for key in REQUEST_FIELDS} for row in rows],
        }
        owner_doc = {
            "schema_version": 1,
            "mode": "provider-source-subset",
            "certificate_scope": "partial-source-only-exact-provider-request-set",
            "lineage": basis["lineage"],
            "full_owner_catalog": base.task_relative(FULL_CATALOG),
            "full_owner_catalog_sha256": basis["full_catalog_sha256"],
            "subset_catalog": base.task_relative(SUBSET_CATALOG),
            "subset_catalog_sha256": base.sha_file(SUBSET_CATALOG),
            "owners": rows,
        }
        write_json(request_path, request_doc)
        write_json(owner_path, owner_doc)
        base.atomic_write(lean_path, base.render_lean(core, rows, jsonl_path).encode("utf-8"))
        inputs = dict(common_inputs)
        inputs[base.task_relative(request_path)] = base.sha_file(request_path)
        inputs[base.task_relative(owner_path)] = base.sha_file(owner_path)
        for row in rows:
            source_path = TASK / row["source_file"]
            facts_path = base.resolve_workspace_path(row["stage2_facts"], "Stage 2 facts")
            inputs[row["source_file"]] = base.sha_file(source_path)
            inputs[base.task_relative(facts_path)] = base.sha_file(facts_path)
        manifest = {
            "schema_version": 1,
            "artifact_kind": "provider-source-subset-original-kernel-snapshot-exporter",
            "mode": "provider-source-subset",
            "certificate_class": "partial-source-only-exact-provider-request-set",
            "source_version": 875,
            "source_only": True,
            "partial": True,
            "platform_ready": False,
            "usable_as_full_source_certificate": False,
            "output": base.workspace_relative(lean_path),
            "output_sha256": base.sha_file(lean_path),
            "imports": base.IMPORTS,
            "runtime_sha256": runtime_sha,
            "input_hashes": dict(sorted(inputs.items())),
            "snapshot_jsonl": base.workspace_relative(jsonl_path),
            "request_manifest": base.task_relative(request_path),
            "owner_manifest": base.task_relative(owner_path),
            "full_owner_catalog": base.task_relative(FULL_CATALOG),
            "full_owner_catalog_sha256": basis["full_catalog_sha256"],
            "subset_catalog": base.task_relative(SUBSET_CATALOG),
            "subset_catalog_sha256": base.sha_file(SUBSET_CATALOG),
            "expected_rows": len(rows),
            "expected_subset_rows": EXPECTED_ROWS,
            "expected_provider_bundles": EXPECTED_BUNDLES,
            "shared_ir_name_domain": "original-source-names",
            "consumer_rule": "Reusable only for an exact requested original source Name present in this authenticated 174-row subset; every generated provider still requires its own kernel comparison.",
            "validation_evidence": "External Root staged preflight and provider-subset JSONL validator required",
            "preflight": {
                "timeout_seconds": 300,
                "command": (
                    "python scripts/preflight_staged_module.py "
                    f"{lean_path.relative_to(VERIFICATION).as_posix()} "
                    f"--root {DIRECTORY.relative_to(VERIFICATION).as_posix()} "
                    f"--imports-manifest {manifest_path.relative_to(VERIFICATION).as_posix()} "
                    "--timeout-seconds 300"
                ),
            },
        }
        write_json(manifest_path, manifest)
        shards.append({
            "index": index,
            "lean": base.task_relative(lean_path),
            "manifest": base.task_relative(manifest_path),
            "jsonl": base.task_relative(jsonl_path),
            "rows": len(rows),
            "preflight_command": manifest["preflight"]["command"],
        })
    report = {
        "schema_version": 1,
        "artifact_kind": "provider-source-subset-generation-report",
        "mode": "provider-source-subset",
        "certificate_scope": "partial-source-only-exact-provider-request-set",
        "lean_started": False,
        "partial": True,
        "platform_ready": False,
        "usable_as_full_source_certificate": False,
        "selected_rows": len(records),
        "provider_bundles": len(basis["bundle_coverage"]),
        "subset_catalog": base.task_relative(SUBSET_CATALOG),
        "subset_catalog_sha256": base.sha_file(SUBSET_CATALOG),
        "shards": shards,
    }
    write_json(GENERATION_REPORT, report)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shard-size", type=int, default=0,
                        help="Maximum rows per exporter; 0 emits the preferred one 174-row shard")
    args = parser.parse_args()
    if args.shard_size < 0:
        raise ValueError("--shard-size cannot be negative")
    report = emit(build_basis(), args.shard_size)
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
