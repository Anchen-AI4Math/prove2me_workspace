#!/usr/bin/env python3
"""Validate the actual 174-row provider source-subset snapshot without Lean."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import generate_provider_source_subset_snapshot as gen
import generate_shared_source_snapshot as base
import validate_shared_source_snapshot as shared


TASK = Path(__file__).resolve().parents[1]
VERIFICATION = TASK / "verification"
DIRECTORY = VERIFICATION / "shared-source-snapshot" / "provider-subset"
CERTIFICATE = DIRECTORY / "provider-subset-validation.json"


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _strict_olean_evidence(lean_path: Path, manifest_path: Path,
                           manifest: dict[str, Any]) -> dict[str, Any]:
    preflight_path = lean_path.with_suffix(lean_path.suffix + ".preflight.json")
    preflight = shared.read_json(preflight_path, "provider-subset preflight")
    _assert(preflight.get("source") == shared.task_relative(lean_path)
            and preflight.get("manifest") == shared.task_relative(manifest_path)
            and preflight.get("module_root") == shared.task_relative(DIRECTORY)
            and preflight.get("actual_module_identity") == lean_path.stem,
            "Provider-subset preflight path/module identity changed")
    _assert(preflight.get("mode") == "modecheck"
            and preflight.get("output_olean") is None
            and preflight.get("output_olean_sha256") is None,
            "Provider-subset exporter must be checked in modecheck")
    search_roots = [Path(item).resolve() for item in preflight.get("effective_lean_path", [])]
    _assert(search_roots, "Provider-subset preflight has no effective LEAN_PATH")
    dependencies = preflight.get("dependency_oleans")
    _assert(isinstance(dependencies, list) and dependencies,
            "Provider-subset preflight has no OLean dependency evidence")
    seen: set[str] = set()
    rows: list[dict[str, Any]] = []
    for dependency in dependencies:
        module = dependency.get("module")
        path = Path(dependency.get("path", "")).resolve()
        digest = dependency.get("sha256_after")
        _assert(isinstance(module, str) and module and path.is_file()
                and digest == dependency.get("sha256_before")
                and digest == shared.sha(path)
                and dependency.get("stable_during_compile") is True,
                f"Provider-subset dependency OLean is stale: {module}")
        relative = Path(*module.split(".")).with_suffix(".olean")
        first = next((root / relative for root in search_roots if (root / relative).is_file()), None)
        resolved_root = Path(dependency.get("resolved_search_root", "")).resolve()
        _assert(first is not None and first.resolve() == path
                and resolved_root in search_roots
                and (resolved_root / relative).resolve() == path,
                f"Provider-subset OLean is not the first LEAN_PATH match: {module}")
        seen.add(module)
        rows.append({"module": module, "path": str(path), "sha256": digest,
                     "resolved_search_root": str(resolved_root)})
    _assert(set(manifest["imports"]) <= seen,
            "Provider-subset exact imports lack OLean evidence")
    return {
        "preflight": shared.task_relative(preflight_path),
        "preflight_sha256": shared.sha(preflight_path),
        "exact_imports": manifest["imports"],
        "exact_import_oleans_present": True,
        "first_search_path_resolution_verified": True,
        "dependency_oleans": rows,
    }


def _validate_catalogs(basis: dict[str, Any]) -> dict[str, Any]:
    catalog = shared.read_json(gen.SUBSET_CATALOG, "provider subset catalog")
    records = basis["records"]
    _assert(catalog.get("artifact_kind") == "provider-source-subset-catalog"
            and catalog.get("certificate_scope") == "partial-source-only-exact-provider-request-set"
            and catalog.get("source_version") == 875
            and catalog.get("partial") is True
            and catalog.get("platform_ready") is False
            and catalog.get("usable_as_full_source_certificate") is False
            and catalog.get("full_owner_catalog") == base.task_relative(gen.FULL_CATALOG)
            and catalog.get("full_owner_catalog_sha256") == basis["full_catalog_sha256"]
            and catalog.get("full_owner_count") == 6148
            and catalog.get("subset_owner_count") == 174
            and catalog.get("provider_bundle_count") == 29
            and catalog.get("unit_plan") == base.task_relative(gen.UNIT_PLAN)
            and catalog.get("unit_plan_sha256") == base.sha_file(gen.UNIT_PLAN)
            and catalog.get("artifact_plan") == base.task_relative(gen.ARTIFACT_PLAN)
            and catalog.get("artifact_plan_sha256") == base.sha_file(gen.ARTIFACT_PLAN)
            and catalog.get("decl_graph_sha256") == basis["graph_sha256"]
            and catalog.get("bundle_coverage") == basis["bundle_coverage"]
            and catalog.get("owners") == records,
            "Provider source-subset catalog differs from the current exact 29-bundle request set")
    return {
        "path": shared.task_relative(gen.SUBSET_CATALOG),
        "sha256": shared.sha(gen.SUBSET_CATALOG),
        "rows": 174,
        "provider_bundles": 29,
        "full_owner_catalog": shared.task_relative(gen.FULL_CATALOG),
        "full_owner_catalog_sha256": basis["full_catalog_sha256"],
        "full_owner_rows_authenticated": 6148,
        "bundle_coverage": basis["bundle_coverage"],
    }


def _validate_static_shard(manifest_path: Path, basis: dict[str, Any],
                           expected: dict[str, dict[str, Any]]) -> tuple[dict[str, Any], list[dict[str, Any]], Path, Path]:
    manifest = shared.read_json(manifest_path, "provider-subset shard manifest")
    lean_path = shared.workspace_path(manifest.get("output", ""), "provider-subset Lean exporter")
    _assert(lean_path.with_suffix(".manifest.json") == manifest_path.resolve(),
            "Provider-subset manifest is not the Lean sidecar")
    _assert(manifest.get("artifact_kind") == "provider-source-subset-original-kernel-snapshot-exporter"
            and manifest.get("mode") == "provider-source-subset"
            and manifest.get("certificate_class") == "partial-source-only-exact-provider-request-set"
            and manifest.get("source_version") == 875
            and manifest.get("source_only") is True
            and manifest.get("partial") is True
            and manifest.get("platform_ready") is False
            and manifest.get("usable_as_full_source_certificate") is False
            and manifest.get("expected_subset_rows") == 174
            and manifest.get("expected_provider_bundles") == 29
            and manifest.get("shared_ir_name_domain") == "original-source-names"
            and manifest.get("imports") == base.IMPORTS,
            "Provider-subset shard scope flags are invalid")
    _assert(manifest.get("full_owner_catalog") == base.task_relative(gen.FULL_CATALOG)
            and manifest.get("full_owner_catalog_sha256") == basis["full_catalog_sha256"]
            and manifest.get("subset_catalog") == base.task_relative(gen.SUBSET_CATALOG)
            and manifest.get("subset_catalog_sha256") == shared.sha(gen.SUBSET_CATALOG),
            "Provider-subset shard catalog lineage changed")
    _assert(shared.sha(lean_path) == manifest.get("output_sha256"),
            "Provider-subset staged Lean source changed")
    checked_inputs = shared.validate_manifest_inputs(manifest)
    request_path = shared.task_path(manifest["request_manifest"], "provider-subset request manifest")
    owner_path = shared.task_path(manifest["owner_manifest"], "provider-subset owner manifest")
    requests = shared.read_json(request_path, "provider-subset requests").get("requests")
    owner_doc = shared.read_json(owner_path, "provider-subset owners")
    owners = owner_doc.get("owners")
    _assert(isinstance(requests, list) and isinstance(owners, list)
            and owner_doc.get("lineage") == basis["lineage"]
            and owner_doc.get("full_owner_catalog") == base.task_relative(gen.FULL_CATALOG)
            and owner_doc.get("full_owner_catalog_sha256") == basis["full_catalog_sha256"]
            and owner_doc.get("subset_catalog") == base.task_relative(gen.SUBSET_CATALOG)
            and owner_doc.get("subset_catalog_sha256") == shared.sha(gen.SUBSET_CATALOG),
            "Provider-subset request/owner lineage changed")
    names = [row.get("source_name") for row in requests]
    _assert(names == sorted(names)
            and names == [row.get("source_name") for row in owners]
            and len(names) == len(set(names)) == manifest.get("expected_rows"),
            "Provider-subset request/owner names or order changed")
    for request, owner in zip(requests, owners, strict=True):
        name = request["source_name"]
        planned = expected.get(name)
        _assert(planned is not None and set(request) == shared.REQUEST_KEYS,
                f"Provider-subset request is outside the authenticated subset: {name}")
        _assert(all(owner.get(key) == value for key, value in planned.items()),
                f"Provider-subset owner differs from catalog: {name}")
        _assert(all(request.get(key) == planned[key] for key in shared.REQUEST_KEYS),
                f"Provider-subset request differs from catalog: {name}")
        stage = basis["extraction"].get("stage2", {}).get("/".join(owner["source_module"].split(".")) + ".lean")
        facts = shared.workspace_path(owner["stage2_facts"], "provider-subset Stage 2 facts")
        _assert(isinstance(stage, dict)
                and stage.get("facts") == shared.workspace_relative(facts)
                and stage.get("facts_sha256") == owner.get("stage2_facts_sha256") == shared.sha(facts),
                f"Provider-subset Stage 2 facts changed: {name}")
    expected_lean = shared.expected_lean(
        shared.CORE.read_text(encoding="utf-8"), requests, manifest["snapshot_jsonl"])
    _assert(lean_path.read_bytes() == expected_lean,
            "Provider-subset Lean source is not exact core/request composition")
    return ({"manifest_inputs": checked_inputs,
             "manifest": shared.task_relative(manifest_path),
             "manifest_sha256": shared.sha(manifest_path),
             "lean_source": shared.task_relative(lean_path),
             "lean_source_sha256": shared.sha(lean_path),
             "request_manifest": shared.task_relative(request_path),
             "request_manifest_sha256": shared.sha(request_path),
             "owner_manifest": shared.task_relative(owner_path),
             "owner_manifest_sha256": shared.sha(owner_path)}, owners, lean_path, request_path)


def validate_subset(require_actual: bool = True) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    basis = gen.build_basis()
    catalog_evidence = _validate_catalogs(basis)
    expected = {row["source_name"]: row for row in basis["records"]}
    manifests = sorted(DIRECTORY.glob("ProviderSourceSubset_*.manifest.json"))
    _assert(manifests, "No provider source-subset shard manifests exist")
    all_rows: dict[str, dict[str, Any]] = {}
    shard_evidence: list[dict[str, Any]] = []
    for manifest_path in manifests:
        static, owners, lean_path, request_path = _validate_static_shard(manifest_path, basis, expected)
        if not require_actual:
            static["rows"] = len(owners)
            shard_evidence.append(static)
            continue
        manifest = shared.read_json(manifest_path, "provider-subset shard manifest")
        preflight, runtime = shared.validate_preflight(lean_path, manifest_path, manifest)
        olean = _strict_olean_evidence(lean_path, manifest_path, manifest)
        raw_sources = shared.validate_raw_sources(owners, shared.read_json(shared.SOURCE_MANIFEST, "source manifest"))
        requests = shared.read_json(request_path, "provider-subset requests")["requests"]
        output_path = shared.workspace_path(manifest["snapshot_jsonl"], "provider-subset JSONL")
        raw_lines = [line for line in output_path.read_bytes().splitlines() if line.strip()]
        _assert(len(raw_lines) == len(requests), "Provider-subset JSONL row count differs")
        row_certificates: list[dict[str, Any]] = []
        for raw_line, request in zip(raw_lines, requests, strict=True):
            name = request["source_name"]
            _assert(name not in all_rows, f"Duplicate provider-subset output row: {name}")
            row = json.loads(raw_line)
            row_certificates.append(shared.validate_row(
                row, raw_line, request, expected[name], basis["graph"], basis["graph_sha256"]))
            all_rows[name] = row
        static.update({
            "jsonl": shared.task_relative(output_path),
            "jsonl_sha256": shared.sha(output_path),
            "rows": len(raw_lines),
            "raw_sources": raw_sources,
            "preflight": preflight,
            "runtime": runtime,
            "olean_resolution": olean,
            "row_certificates": row_certificates,
        })
        shard_evidence.append(static)
    total = sum(item["rows"] for item in shard_evidence)
    _assert(total == 174, f"Provider-subset shards must contain exactly 174 requests, got {total}")
    if require_actual:
        _assert(set(all_rows) == set(expected), "Actual provider-subset JSONL does not exactly cover 174 names")
    report = {
        "schema_version": 1,
        "artifact_kind": "provider-source-subset-validation",
        "mode": "provider-source-subset",
        "validated": require_actual,
        "certificate_scope": "partial-source-only-exact-provider-request-set",
        "source_only_original_kernel_certificate": require_actual,
        "partial": True,
        "platform_ready": False,
        "usable_as_full_source_certificate": False,
        "consumer_requires_generated_kernel_comparison": True,
        "source_version": 875,
        "source_commit": basis["lineage"]["source_commit"],
        "generator": shared.task_relative(Path(gen.__file__).resolve()),
        "generator_sha256": shared.sha(Path(gen.__file__).resolve()),
        "validator": shared.task_relative(Path(__file__).resolve()),
        "validator_sha256": shared.sha(Path(__file__).resolve()),
        "shared_core_sha256": shared.sha(shared.CORE),
        "decl_graph_sha256": basis["graph_sha256"],
        "unit_plan_sha256": base.sha_file(gen.UNIT_PLAN),
        "artifact_plan_sha256": base.sha_file(gen.ARTIFACT_PLAN),
        "catalog": catalog_evidence,
        "provided_names": sorted(expected),
        "row_count": 174,
        "provider_bundle_count": 29,
        "shards": shard_evidence,
        "checks": {
            "full_6148_owner_catalog_current": True,
            "exact_29_provider_request_manifests_current": True,
            "exact_174_name_subset_covered_once": True,
            "partial_source_only_scope_explicit": True,
            "platform_readiness_not_claimed": True,
            "actual_preflight_log_runtime_oleans_current": require_actual,
            "module_owner_kind_and_graph_hashes_equal": require_actual,
            "closed_types_and_complete_definition_values": require_actual,
            "theorem_values_omitted": require_actual,
            "standard_axioms_only": require_actual,
        },
        "performance": None if not require_actual else {
            "measured_shards": len(shard_evidence),
            "measured_rows": 174,
            "preflight_seconds": [item["preflight"]["seconds"] for item in shard_evidence],
            "max_preflight_seconds": max(item["preflight"]["seconds"] for item in shard_evidence),
            "each_shard_within_300_seconds": all(
                0 < item["preflight"]["seconds"] <= 300 for item in shard_evidence),
        },
    }
    return report, all_rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-plan", action="store_true",
                      help="Validate staged scope and bytes without requiring Lean outputs")
    mode.add_argument("--certify-existing", action="store_true",
                      help="Validate existing actual preflight/JSONL evidence and write the certificate")
    args = parser.parse_args()
    report, _ = validate_subset(require_actual=args.certify_existing)
    if args.certify_existing:
        base.write_json(CERTIFICATE, report)
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
