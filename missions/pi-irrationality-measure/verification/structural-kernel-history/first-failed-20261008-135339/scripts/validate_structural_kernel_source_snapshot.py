#!/usr/bin/env python3
"""Validate the additive 74-row structural-kernel source certificate.

`--check-plan` is pure Python and does not require Lean output.
`--certify-existing` validates an already completed Root preflight and writes a
partial source-only certificate.  Neither mode starts Lean or contacts the
platform.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
from typing import Any

import generate_shared_source_snapshot as base
import generate_structural_kernel_source_snapshot as gen
import structural_kernel_snapshot as kernel
import validate_shared_source_snapshot as shared


TASK = Path(__file__).resolve().parents[1]
DIRECTORY = gen.DIRECTORY
CERTIFICATE = DIRECTORY / "StructuralKernelSource74.validation.json"


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _norm_path(path: Path) -> str:
    return os.path.normcase(str(path.resolve()))


def _command_row(facts_path: Path, offset: int) -> dict[str, Any]:
    matches: list[dict[str, Any]] = []
    for line in facts_path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        start = (((row.get("syntax") or {}).get("range") or {}).get("start") or {}).get("offset")
        if row.get("kind") == "command" and row.get("isDeclaration") is True and start == offset:
            matches.append(row)
    _assert(len(matches) == 1,
            f"Expected one authoritative Stage2 declaration command at {facts_path}:{offset}")
    return matches[0]


def _syntax_kinds(value: Any) -> list[str]:
    found: list[str] = []
    if isinstance(value, dict):
        for key in ("syntaxKind", "kind"):
            if isinstance(value.get(key), str):
                found.append(value[key])
        for child in value.get("children", []):
            found.extend(_syntax_kinds(child))
    elif isinstance(value, list):
        for child in value:
            found.extend(_syntax_kinds(child))
    return found


def validate_atomic_units(basis: dict[str, Any]) -> list[dict[str, Any]]:
    owners = {row["source_name"]: row for row in basis["records"]}
    evidence: list[dict[str, Any]] = []
    seen: set[str] = set()
    for family in basis["families"]:
        for unit in family["units"]:
            unit_id = unit["unit"]
            if unit_id in seen:
                continue
            seen.add(unit_id)
            unit_names = unit["graph_names"]
            owner = owners[unit_names[0]]
            source_path = TASK / owner["source_file"]
            facts_path = base.resolve_workspace_path(owner["stage2_facts"], "structural Stage2 facts")
            _assert(base.sha_file(source_path) == owner["source_sha256"]
                    and base.sha_file(facts_path) == owner["stage2_facts_sha256"],
                    f"Atomic structure source/facts bytes changed: {unit_id}")
            row = _command_row(facts_path, unit["start_offset"])
            syntax = row.get("syntax") or {}
            rng = syntax.get("range") or {}
            _assert((rng.get("start") or {}).get("offset") == unit["start_offset"]
                    and (rng.get("end") or {}).get("offset") == unit["end_offset"],
                    f"Atomic command Stage2 range differs: {unit_id}")
            kinds = sorted(set(_syntax_kinds(syntax)))
            structure = unit_id in {gen.PARAMETERS_STRUCTURE, gen.ADMISSIBLE_STRUCTURE}
            if structure:
                _assert("Lean.Parser.Command.structure" in kinds
                        and "Lean.Parser.Command.declaration" in kinds,
                        f"Atomic structure syntax kind is absent: {unit_id}")
                forbidden = [kind for kind in kinds if kind.startswith("Lean.Parser.Command.")
                             and any(tag in kind.lower() for tag in ("mutual", "inductive", "instance", "macro"))]
                _assert(not forbidden, f"Unsupported structure wrapper: {unit_id}: {forbidden}")
            else:
                _assert(any(kind in kinds for kind in
                            ("Lean.Parser.Command.theorem", "Lean.Parser.Command.lemma", "theorem", "lemma")),
                        f"Expected ordinary theorem command: {unit_id}")
            raw = source_path.read_bytes()[unit["start_offset"]:unit["end_offset"]]
            _assert(len(raw) == unit["end_offset"] - unit["start_offset"],
                    f"Atomic command byte range is invalid: {unit_id}")
            _assert(all(owners[name]["command_unit"] == unit_id for name in unit_names),
                    f"Atomic graph CI owner coverage differs: {unit_id}")
            evidence.append({
                "unit": unit_id,
                "source": owner["source_file"],
                "source_sha256": owner["source_sha256"],
                "facts": base.task_relative(facts_path),
                "facts_sha256": owner["stage2_facts_sha256"],
                "start_offset": unit["start_offset"],
                "end_offset": unit["end_offset"],
                "command_bytes": len(raw),
                "command_sha256": hashlib.sha256(raw).hexdigest(),
                "syntax_kind": "structure" if structure else "theorem",
                "graph_ci_count": len(unit_names),
                "graph_names": unit_names,
                "whole_command_atomic": True,
            })
    _assert(set(seen) == set(gen.TARGET_UNITS), "Atomic structural target unit set differs")
    return evidence


def validate_catalog(basis: dict[str, Any]) -> dict[str, Any]:
    catalog = shared.read_json(gen.CATALOG, "structural source catalog")
    _assert(catalog.get("artifact_kind") == "structural-kernel-source-catalog"
            and catalog.get("certificate_scope") == "partial-source-only-two-atomic-structure-families"
            and catalog.get("source_version") == 875
            and catalog.get("partial") is True
            and catalog.get("platform_ready") is False
            and catalog.get("usable_as_full_source_certificate") is False
            and catalog.get("kernel_metadata_schema") == kernel.KERNEL_METADATA_SCHEMA
            and catalog.get("recursor_rule_rhs_required") is True
            and catalog.get("lean_declaration_source") == basis["lean_declaration_source"]
            and catalog.get("lean_declaration_source_sha256") == basis["lean_declaration_source_sha256"]
            and catalog.get("constant_info_fields") == gen.CONSTANT_INFO_FIELDS
            and catalog.get("full_owner_catalog") == base.task_relative(gen.FULL_CATALOG)
            and catalog.get("full_owner_catalog_sha256") == basis["full_catalog_sha256"]
            and catalog.get("full_owner_count") == 6148
            and catalog.get("row_count") == gen.EXPECTED_ROWS
            and catalog.get("unit_plan") == base.task_relative(gen.UNIT_PLAN)
            and catalog.get("unit_plan_sha256") == base.sha_file(gen.UNIT_PLAN)
            and catalog.get("artifact_plan") == base.task_relative(gen.ARTIFACT_PLAN)
            and catalog.get("artifact_plan_sha256") == base.sha_file(gen.ARTIFACT_PLAN)
            and catalog.get("decl_graph_sha256") == basis["graph_sha256"]
            and catalog.get("families") == basis["families"]
            and catalog.get("owners") == basis["records"],
            "Structural source catalog is stale or incomplete")
    return {
        "path": base.task_relative(gen.CATALOG),
        "sha256": base.sha_file(gen.CATALOG),
        "rows": gen.EXPECTED_ROWS,
        "families": sorted(gen.FAMILIES),
        "full_owner_catalog": base.task_relative(gen.FULL_CATALOG),
        "full_owner_catalog_sha256": basis["full_catalog_sha256"],
        "lean_declaration_source": basis["lean_declaration_source"],
        "lean_declaration_source_sha256": basis["lean_declaration_source_sha256"],
    }


def validate_static_exporter(basis: dict[str, Any]) -> tuple[dict[str, Any], Path, Path, list[dict[str, Any]]]:
    manifests = sorted(DIRECTORY.glob("StructuralKernelSource_*.manifest.json"))
    _assert(len(manifests) == 1, "Structural source plan must have exactly one staged exporter")
    manifest_path = manifests[0]
    manifest = shared.read_json(manifest_path, "structural source manifest")
    lean_path = shared.workspace_path(manifest.get("output", ""), "structural source exporter")
    _assert(lean_path.with_suffix(".manifest.json") == manifest_path.resolve(),
            "Structural source manifest is not the Lean sidecar")
    _assert(manifest.get("artifact_kind") == "structural-kernel-original-source-snapshot-exporter"
            and manifest.get("schema_version") == 2
            and manifest.get("mode") == "structural-kernel-source"
            and manifest.get("certificate_class") == "partial-source-only-two-atomic-structure-families"
            and manifest.get("source_version") == 875
            and manifest.get("source_only") is True
            and manifest.get("partial") is True
            and manifest.get("platform_ready") is False
            and manifest.get("usable_as_full_source_certificate") is False
            and manifest.get("kernel_metadata_schema") == kernel.KERNEL_METADATA_SCHEMA
            and manifest.get("recursor_rule_rhs_required") is True
            and manifest.get("lean_declaration_source") == basis["lean_declaration_source"]
            and manifest.get("lean_declaration_source_sha256") == basis["lean_declaration_source_sha256"]
            and manifest.get("constant_info_fields") == gen.CONSTANT_INFO_FIELDS
            and manifest.get("imports") == base.IMPORTS
            and manifest.get("expected_rows") == gen.EXPECTED_ROWS
            and manifest.get("expected_families") == sorted(gen.FAMILIES),
            "Structural source manifest scope flags differ")
    _assert(base.sha_file(lean_path) == manifest.get("output_sha256"),
            "Structural source Lean bytes changed")
    checked_inputs = shared.validate_manifest_inputs(manifest)
    request_path = shared.task_path(manifest["request_manifest"], "structural source requests")
    owner_path = shared.task_path(manifest["owner_manifest"], "structural source owners")
    request_doc = shared.read_json(request_path, "structural requests")
    owner_doc = shared.read_json(owner_path, "structural owners")
    requests, owners = request_doc.get("requests"), owner_doc.get("owners")
    _assert(request_doc.get("schema_version") == 2
            and request_doc.get("kernel_metadata_schema") == kernel.KERNEL_METADATA_SCHEMA
            and owner_doc.get("schema_version") == 2
            and owner_doc.get("lineage") == basis["lineage"]
            and owner_doc.get("catalog") == base.task_relative(gen.CATALOG)
            and owner_doc.get("catalog_sha256") == base.sha_file(gen.CATALOG)
            and isinstance(requests, list) and isinstance(owners, list),
            "Structural request/owner manifests are invalid")
    expected_requests = [{key: row[key] for key in gen.REQUEST_FIELDS} for row in basis["records"]]
    _assert(requests == expected_requests and owners == basis["records"],
            "Structural request/owner rows differ from the authenticated 74-row basis")
    jsonl_path = (base.WORKSPACE / manifest["snapshot_jsonl"]).resolve()
    _assert(jsonl_path.is_relative_to(base.WORKSPACE), "Structural JSONL path escapes workspace")
    expected_lean = gen.render_lean(gen.CORE.read_text(encoding="utf-8"), basis["records"], jsonl_path)
    _assert(lean_path.read_text(encoding="utf-8") == expected_lean,
            "Structural source Lean is not exact core/request composition")
    return ({
        "manifest": base.task_relative(manifest_path),
        "manifest_sha256": base.sha_file(manifest_path),
        "lean_source": base.task_relative(lean_path),
        "lean_source_sha256": base.sha_file(lean_path),
        "request_manifest": base.task_relative(request_path),
        "request_manifest_sha256": base.sha_file(request_path),
        "owner_manifest": base.task_relative(owner_path),
        "owner_manifest_sha256": base.sha_file(owner_path),
        "manifest_inputs": checked_inputs,
    }, lean_path, request_path, owners)


def strict_olean_evidence(lean_path: Path, manifest_path: Path,
                          manifest: dict[str, Any]) -> dict[str, Any]:
    preflight_path = lean_path.with_suffix(lean_path.suffix + ".preflight.json")
    preflight = shared.read_json(preflight_path, "structural source preflight")
    _assert(preflight.get("source") == base.task_relative(lean_path)
            and preflight.get("manifest") == base.task_relative(manifest_path)
            and preflight.get("module_root") == base.task_relative(DIRECTORY)
            and preflight.get("actual_module_identity") == lean_path.stem
            and preflight.get("mode") == "modecheck"
            and preflight.get("output_olean") is None
            and preflight.get("output_olean_sha256") is None,
            "Structural source preflight path/module/mode differs")
    search_roots = [Path(item).resolve() for item in preflight.get("effective_lean_path", [])]
    dependencies = preflight.get("dependency_oleans")
    _assert(search_roots and isinstance(dependencies, list) and dependencies,
            "Structural source preflight lacks import OLean evidence")
    seen: set[str] = set()
    rows: list[dict[str, Any]] = []
    for dependency in dependencies:
        module = dependency.get("module")
        path = Path(dependency.get("path", "")).resolve()
        digest = dependency.get("sha256_after")
        _assert(isinstance(module, str) and path.is_file()
                and digest == dependency.get("sha256_before") == shared.sha(path)
                and dependency.get("stable_during_compile") is True,
                f"Structural source dependency OLean changed: {module}")
        relative = Path(*module.split(".")).with_suffix(".olean")
        first = next((root / relative for root in search_roots if (root / relative).is_file()), None)
        resolved_root = Path(dependency.get("resolved_search_root", "")).resolve()
        _assert(first is not None and _norm_path(first) == _norm_path(path)
                and any(_norm_path(root) == _norm_path(resolved_root) for root in search_roots)
                and _norm_path(resolved_root / relative) == _norm_path(path),
                f"Structural source OLean is not the first LEAN_PATH match: {module}")
        seen.add(module)
        rows.append({"module": module, "path": str(path), "sha256": digest,
                     "resolved_search_root": str(resolved_root)})
    _assert(set(manifest["imports"]) <= seen, "Structural source imports lack exact OLean evidence")
    return {
        "preflight": base.task_relative(preflight_path),
        "preflight_sha256": base.sha_file(preflight_path),
        "exact_imports": manifest["imports"],
        "dependency_oleans": rows,
        "first_search_path_resolution_verified": True,
    }


def validate(require_actual: bool) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    basis = gen.build_basis()
    catalog = validate_catalog(basis)
    atomic_units = validate_atomic_units(basis)
    static, lean_path, request_path, owners = validate_static_exporter(basis)
    negative = kernel.negative_fixture_results()
    _assert(all(negative.values()), "Structural metadata negative fixtures do not all reject")
    rows_by_name: dict[str, dict[str, Any]] = {}
    row_certificates: list[dict[str, Any]] = []
    actual: dict[str, Any] | None = None
    family_checks: list[dict[str, Any]] = []
    if require_actual:
        manifest_path = lean_path.with_suffix(".manifest.json")
        manifest = shared.read_json(manifest_path, "structural source manifest")
        preflight, runtime = shared.validate_preflight(lean_path, manifest_path, manifest)
        oleans = strict_olean_evidence(lean_path, manifest_path, manifest)
        raw_sources = shared.validate_raw_sources(owners, shared.read_json(shared.SOURCE_MANIFEST, "source manifest"))
        requests = shared.read_json(request_path, "structural source requests")["requests"]
        output_path = shared.workspace_path(manifest["snapshot_jsonl"], "structural source JSONL")
        raw_lines = [line for line in output_path.read_bytes().splitlines() if line.strip()]
        _assert(len(raw_lines) == len(requests) == gen.EXPECTED_ROWS,
                "Structural source JSONL row count differs from 74")
        graph = basis["graph"]
        for raw, request, owner in zip(raw_lines, requests, owners, strict=True):
            row = json.loads(raw)
            certificate = kernel.validate_row_basic(
                row, request, owner, graph, basis["graph_sha256"])
            name = row["sourceName"]
            _assert(name not in rows_by_name, f"Duplicate structural source row: {name}")
            rows_by_name[name] = row
            certificate.update({
                "jsonl_line_sha256": hashlib.sha256(raw).hexdigest(),
                "canonical_row_sha256": kernel.canonical_row_sha256(row),
            })
            row_certificates.append(certificate)
        _assert(set(rows_by_name) == {row["source_name"] for row in basis["records"]},
                "Structural source JSONL does not exactly cover the authenticated 74 Names")
        for family in basis["families"]:
            family_rows = {name: rows_by_name[name] for name in family["source_names"]}
            family_checks.append(kernel.validate_family_relationships(family_rows, family))
        actual = {
            "jsonl": base.task_relative(output_path),
            "jsonl_sha256": base.sha_file(output_path),
            "preflight": preflight,
            "runtime": runtime,
            "olean_resolution": oleans,
            "raw_sources": raw_sources,
            "row_certificates": row_certificates,
        }
    report = {
        "schema_version": 1,
        "artifact_kind": "structural-kernel-source-validation",
        "mode": "structural-kernel-source",
        "validated": require_actual,
        "certificate_scope": "partial-source-only-two-atomic-structure-families",
        "source_only_original_kernel_certificate": require_actual,
        "partial": True,
        "platform_ready": False,
        "usable_as_full_source_certificate": False,
        "consumer_requires_generated_kernel_comparison": True,
        "source_version": 875,
        "source_commit": basis["lineage"]["source_commit"],
        "kernel_metadata_schema": kernel.KERNEL_METADATA_SCHEMA,
        "recursor_rule_rhs_required": True,
        "generator": base.task_relative(Path(gen.__file__).resolve()),
        "generator_sha256": base.sha_file(Path(gen.__file__).resolve()),
        "validator": base.task_relative(Path(__file__).resolve()),
        "validator_sha256": base.sha_file(Path(__file__).resolve()),
        "structural_core": base.task_relative(gen.CORE),
        "structural_core_sha256": base.sha_file(gen.CORE),
        "decl_graph_sha256": basis["graph_sha256"],
        "unit_plan_sha256": base.sha_file(gen.UNIT_PLAN),
        "artifact_plan_sha256": base.sha_file(gen.ARTIFACT_PLAN),
        "catalog": catalog,
        "atomic_units": atomic_units,
        "provided_names": sorted(row["source_name"] for row in basis["records"]),
        "row_count": gen.EXPECTED_ROWS,
        "families": basis["families"],
        "family_kernel_checks": family_checks,
        "static_exporter": static,
        "actual_evidence": actual,
        "negative_fixtures": negative,
        "checks": {
            "complete_6148_owner_catalog_current": True,
            "exact_74_name_scope": True,
            "whole_structure_commands_atomic": True,
            "all_graph_cis_requested_once": True,
            "exact_public_name_and_actual_module_owner_required": True,
            "types_and_definition_values_required": True,
            "theorem_values_omitted": True,
            "inductive_constructor_metadata_required": True,
            "recursor_nfields_and_rule_rhs_required": True,
            "type_only_structural_claim_rejected": True,
            "actual_preflight_and_std3_checked": require_actual,
        },
        "performance": None if not require_actual else {
            "seconds": actual["preflight"]["seconds"],
            "timeout_seconds": actual["preflight"]["timeout_seconds"],
            "within_300_seconds": actual["preflight"]["seconds"] <= 300,
        },
    }
    return report, rows_by_name


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-plan", action="store_true")
    mode.add_argument("--certify-existing", action="store_true")
    args = parser.parse_args()
    report, _ = validate(require_actual=args.certify_existing)
    if args.certify_existing:
        base.write_json(CERTIFICATE, report)
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
