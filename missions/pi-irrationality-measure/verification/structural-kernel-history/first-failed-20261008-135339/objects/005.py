#!/usr/bin/env python3
"""Validate a provider containing an atomic Lean structure declaration.

This is an additive validator.  It does not change the frozen ordinary
theorem/definition validator or the 174-row source cache.  The source side is
accepted only from the separately compiled 74-row structural source
certificate.  The generated side must have an actual provider OLean and an
actual schema-v2 snapshot preflight.  InductiveVal, ConstructorVal, and
RecursorVal metadata (including every recursor rule RHS) are compared exactly.

The script never starts Lean.  ``--check-only`` stages deterministic inputs;
``--certify-existing`` verifies already captured preflights.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import generate_shared_source_snapshot as base
import generate_structural_kernel_source_snapshot as source_gen
import prepare_structural_provider_snapshot as generated_stage
import structural_kernel_snapshot as kernel
import validate_provider_bundle as ordinary
import validate_structural_kernel_source_snapshot as source_validator
from span_edits import Edit, apply_edits


TASK = Path(__file__).resolve().parents[1]
VERIFICATION = TASK / "verification"
PROVIDER_ROOT = VERIFICATION / "providers-complete-preview"
BATCH = "all-shared-safe-leaves"
RUNTIME = VERIFICATION / "lean-runtime.json"
SOURCE_CERTIFICATE = (
    VERIFICATION / "shared-source-snapshot" / "structural-kernel-74" /
    "StructuralKernelSource74.validation.json"
)
MAX_SECONDS = 300


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read(path: Path) -> Any:
    if not path.is_file():
        raise ValueError(f"Missing structural provider input: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def task_relative(path: Path) -> str:
    return path.resolve().relative_to(TASK).as_posix()


def _reconstruct_provider_source(manifest: dict[str, Any], source: Path, output: Path) -> None:
    edits = manifest.get("edits")
    _assert(isinstance(edits, list), "Provider edit ledger is absent")
    parsed: list[Edit] = []
    for row in edits:
        _assert(isinstance(row, dict) and set(row) == {"start", "end", "reason", "replacement"}
                and isinstance(row["start"], int) and isinstance(row["end"], int)
                and isinstance(row["reason"], str) and isinstance(row["replacement"], str),
                "Provider edit ledger row schema differs")
        parsed.append(Edit(row["start"], row["end"], row["replacement"].encode("utf-8"), row["reason"]))
    reconstructed = apply_edits(source.read_bytes(), parsed, manifest["source_sha256"])
    _assert(reconstructed == output.read_bytes(),
            "Provider source is not the exact authenticated byte-edit reconstruction")


def structural_check(module: str) -> dict[str, Any]:
    provider_root = ordinary.resolve_provider_root(PROVIDER_ROOT)
    complete_basis = ordinary.check_complete_provider_basis(provider_root)
    manifest_path, manifest, stem, snapshot_dir = generated_stage.locate(provider_root, module)
    basis, family = generated_stage.family_basis(manifest["source_module"])
    _assert(manifest["source_module"] == family["source_module"]
            and set(family["selected_units"]) <= set(manifest.get("selected_units", [])),
            "Provider does not contain every structural family unit")
    source = ordinary.workspace_path(manifest["source"], "ported structural source")
    original = ordinary.workspace_path(manifest["original_source"], "original structural source")
    output = ordinary.workspace_path(manifest["output"], "structural provider source")
    facts = ordinary.workspace_path(manifest["facts"], "structural Stage2 facts")
    for field, path in (("source_sha256", source), ("original_source_sha256", original),
                        ("output_sha256", output), ("facts_sha256", facts)):
        _assert(base.sha_file(path) == manifest.get(field), f"Provider {field} changed")
    _assert(manifest.get("source_commit") == ordinary.COMMIT
            and manifest.get("preview_only") is True
            and manifest.get("provisional") is True
            and manifest.get("validated") is False
            and manifest.get("submission_ready") is False
            and manifest.get("lean_started") is False
            and manifest.get("api_used") is False,
            "Provider preview status or source lineage differs")
    _assert(manifest.get("source_unchanged") is True
            and manifest.get("source_skeleton_preserved") is True
            and manifest.get("full_definition_proofs_preserved") is True
            and manifest.get("independent_byte_reconstruction_equal") is True,
            "Provider source preservation attestations are absent")
    _assert(not manifest.get("renames") and not manifest.get("deprivate_units")
            and not manifest.get("elaboration_only_helpers") and not manifest.get("kept_local_instances"),
            "Structural provider requires an unsupported rename/private/helper case")
    for rel, expected in manifest.get("input_hashes", {}).items():
        path = (TASK / rel).resolve()
        _assert(path.is_relative_to(TASK) and path.is_file() and base.sha_file(path) == expected,
                f"Provider generation input changed: {rel}")
    for key, digest_key in (("provider_plan", "provider_plan_sha256"),
                            ("provider_artifact_plan", "provider_artifact_plan_sha256")):
        path = (TASK / manifest[key]).resolve()
        _assert(path.is_relative_to(TASK) and path.is_file()
                and base.sha_file(path) == manifest[digest_key], f"{key} changed")
    ordinary.derive_expected_imports(manifest, provider_root / BATCH, stem, provider_root)
    _assert(manifest.get("imports") == sorted(set(manifest.get("imports", [])))
            and ordinary.exact_import_header(output.read_bytes(), manifest["imports"]),
            "Provider exact import header differs")
    ledger = read(provider_root / BATCH / "ledgers" / stem / "import-ledger.json")
    _assert(manifest.get("import_provenance") == ledger.get("project_import_closure_provenance"),
            "Provider import provenance differs from its ledger")
    for item in manifest.get("import_provenance", []):
        imported_source = ordinary.workspace_path(item["source"], "project import source")
        imported_facts = ordinary.workspace_path(item["facts"], "project import facts")
        _assert(base.sha_file(imported_source) == item["source_sha256"]
                and base.sha_file(imported_facts) == item["facts_sha256"],
                f"Provider import provenance bytes changed: {item.get('module')}")
    _reconstruct_provider_source(manifest, source, output)

    unit_plan = read(Path(manifest["provider_plan"]) if Path(manifest["provider_plan"]).is_absolute()
                     else TASK / manifest["provider_plan"])
    units = {row["id"]: row for row in unit_plan.get("units", []) if isinstance(row, dict) and "id" in row}
    atomic = source_validator.validate_atomic_units(basis)
    atomic_by_unit = {row["unit"]: row for row in atomic}
    for selected in family["selected_units"]:
        _assert(selected in units and selected in atomic_by_unit,
                f"Provider selected unit lacks complete-plan/AST evidence: {selected}")
        expected_unit = next(row for row in family["units"] if row["unit"] == selected)
        actual_unit = units[selected]
        _assert(actual_unit.get("module") == family["source_module"]
                and actual_unit.get("graph_names") == expected_unit["graph_names"]
                and (actual_unit.get("start") or {}).get("offset") == expected_unit["start_offset"]
                and (actual_unit.get("end") or {}).get("offset") == expected_unit["end_offset"],
                f"Provider unit differs from authenticated atomic source unit: {selected}")
    expected_names = [request["source_graph_name"] for request in
                      read(snapshot_dir / "snapshot-requests.json")["original"]
                      if request["source_graph_name"] in family["source_names"]]
    _assert(set(expected_names) == set(family["source_names"])
            and len(expected_names) == family["expected_rows"],
            "Provider snapshot requests do not exactly cover the structure family")
    plan = read(snapshot_dir / "snapshot-comparison-plan.json")
    _assert(plan.get("source_module") == family["source_module"]
            and plan.get("generated_module") == manifest["platform_module"]
            and set(expected_names) <= set(plan.get("source_graph_names", []))
            and plan.get("generated_bundle_sha256") == base.sha_file(output)
            and plan.get("validated") is False and plan.get("lean_started") is False,
            "Provider snapshot plan differs from the atomic family")
    return {
        "provider_root": task_relative(provider_root),
        "batch": BATCH,
        "complete_provider_basis": complete_basis,
        "manifest": task_relative(manifest_path),
        "manifest_sha256": base.sha_file(manifest_path),
        "provider_source": task_relative(output),
        "provider_source_sha256": base.sha_file(output),
        "source_module": manifest["source_module"],
        "platform_module": manifest["platform_module"],
        "imports": manifest["imports"],
        "selected_units": family["selected_units"],
        "family": family,
        "basis": basis,
        "stem": stem,
        "snapshot_dir": snapshot_dir,
        "expected_names": expected_names,
    }


def provider_import_manifest(result: dict[str, Any]) -> tuple[Path, dict[str, Any]]:
    path = result["snapshot_dir"] / "structural-bundle-imports.json"
    manifest = read(TASK / result["manifest"])
    document = {
        "schema_version": 2,
        "artifact_kind": "structural-provider-bundle-imports",
        "runtime_sha256": base.sha_file(RUNTIME),
        "input_hashes": {},
        "source": manifest["source"],
        "source_sha256": manifest["source_sha256"],
        "original_source": manifest["original_source"],
        "original_source_sha256": manifest["original_source_sha256"],
        "output": manifest["output"],
        "output_sha256": manifest["output_sha256"],
        "imports": manifest["imports"],
        "structural_family": result["family"]["family_root"],
        "selected_units": result["selected_units"],
    }
    return path, document


def provider_stage(result: dict[str, Any], *, write: bool) -> dict[str, Any]:
    path, document = provider_import_manifest(result)
    if write:
        base.write_json(path, document)
    else:
        _assert(read(path) == document, "Structural provider imports manifest differs")
    return {
        "source": (TASK / result["provider_source"]).relative_to(VERIFICATION).as_posix(),
        "root": (PROVIDER_ROOT / BATCH).relative_to(VERIFICATION).as_posix(),
        "manifest": path,
        "module": result["platform_module"],
        "imports": result["imports"],
        "mode": "emit-olean",
        "role": "provider-bundle",
    }


def generated_preflight_stage(stage: dict[str, Any]) -> dict[str, Any]:
    return {
        "source": stage["output"].relative_to(VERIFICATION).as_posix(),
        "root": stage["snapshot_dir"].relative_to(VERIFICATION).as_posix(),
        "manifest": stage["imports_path"],
        "module": "SnapshotGeneratedStructural",
        "imports": stage["imports"],
        "mode": "modecheck",
        "role": "generated-structural-snapshot",
    }


def replay_source_certificate(path: Path) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    _assert(path.resolve() == SOURCE_CERTIFICATE.resolve(),
            "Only the dedicated structural 74-row source certificate is accepted")
    supplied = read(path)
    replayed, rows = source_validator.validate(require_actual=True)
    _assert(supplied == replayed
            and supplied.get("validated") is True
            and supplied.get("source_only_original_kernel_certificate") is True
            and supplied.get("certificate_scope") == "partial-source-only-two-atomic-structure-families"
            and supplied.get("partial") is True
            and supplied.get("platform_ready") is False
            and supplied.get("usable_as_full_source_certificate") is False
            and supplied.get("row_count") == source_gen.EXPECTED_ROWS,
            "Structural source certificate does not equal a fresh full replay")
    return supplied, rows


def load_generated_rows(result: dict[str, Any], staged: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], list[dict[str, Any]]]:
    basis = result["basis"]
    family = result["family"]
    owner_by_name = {row["source_name"]: row for row in basis["records"]
                     if row["family_root"] == family["family_root"]}
    requests_doc = read(result["snapshot_dir"] / "snapshot-requests.json")
    generated_requests = [request for request in requests_doc["generated"]
                          if request["source_graph_name"] in family["source_names"]]
    raw_lines = [line for line in staged["jsonl"].read_bytes().splitlines() if line.strip()]
    _assert(len(raw_lines) == len(generated_requests) == family["expected_rows"],
            "Generated structural snapshot row count differs")
    rows: dict[str, dict[str, Any]] = {}
    certs: list[dict[str, Any]] = []
    for raw, provider_request in zip(raw_lines, generated_requests, strict=True):
        name = provider_request["source_graph_name"]
        owner = owner_by_name.get(name)
        _assert(owner is not None, f"Generated structural Name is outside its family: {name}")
        request = {key: owner[key] for key in source_gen.REQUEST_FIELDS}
        request["source_module"] = result["platform_module"]
        _assert(provider_request.get("expected_public_name") == name
                and provider_request.get("expected_module") == result["platform_module"]
                and provider_request.get("expected_kind") == owner["graph_kind"]
                and provider_request.get("command_unit") == owner["command_unit"]
                and provider_request.get("source_was_private") is False,
                f"Generated provider request differs from structural owner: {name}")
        row = json.loads(raw)
        certificate = kernel.validate_row_basic(
            row, request, owner, basis["graph"], basis["graph_sha256"],
            expected_module=result["platform_module"])
        _assert(name not in rows, f"Duplicate generated structural row: {name}")
        rows[name] = row
        certificate.update({
            "jsonl_line_sha256": hashlib.sha256(raw).hexdigest(),
            "canonical_row_sha256": kernel.canonical_row_sha256(row),
        })
        certs.append(certificate)
    _assert(set(rows) == set(family["source_names"]),
            "Generated snapshot does not exactly cover the structure family")
    family_for_generated = dict(family, source_module=result["platform_module"])
    kernel.validate_family_relationships(rows, family_for_generated)
    return rows, certs


def certify(result: dict[str, Any], source_certificate: Path) -> dict[str, Any]:
    provider = provider_stage(result, write=False)
    provider_evidence = ordinary.verify_preflight_record(provider)
    staged = generated_stage.expected_stage(PROVIDER_ROOT, result["source_module"], require_provider=True)
    generated_stage.check(PROVIDER_ROOT, result["source_module"], require_provider=True)
    generated = generated_preflight_stage(staged)
    generated_evidence = ordinary.verify_preflight_record(generated)
    supplied_source, source_rows = replay_source_certificate(source_certificate)
    generated_rows, generated_certs = load_generated_rows(result, staged)
    selected_source = {name: source_rows[name] for name in result["family"]["source_names"]}
    kernel.validate_family_relationships(selected_source, result["family"])
    for name in result["expected_names"]:
        kernel.compare_rows(selected_source[name], generated_rows[name],
                            result["source_module"], result["platform_module"])
    negative = kernel.negative_fixture_results()
    _assert(all(negative.values()), "Structural metadata negative fixtures failed")
    report = {
        "schema_version": 1,
        "artifact_kind": "structural-provider-kernel-validation",
        "validated": True,
        "partial_source_certificate": True,
        "platform_ready": False,
        "provider_source_ready_for_separate_publication_review": True,
        "source_snapshot_strategy": "structural-kernel-74-partial-source-cache",
        "generated_snapshot_strategy": "complete-structural-ConstantInfo-direct-public-Name",
        "source_module": result["source_module"],
        "platform_module": result["platform_module"],
        "family_root": result["family"]["family_root"],
        "selected_units": result["selected_units"],
        "compared_names": result["expected_names"],
        "row_count": len(result["expected_names"]),
        "provider_manifest": result["manifest"],
        "provider_manifest_sha256": result["manifest_sha256"],
        "provider_source": result["provider_source"],
        "provider_source_sha256": result["provider_source_sha256"],
        "source_certificate": task_relative(source_certificate),
        "source_certificate_sha256": base.sha_file(source_certificate),
        "source_certificate_validator": task_relative(Path(source_validator.__file__).resolve()),
        "source_certificate_validator_sha256": base.sha_file(Path(source_validator.__file__).resolve()),
        "source_certificate_replayed_exactly": True,
        "source_certificate_scope": supplied_source["certificate_scope"],
        "provider_preflight": provider_evidence,
        "generated_preflight": generated_evidence,
        "generated_provenance": task_relative(staged["provenance_path"]),
        "generated_provenance_sha256": base.sha_file(staged["provenance_path"]),
        "generated_jsonl": task_relative(staged["jsonl"]),
        "generated_jsonl_sha256": base.sha_file(staged["jsonl"]),
        "generated_row_certificates": generated_certs,
        "kernel_metadata_schema": kernel.KERNEL_METADATA_SCHEMA,
        "types_equal": True,
        "definition_values_equal": True,
        "axioms_equal_and_std3": True,
        "inductive_constructor_recursor_metadata_equal": True,
        "recursor_rule_nfields_and_rhs_equal": True,
        "actual_module_owners_equal_after_source_to_platform_mapping": True,
        "whole_atomic_graph_ci_coverage_equal": True,
        "negative_fixtures": negative,
        "performance": {
            "provider_seconds": provider_evidence["seconds"],
            "generated_snapshot_seconds": generated_evidence["seconds"],
            "each_under_300_seconds": (
                provider_evidence["seconds"] <= MAX_SECONDS
                and generated_evidence["seconds"] <= MAX_SECONDS
            ),
        },
        "validator": task_relative(Path(__file__).resolve()),
        "validator_sha256": base.sha_file(Path(__file__).resolve()),
        "lean_started_by_validator": False,
    }
    certificate = result["snapshot_dir"] / "provider-validation-structural.json"
    base.write_json(certificate, report)
    return {**report, "certificate": task_relative(certificate),
            "certificate_sha256": base.sha_file(certificate)}


def check_only(result: dict[str, Any]) -> dict[str, Any]:
    provider = provider_stage(result, write=True)
    staged_report = generated_stage.stage(
        PROVIDER_ROOT, result["source_module"], require_provider=False)
    negative = kernel.negative_fixture_results()
    _assert(all(negative.values()), "Structural metadata negative fixtures failed")
    return {
        "schema_version": 1,
        "artifact_kind": "structural-provider-validation-plan",
        "validated": False,
        "lean_started": False,
        "source_module": result["source_module"],
        "platform_module": result["platform_module"],
        "family_root": result["family"]["family_root"],
        "rows": result["family"]["expected_rows"],
        "selected_units": result["selected_units"],
        "provider_manifest": result["manifest"],
        "provider_manifest_sha256": result["manifest_sha256"],
        "provider_imports_manifest": task_relative(provider["manifest"]),
        "provider_imports_manifest_sha256": base.sha_file(provider["manifest"]),
        "generated_stage": staged_report,
        "source_certificate_required": task_relative(SOURCE_CERTIFICATE),
        "source_certificate_currently_validated": SOURCE_CERTIFICATE.is_file(),
        "negative_fixtures": negative,
        "provider_preflight_command": (
            "python scripts/preflight_staged_module.py " + provider["source"]
            + " --root " + provider["root"]
            + " --imports-manifest " + provider["manifest"].relative_to(VERIFICATION).as_posix()
            + " --emit-olean --timeout-seconds 300"
        ),
        "next_after_provider_preflight": (
            "python scripts/prepare_structural_provider_snapshot.py --module "
            + result["source_module"]
            + " --provider-root verification/providers-complete-preview --bind-provider"
        ),
        "generated_preflight_command_after_bind": (
            "python scripts/preflight_staged_module.py "
            + (result["snapshot_dir"] / "SnapshotGeneratedStructural.lean").relative_to(VERIFICATION).as_posix()
            + " --root " + result["snapshot_dir"].relative_to(VERIFICATION).as_posix()
            + " --imports-manifest "
            + (result["snapshot_dir"] / "structural-imports.json").relative_to(VERIFICATION).as_posix()
            + " --timeout-seconds 300"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", required=True)
    parser.add_argument("--provider-root", default="verification/providers-complete-preview")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-only", action="store_true")
    mode.add_argument("--certify-existing", action="store_true")
    parser.add_argument("--source-certificate",
                        default=task_relative(SOURCE_CERTIFICATE))
    args = parser.parse_args()
    requested_root = (TASK / args.provider_root).resolve() if not Path(args.provider_root).is_absolute() else Path(args.provider_root).resolve()
    _assert(requested_root == PROVIDER_ROOT.resolve(),
            "Structural provider validator accepts only providers-complete-preview")
    result = structural_check(args.module)
    if args.check_only:
        report = check_only(result)
    else:
        certificate = (TASK / args.source_certificate).resolve() if not Path(args.source_certificate).is_absolute() else Path(args.source_certificate).resolve()
        report = certify(result, certificate)
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
