#!/usr/bin/env python3
"""Stage a schema-v2 generated snapshot for an atomic structure provider.

The helper is isolated from the frozen ordinary fast-snapshot workflow.  It
uses exact direct public Name lookup and the complete structural ConstantInfo
exporter.  It never runs Lean.  `--bind-provider` is allowed only after the
provider bundle has an authenticated emit-OLean preflight.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import generate_shared_source_snapshot as base
import generate_structural_kernel_source_snapshot as source_gen
import validate_provider_bundle as ordinary


TASK = Path(__file__).resolve().parents[1]
VERIFICATION = TASK / "verification"
DEFAULT_PROVIDER_ROOT = VERIFICATION / "providers-complete-preview"
BATCH = "all-shared-safe-leaves"
CORE = VERIFICATION / "StructuralKernelSnapshotCore.inc"
RUNTIME = VERIFICATION / "lean-runtime.json"
VALIDATOR = TASK / "scripts" / "validate_structural_provider_bundle.py"
KERNEL_VALIDATION = TASK / "scripts" / "structural_kernel_snapshot.py"
SOURCE_VALIDATOR = TASK / "scripts" / "validate_structural_kernel_source_snapshot.py"
SOURCE_CERTIFIER = TASK / "scripts" / "certify_structural_kernel_source_snapshot.py"


def _assert(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read(path: Path) -> Any:
    if not path.is_file():
        raise ValueError(f"Missing structural provider input: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def task_relative(path: Path) -> str:
    return path.resolve().relative_to(TASK).as_posix()


def locate(provider_root: Path, module: str) -> tuple[Path, dict[str, Any], str, Path]:
    provider_root = provider_root.resolve()
    _assert(provider_root == DEFAULT_PROVIDER_ROOT.resolve(),
            "Structural provider staging currently accepts only providers-complete-preview")
    batch_root = provider_root / BATCH
    candidates: list[Path] = []
    for path in (batch_root / "Definitions").glob("*.manifest.json"):
        manifest = read(path)
        if module in (manifest.get("source_module"), manifest.get("platform_module"),
                      path.name.removesuffix(".manifest.json")):
            candidates.append(path)
    _assert(len(candidates) == 1,
            f"Expected one staged structural provider manifest for {module}; found {len(candidates)}")
    manifest_path = candidates[0]
    manifest = read(manifest_path)
    stem = manifest_path.name.removesuffix(".manifest.json")
    snapshot_dir = batch_root / "snapshots" / stem
    return manifest_path, manifest, stem, snapshot_dir


def family_basis(source_module: str) -> tuple[dict[str, Any], dict[str, Any]]:
    basis = source_gen.build_basis()
    matches = [family for family in basis["families"] if family["source_module"] == source_module]
    _assert(len(matches) == 1, f"Source module is not one of the two structural families: {source_module}")
    return basis, matches[0]


def request_lean(request: dict[str, Any], owner: dict[str, Any], family_root: str) -> str:
    fields = [
        ("sourceName", request["source_graph_name"]),
        ("expectedPublicName", request["expected_public_name"]),
        ("expectedModule", request["expected_module"]),
        ("graphKind", request["expected_kind"]),
        ("declGraphSha256", request["decl_graph_sha256"]),
        ("declGraphRowSha256", request["decl_graph_row_sha256"]),
        ("ownerKind", owner["owner_kind"]),
        ("ownerId", owner["owner_id"]),
        ("commandUnit", owner["command_unit"]),
        ("familyRoot", family_root),
    ]
    body = ",\n      ".join(f"{key} := {json.dumps(value, ensure_ascii=False)}" for key, value in fields)
    return "    {\n      " + body + "\n    }"


def expected_stage(provider_root: Path, module: str, require_provider: bool) -> dict[str, Any]:
    manifest_path, manifest, stem, snapshot_dir = locate(provider_root, module)
    basis, family = family_basis(manifest["source_module"])
    _assert(manifest.get("source_module") == family["source_module"]
            and set(family["selected_units"]) <= set(manifest.get("selected_units", [])),
            "Provider manifest does not contain every authenticated structural unit")
    provider_source = manifest_path.with_suffix("").with_suffix(".lean")
    _assert(provider_source.is_file() and base.sha_file(provider_source) == manifest.get("output_sha256"),
            "Structural provider source bytes differ from its manifest")
    request_path = snapshot_dir / "snapshot-requests.json"
    request_doc = read(request_path)
    original, generated = request_doc.get("original"), request_doc.get("generated")
    _assert(isinstance(original, list) and isinstance(generated, list)
            and len(original) == len(generated),
            "Structural provider original/generated request row counts differ")
    owners = {row["source_name"]: row for row in basis["records"]
              if row["family_root"] == family["family_root"]}
    expected_names = []
    target_generated: list[dict[str, Any]] = []
    for old, new in zip(original, generated, strict=True):
        name = old.get("source_graph_name")
        if name not in family["source_names"]:
            continue
        owner = owners.get(name)
        _assert(owner is not None and name not in expected_names,
                f"Structural provider request is absent or duplicate: {name}")
        _assert(old.get("expected_module") == family["source_module"]
                and new.get("expected_module") == manifest["platform_module"]
                and old.get("expected_public_name") == new.get("expected_public_name") == name
                and old.get("source_was_private") is False
                and new.get("source_was_private") is False
                and old.get("expected_kind") == new.get("expected_kind") == owner["graph_kind"]
                and old.get("command_unit") == new.get("command_unit") == owner["command_unit"]
                and old.get("decl_graph_sha256") == new.get("decl_graph_sha256") == owner["decl_graph_sha256"]
                and old.get("decl_graph_row_sha256") == new.get("decl_graph_row_sha256") == owner["decl_graph_row_sha256"],
                f"Structural generated request differs from authenticated owner: {name}")
        expected_names.append(name)
        target_generated.append(new)
    _assert(set(expected_names) == set(family["source_names"]),
            "Structural provider requests do not exactly cover all atomic graph CIs")

    output = snapshot_dir / "SnapshotGeneratedStructural.lean"
    jsonl = snapshot_dir / "structural-generated.jsonl"
    provenance_path = snapshot_dir / "structural-generated-provenance.json"
    imports_path = snapshot_dir / "structural-imports.json"
    provider_imports_path = snapshot_dir / "structural-bundle-imports.json"
    requests_lean = ",\n".join(
        request_lean(request, owners[request["source_graph_name"]], family["family_root"])
        for request in target_generated)
    source_text = (
        "import Lean\n"
        f"import {manifest['platform_module']}\n\n"
        + CORE.read_text(encoding="utf-8").rstrip()
        + "\n\nopen PiExponentStructuralKernelSnapshot\n\n"
        + "def structuralGeneratedRequests : Array StructuralRequest := #[\n"
        + requests_lean
        + "\n  ]\n\n"
        + "run_meta do\n"
        + f"  exportStructuralSnapshotJsonl structuralGeneratedRequests {json.dumps(base.workspace_relative(jsonl))}\n"
    )
    input_paths = [
        CORE, Path(__file__).resolve(), VALIDATOR, KERNEL_VALIDATION, SOURCE_VALIDATOR,
        SOURCE_CERTIFIER,
        source_gen.UNIT_PLAN, source_gen.ARTIFACT_PLAN, base.DECL_GRAPH, RUNTIME,
        manifest_path, provider_source, request_path,
    ]
    if require_provider:
        input_paths.append(provider_imports_path)
    input_hashes = {task_relative(path): base.sha_file(path) for path in input_paths}
    provenance = {
        "schema_version": 1,
        "strategy": "complete-structural-ConstantInfo-direct-public-Name",
        "provider_root": task_relative(provider_root),
        "batch": BATCH,
        "source_module": manifest["source_module"],
        "platform_module": manifest["platform_module"],
        "family_root": family["family_root"],
        "selected_units": family["selected_units"],
        "provider_selected_units": manifest["selected_units"],
        "expected_names": expected_names,
        "expected_rows": family["expected_rows"],
        "kernel_metadata_schema": "lean-4.33.1-ConstantInfo-complete-v1",
        "recursor_rule_rhs_required": True,
        "provider_manifest": task_relative(manifest_path),
        "provider_manifest_sha256": base.sha_file(manifest_path),
        "provider_source": task_relative(provider_source),
        "provider_source_sha256": base.sha_file(provider_source),
        "snapshot_requests": task_relative(request_path),
        "snapshot_requests_sha256": base.sha_file(request_path),
        "structural_core": task_relative(CORE),
        "structural_core_sha256": base.sha_file(CORE),
        "generated_snapshot": task_relative(output),
        "generated_snapshot_sha256": base.sha_bytes(source_text.encode("utf-8")),
        "generated_jsonl": task_relative(jsonl),
        "input_hashes": dict(sorted(input_hashes.items())),
        "actual_provider_evidence": None,
        "runnable": False,
        "validated": False,
        "lean_started": False,
    }
    provider_evidence = None
    if require_provider:
        stage = {
            "source": provider_source,
            "manifest": provider_imports_path,
            "module": manifest["platform_module"],
            "imports": manifest["imports"],
            "mode": "emit-olean",
            "role": "provider-bundle",
        }
        provider_evidence = ordinary.verify_preflight_record(stage)
        _assert(provider_evidence.get("output_olean") and provider_evidence.get("output_olean_sha256"),
                "Structural provider preflight did not emit an OLean")
        provenance["actual_provider_evidence"] = provider_evidence
        provenance["runnable"] = True
    return {
        "manifest": manifest,
        "family": family,
        "snapshot_dir": snapshot_dir,
        "output": output,
        "source_text": source_text,
        "jsonl": jsonl,
        "provenance": provenance,
        "provenance_path": provenance_path,
        "imports_path": imports_path,
        "provider_imports_path": provider_imports_path,
        "provider_evidence": provider_evidence,
        "imports": ["Lean", manifest["platform_module"]],
    }


def write_json(path: Path, value: Any) -> None:
    base.write_json(path, value)


def expected_imports_manifest(result: dict[str, Any]) -> dict[str, Any]:
    evidence = result["provider_evidence"]
    _assert(evidence is not None, "Structural generated imports require actual provider evidence")
    provider_record = TASK / evidence["record"]
    provider_log = TASK / evidence["log"]
    provider_olean = TASK / evidence["output_olean"]
    _assert(provider_record.is_file() and provider_log.is_file() and provider_olean.is_file(),
            "Structural provider evidence files are absent")
    _assert(result["output"].is_file() and result["provenance_path"].is_file(),
            "Structural generated source/provenance must be staged before binding imports")
    inputs = dict(result["provenance"]["input_hashes"])
    for path in (result["provenance_path"], provider_record, provider_log, provider_olean):
        inputs[task_relative(path)] = base.sha_file(path)
    # Emitted provider OLeans live below .../lib/lean/<Module/Path>.olean.
    module_relative = Path(*evidence["actual_module_identity"].split(".")).with_suffix(".olean")
    provider_search_root = provider_olean
    for _ in module_relative.parts:
        provider_search_root = provider_search_root.parent
    _assert((provider_search_root / module_relative).resolve() == provider_olean.resolve(),
            "Provider OLean path does not match its actual module identity")
    return {
        "schema_version": 2,
        "artifact_kind": "structural-generated-snapshot-imports",
        "runtime_sha256": base.sha_file(RUNTIME),
        "input_hashes": dict(sorted(inputs.items())),
        "output": base.workspace_relative(result["output"]),
        "output_sha256": base.sha_file(result["output"]),
        "imports": result["imports"],
        "snapshot_jsonl": base.workspace_relative(result["jsonl"]),
        "structural_provenance": task_relative(result["provenance_path"]),
        "structural_provenance_sha256": base.sha_file(result["provenance_path"]),
        "actual_import_oleans": [
            {
                "module": evidence["actual_module_identity"],
                "path": str(provider_olean.resolve()),
                "sha256": evidence["output_olean_sha256"],
                "resolved_search_root": str(provider_search_root.resolve()),
            }
        ],
    }


def stage(provider_root: Path, module: str, require_provider: bool) -> dict[str, Any]:
    result = expected_stage(provider_root, module, require_provider)
    result["snapshot_dir"].mkdir(parents=True, exist_ok=True)
    base.atomic_write(result["output"], result["source_text"].encode("utf-8"))
    write_json(result["provenance_path"], result["provenance"])
    if require_provider:
        write_json(result["imports_path"], expected_imports_manifest(result))
    return {
        "status": "runnable" if require_provider else "pending-provider-olean",
        "lean_started": False,
        "source_module": result["manifest"]["source_module"],
        "platform_module": result["manifest"]["platform_module"],
        "rows": result["family"]["expected_rows"],
        "snapshot": task_relative(result["output"]),
        "snapshot_sha256": base.sha_file(result["output"]),
        "provenance": task_relative(result["provenance_path"]),
        "provenance_sha256": base.sha_file(result["provenance_path"]),
        "imports_manifest": task_relative(result["imports_path"]) if require_provider else None,
        "preflight_command": None if not require_provider else (
            "python scripts/preflight_staged_module.py "
            f"{result['output'].relative_to(VERIFICATION).as_posix()} "
            f"--root {result['snapshot_dir'].relative_to(VERIFICATION).as_posix()} "
            f"--imports-manifest {result['imports_path'].relative_to(VERIFICATION).as_posix()} "
            "--timeout-seconds 300"
        ),
    }


def check(provider_root: Path, module: str, require_provider: bool) -> dict[str, Any]:
    expected = expected_stage(provider_root, module, require_provider)
    _assert(expected["output"].read_text(encoding="utf-8") == expected["source_text"],
            "Staged structural generated snapshot differs from reconstruction")
    _assert(read(expected["provenance_path"]) == expected["provenance"],
            "Structural generated provenance differs from reconstruction")
    if require_provider:
        _assert(read(expected["imports_path"]) == expected_imports_manifest(expected),
                "Structural generated imports manifest differs from reconstruction")
    return {
        "status": "checked-runnable" if require_provider else "checked-pending",
        "lean_started": False,
        "snapshot": task_relative(expected["output"]),
        "snapshot_sha256": base.sha_file(expected["output"]),
        "provenance": task_relative(expected["provenance_path"]),
        "provenance_sha256": base.sha_file(expected["provenance_path"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", required=True)
    parser.add_argument("--provider-root", default="verification/providers-complete-preview")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--bind-provider", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    provider_root = (TASK / args.provider_root).resolve() if not Path(args.provider_root).is_absolute() else Path(args.provider_root).resolve()
    if args.check_only:
        report = check(provider_root, args.module, require_provider=True)
    else:
        report = stage(provider_root, args.module, require_provider=args.bind_provider)
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
