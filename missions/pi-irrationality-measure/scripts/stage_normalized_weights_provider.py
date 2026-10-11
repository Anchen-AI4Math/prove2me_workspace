#!/usr/bin/env python3
"""Stage the normalizedLogWeights Definition and exact structural probes.

This is a pure-Python adapter: it uses the read-only 875-module provider gate,
validates the selected source owner against the complete 6,148-name catalog,
and writes Lean exporters/import manifests without invoking Lean or APIs.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import generate_namespace_context_providers as readonly
import generate_platform_provider_bundles as producer
import generate_provider_source_subset_snapshot as subset
import generate_shared_source_snapshot as base
import structural_kernel_snapshot as kernel
import validate_ast_facts
import validate_shared_source_snapshot as shared

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification/ap3"
BATCH = "s"
MODULE = "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations"
PLATFORM_MODULE = "Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations"
NAME = "OAI.PiExponent.normalizedLogWeights"
UNIT = "OAI.NumberTheory.PiExponent.Approximation.SuccessiveApproximations:3411"
CORE = TASK / "verification/StructuralKernelSnapshotCore.inc"
FULL_CATALOG = TASK / "verification/shared-source-snapshot/complete-source/CompleteSource875.owners.json"
SUBSET_CATALOG = TASK / "verification/shared-source-snapshot/provider-subset/ProviderSourceSubset174.catalog.json"
SUBSET_VALIDATION = TASK / "verification/shared-source-snapshot/provider-subset/provider-subset-validation.json"
PROBE_DIR = DEST / BATCH / "probes"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def task_relative(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def workspace_relative(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def catalog_owner(g: Any) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    unit_plan = base.read_json(base.PREVIEW_UNIT_PLAN, "875-module unit plan")
    artifact_plan = base.read_json(base.PREVIEW_ARTIFACT_PLAN, "875-module artifact plan")
    extraction = base.read_json(base.EXTRACTION_STATE, "complete extraction state")
    complete = base.require_complete_source_inputs(unit_plan, artifact_plan, extraction)
    graph, graph_sha = base.load_decl_graph()
    expected = shared.expected_complete_source_owners(unit_plan, graph)
    _, catalog_index = subset._catalog_rows(expected, unit_plan, complete)
    units = base.unit_index(unit_plan)
    raw_owners = base.collect_complete_source_owners(units, graph)
    if NAME not in expected or NAME not in catalog_index or NAME not in raw_owners:
        raise ValueError("normalizedLogWeights is absent from the complete 6,148-name source owner set")
    owner = base.validate_owner(raw_owners[NAME], graph, graph_sha, extraction)
    expected_owner = expected[NAME]
    catalog_row = catalog_index[NAME]
    for key, value in expected_owner.items():
        if owner.get(key) != value or catalog_row.get(key) != value:
            raise ValueError("Complete source catalog/AST owner mismatch for normalizedLogWeights: " + key)
    if catalog_row != owner:
        raise ValueError("Validated AST owner differs from its full-catalog row")
    if owner["source_private"] or owner["source_module"] != MODULE or owner["command_unit"] != UNIT:
        raise ValueError("Selected owner is not the exact public source definition unit 3411")
    if owner["graph_kind"] != "def" or owner["owner_kind"] != "definition":
        raise ValueError("Selected source owner is not an ordinary definition")
    unit = units[UNIT]
    if unit.get("graph_names") != [NAME] or unit.get("category") != "definition":
        raise ValueError("Source unit 3411 is no longer the unique normalizedLogWeights definition")

    source = base.source_file_for_module(MODULE)
    facts_path = base.resolve_workspace_path(owner["stage2_facts"], "normalizedLogWeights Stage 2 facts")
    facts = [json.loads(line) for line in facts_path.read_bytes().splitlines()]
    validate_ast_facts.validate_facts(source, facts, owner["source_sha256"])

    # This certificate is an explicitly excluded partial cache. Authenticate its
    # noncoverage fact, but never use it to validate this declaration.
    subset_doc = base.read_json(SUBSET_CATALOG, "174-row partial source catalog")
    subset_names = {row.get("source_name") for row in subset_doc.get("owners", []) if isinstance(row, dict)}
    if len(subset_names) != 174 or NAME in subset_names:
        raise ValueError("The 174-row source subset unexpectedly covers normalizedLogWeights")
    return owner, {"unit_plan": unit_plan, "artifact_plan": artifact_plan, "extraction": extraction,
                   "graph": graph, "graph_sha256": graph_sha, "unit": unit,
                   "facts_path": facts_path, "source": source}, {
                   "path": task_relative(SUBSET_CATALOG), "sha256": sha(SUBSET_CATALOG),
                   "validation_path": task_relative(SUBSET_VALIDATION), "validation_sha256": sha(SUBSET_VALIDATION),
                   "row_count": len(subset_names), "target_name_present": False,
                   "used_as_validation_certificate": False}


def render_probe(request: dict[str, str], module_import: str, output: Path, probe_name: str) -> str:
    fields = [
        ("sourceName", request["source_name"]),
        ("expectedPublicName", request["expected_public_name"]),
        ("expectedModule", request["expected_module"]),
        ("graphKind", request["graph_kind"]),
        ("declGraphSha256", request["decl_graph_sha256"]),
        ("declGraphRowSha256", request["decl_graph_row_sha256"]),
        ("ownerKind", request["owner_kind"]),
        ("ownerId", request["owner_id"]),
        ("commandUnit", request["command_unit"]),
        ("familyRoot", NAME),
    ]
    body = ",\n      ".join(f"{key} := {lean_string(value)}" for key, value in fields)
    request_name = probe_name + "Requests"
    return (
        "import Lean\n"
        f"import {module_import}\n\n"
        + CORE.read_text(encoding="utf-8").rstrip()
        + "\n\nopen PiExponentStructuralKernelSnapshot\n\n"
        + f"def {request_name} : Array StructuralRequest := #[\n"
        + "    {\n      " + body + "\n    }\n  ]\n\n"
        + "run_meta do\n"
        + f"  exportStructuralSnapshotJsonl {request_name} {lean_string(workspace_relative(output))}\n"
    )


def probe_request(owner: dict[str, Any], expected_module: str, expected_name: str) -> dict[str, str]:
    return {
        "source_name": NAME,
        "source_module": expected_module,
        "expected_public_name": expected_name,
        "expected_module": expected_module,
        "graph_kind": owner["graph_kind"],
        "decl_graph_sha256": owner["decl_graph_sha256"],
        "decl_graph_row_sha256": owner["decl_graph_row_sha256"],
        "owner_kind": owner["owner_kind"],
        "owner_id": owner["owner_id"],
        "command_unit": owner["command_unit"],
        "family_root": NAME,
    }


def common_hashes(owner: dict[str, Any], facts_path: Path, provider_source: Path, provider_manifest: Path) -> dict[str, str]:
    source = base.source_file_for_module(MODULE)
    original = TASK / "source/lean" / Path(*MODULE.split(".")).with_suffix(".lean")
    paths = [
        Path(__file__).resolve(), CORE, FULL_CATALOG, SUBSET_CATALOG, SUBSET_VALIDATION,
        base.DECL_GRAPH, base.EXTRACTION_STATE, base.RUNTIME, base.PREVIEW_UNIT_PLAN, base.PREVIEW_ARTIFACT_PLAN,
        TASK / "verification/ast-unit-inventory.json", TASK / "verification/ast-scope-inventory.json",
        TASK / "verification/ast-import-inventory.json", TASK / "verification/ast-wrapper-inventory.json",
        Path(base.__file__).resolve(), Path(shared.__file__).resolve(), Path(subset.__file__).resolve(),
        Path(kernel.__file__).resolve(), Path(validate_ast_facts.__file__).resolve(),
        TASK / "scripts/generate_namespace_context_providers.py",
        TASK / "scripts/generate_platform_provider_bundles.py",
        TASK / "scripts/generate_platform_nodes.py", TASK / "scripts/generate_platform_bundles.py",
        TASK / "scripts/plan_platform_units_providers.py", source, original, facts_path,
        provider_source, provider_manifest,
        TASK / "port/lean/OAI/NumberTheory/PiExponent/Main.lean",
        TASK / "source/manifest.json",
    ]
    return {task_relative(path): sha(path) for path in paths}


def stage() -> dict[str, Any]:
    if DEST.exists():
        raise ValueError("Refusing to overwrite existing isolated ap3 stage root")
    if CORE.is_file() is False or not FULL_CATALOG.is_file() or not SUBSET_CATALOG.is_file():
        raise ValueError("Required structural core or authenticated owner catalog is missing")

    # Process-local output redirection only; frozen generator implementations and plans stay unchanged.
    producer.OUTPUT = DEST
    g = readonly.readonly_generator()
    helper = Path(__file__).resolve()
    g.input_hashes[task_relative(helper)] = sha(helper)
    bundle = g.artifact_plan["definition_bundles"].get(MODULE)
    if not isinstance(bundle, dict) or bundle.get("units") != [UNIT] or bundle.get("imports") != []:
        raise ValueError("The normalizedLogWeights bundle no longer has the exact one-unit/zero-import plan")
    risks = g.module_name_risk(MODULE)
    if risks:
        raise ValueError("Unsupported normalizedLogWeights provider boundary: " + json.dumps(risks, ensure_ascii=False))

    owner, basis, excluded_subset = catalog_owner(g)
    original_requests = g.snapshot_requests(MODULE, generated=False)
    generated_requests = g.snapshot_requests(MODULE, generated=True)
    if (len(original_requests) != 1 or len(generated_requests) != 1
            or original_requests[0]["source_graph_name"] != NAME
            or generated_requests[0]["source_graph_name"] != NAME
            or generated_requests[0]["expected_public_name"] != NAME
            or original_requests[0]["expected_kind"] != "def"
            or generated_requests[0]["expected_kind"] != "def"):
        raise ValueError("Provider snapshot requests do not describe exactly the public normalizedLogWeights def CI")

    provider_report = g.stage_bundle(MODULE, BATCH)
    provider_source = ROOT / provider_report["output"]
    provider_manifest = provider_source.with_suffix(".manifest.json")
    if not provider_source.is_file() or not provider_manifest.is_file():
        raise ValueError("Definition provider source or import manifest was not staged")
    provider_doc = json.loads(provider_manifest.read_text(encoding="utf-8"))
    if (provider_doc.get("source_module") != MODULE or provider_doc.get("platform_module") != PLATFORM_MODULE
            or provider_doc.get("selected_units") != [UNIT]
            or provider_doc.get("output_sha256") != sha(provider_source)):
        raise ValueError("Staged Definition provider does not match the exact normalizedLogWeights source unit")

    probe_dir = PROBE_DIR
    probe_dir.mkdir(parents=True, exist_ok=True)
    source_out = probe_dir / "SourceStructural.lean"
    generated_out = probe_dir / "GeneratedStructural.lean"
    source_jsonl = probe_dir / "source.jsonl"
    generated_jsonl = probe_dir / "generated.jsonl"
    source_request = probe_request(owner, MODULE, NAME)
    generated_request = probe_request(owner, PLATFORM_MODULE, NAME)
    source_request_path = probe_dir / "source-request.json"
    generated_request_path = probe_dir / "generated-request.json"
    write_json(source_request_path, source_request)
    write_json(generated_request_path, generated_request)
    source_out.write_text(render_probe(source_request, "OAI.NumberTheory.PiExponent.Main", source_jsonl,
                                       "structuralSource"), encoding="utf-8")
    generated_out.write_text(render_probe(generated_request, PLATFORM_MODULE, generated_jsonl,
                                          "structuralGenerated"), encoding="utf-8")

    hashes = common_hashes(owner, basis["facts_path"], provider_source, provider_manifest)
    hashes[task_relative(source_request_path)] = sha(source_request_path)
    hashes[task_relative(generated_request_path)] = sha(generated_request_path)
    hashes[task_relative(source_out)] = sha(source_out)
    hashes[task_relative(generated_out)] = sha(generated_out)
    hashes[task_relative(provider_source)] = sha(provider_source)
    hashes[task_relative(provider_manifest)] = sha(provider_manifest)
    owner_path = probe_dir / "source-owner.json"
    write_json(owner_path, owner)
    hashes[task_relative(owner_path)] = sha(owner_path)

    runtime = json.loads((TASK / "verification/lean-runtime.json").read_text(encoding="utf-8"))
    runtime_sha = sha(TASK / "verification/lean-runtime.json")
    source_manifest = {
        "schema_version": 1, "artifact_kind": "normalizedLogWeights-source-structural-probe-imports",
        "source_version": 875, "source_commit": provider_doc.get("source_commit"),
        "source_only": True, "partial": True, "platform_ready": False,
        "output": workspace_relative(source_out), "output_sha256": sha(source_out),
        "imports": ["Lean", "OAI.NumberTheory.PiExponent.Main"],
        "runtime_sha256": runtime_sha, "input_hashes": dict(sorted(hashes.items())),
        "snapshot_jsonl": workspace_relative(source_jsonl),
        "request_manifest": task_relative(source_request_path),
        "owner_witness": task_relative(owner_path), "owner_witness_sha256": sha(owner_path),
        "full_owner_catalog": task_relative(FULL_CATALOG), "full_owner_catalog_sha256": sha(FULL_CATALOG),
        "full_owner_count": 6148, "decl_graph_sha256": owner["decl_graph_sha256"],
        "decl_graph_row_sha256": owner["decl_graph_row_sha256"],
        "source_module": MODULE, "source_name": NAME, "command_unit": UNIT,
        "source_sha256": owner["source_sha256"], "stage2_facts": owner["stage2_facts"],
        "stage2_facts_sha256": owner["stage2_facts_sha256"],
        "source174_noncoverage_audit": excluded_subset,
        "uses_source174_certificate": False, "validated": False, "lean_started": False, "api_used": False,
        "preflight_command": (
            "python scripts/preflight_staged_module.py ap3/s/probes/SourceStructural.lean "
            "--root ap3/s/probes --imports-manifest ap3/s/probes/SourceStructural.imports.json "
            "--timeout-seconds 300"
        ),
    }
    generated_manifest = {
        "schema_version": 1, "artifact_kind": "normalizedLogWeights-generated-structural-probe-imports",
        "source_version": 875, "source_commit": provider_doc.get("source_commit"),
        "source_only": False, "partial": True, "platform_ready": False,
        "output": workspace_relative(generated_out), "output_sha256": sha(generated_out),
        "imports": ["Lean", PLATFORM_MODULE], "runtime_sha256": runtime_sha,
        "input_hashes": dict(sorted(hashes.items())),
        "snapshot_jsonl": workspace_relative(generated_jsonl),
        "request_manifest": task_relative(generated_request_path),
        "owner_witness": task_relative(owner_path), "owner_witness_sha256": sha(owner_path),
        "full_owner_catalog": task_relative(FULL_CATALOG), "full_owner_catalog_sha256": sha(FULL_CATALOG),
        "full_owner_count": 6148, "decl_graph_sha256": owner["decl_graph_sha256"],
        "decl_graph_row_sha256": owner["decl_graph_row_sha256"],
        "source_module": MODULE, "generated_module": PLATFORM_MODULE, "source_name": NAME,
        "command_unit": UNIT, "provider_source": task_relative(provider_source),
        "provider_source_sha256": sha(provider_source), "provider_manifest": task_relative(provider_manifest),
        "provider_manifest_sha256": sha(provider_manifest),
        "expected_provider_olean": "verification/staged-build/lib/lean/Definitions/Def_OAI_NumberTheory_PiExponent_Approximation_SuccessiveApproximations.olean",
        "provider_olean_sha256": None,
        "source174_noncoverage_audit": excluded_subset,
        "uses_source174_certificate": False, "validated": False, "lean_started": False, "api_used": False,
        "preflight_command": (
            "python scripts/preflight_staged_module.py ap3/s/probes/GeneratedStructural.lean "
            "--root ap3/s/probes --imports-manifest ap3/s/probes/GeneratedStructural.imports.json "
            "--timeout-seconds 300"
        ),
    }
    source_manifest_path = probe_dir / "SourceStructural.imports.json"
    generated_manifest_path = probe_dir / "GeneratedStructural.imports.json"
    write_json(source_manifest_path, source_manifest)
    write_json(generated_manifest_path, generated_manifest)

    source_manifest_sha = sha(source_manifest_path)
    generated_manifest_sha = sha(generated_manifest_path)
    definition_preflight = (
        "python scripts/preflight_staged_module.py "
        + provider_source.relative_to(TASK / "verification").as_posix()
        + " --root ap3/s/Definitions --imports-manifest ap3/s/Definitions/"
        + provider_manifest.name + " --emit-olean --timeout-seconds 300"
    )
    report = {
        "schema_version": 1, "artifact_kind": "normalizedLogWeights-definition-and-structural-probe-stage",
        "source_commit": provider_doc.get("source_commit"), "proposal_status": "Draft",
        "provider_root": "verification/ap3", "batch": BATCH, "source_module": MODULE,
        "platform_module": PLATFORM_MODULE, "selected_unit": UNIT, "source_name": NAME,
        "definition_provider": task_relative(provider_source),
        "definition_provider_sha256": sha(provider_source),
        "definition_provider_manifest": task_relative(provider_manifest),
        "definition_provider_manifest_sha256": sha(provider_manifest),
        "source_probe": task_relative(source_out), "source_probe_sha256": sha(source_out),
        "source_import_manifest": task_relative(source_manifest_path), "source_import_manifest_sha256": source_manifest_sha,
        "generated_probe": task_relative(generated_out), "generated_probe_sha256": sha(generated_out),
        "generated_import_manifest": task_relative(generated_manifest_path), "generated_import_manifest_sha256": generated_manifest_sha,
        "source_owner_witness": task_relative(owner_path), "source_owner_witness_sha256": sha(owner_path),
        "full_owner_catalog": task_relative(FULL_CATALOG), "full_owner_catalog_sha256": sha(FULL_CATALOG),
        "source174_noncoverage_audit": excluded_subset,
        "input_hashes": dict(sorted(hashes.items())),
        "definition_preflight_command": definition_preflight,
        "source_preflight_command": source_manifest["preflight_command"],
        "generated_preflight_command": generated_manifest["preflight_command"],
        "post_compile_comparison": {
            "consumer": "scripts/structural_kernel_snapshot.py:validate_row_basic, compare_rows",
            "required": ["exact public Name", "source actual owner is original module", "generated actual owner is Definitions module",
                         "kernel type", "complete ordinary Def value", "Std3 axioms"],
            "owner_mapping": {"source": MODULE, "generated": PLATFORM_MODULE},
            "only_universe_parameter_display_names_normalized": True,
        },
        "compile_flow": [definition_preflight, source_manifest["preflight_command"], generated_manifest["preflight_command"]],
        "lean_started": False, "api_used": False, "validated": False, "platform_ready": False,
        "source174_certificate_used": False,
    }
    report_path = DEST / "stage-manifest.json"
    write_json(report_path, report)
    return report


if __name__ == "__main__":
    print(json.dumps(stage(), ensure_ascii=False, indent=2))
