"""Isolated FormalLogTruncation provider and exact equation-API staging.

Pure Python only. Frozen context stages, source catalogs and producers are read
only. An actual emitted provider OLean is required before preparing generated
snapshot/probe compiler manifests. Every new certificate remains pending.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import generate_namespace_context_providers as context
import generate_platform_provider_bundles as provider
import validate_namespace_context_providers as context_check
import prepare_fast_provider_snapshot as frozen_fast
import replay_fast_provider_snapshot_windows as windows_fast
import generate_equation_provenance_probe as equation
import preflight_staged_module as runner
from rewrite_ast_imports import external_import_union, import_edits
from skeleton_subtract import declaration_edits
from span_edits import apply_edits
from validate_ast_facts import validate_facts

TASK, ROOT, V = context.TASK, context.ROOT, context.V
DEST = V / "providers-formal-log-preview"
BATCH = DEST / "formal-log"
MODULE = equation.MODULE
STEM = "Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation"
SELF = Path(__file__).resolve()
sha, read, rel = context.sha, context.read, context.task_relative


def save(path, value):
    context_check.write_exact(path, value)


def source_bytes(path, value):
    data = value.encode("utf-8")
    if path.exists() and path.read_bytes() != data:
        raise ValueError("Preserve differing existing source first: " + rel(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def generator():
    g = context.readonly_generator()
    captured = []
    old = context.write
    try:
        context.write = lambda p, d: captured.append((p, d))
        overlay_path, overlay = context.context_overlay(g)
    finally:
        context.write = old
    if len(captured) != 1 or read(overlay_path) != overlay:
        raise ValueError("Frozen context overlay no longer matches exact AST authority")
    g.input_hashes[rel(SELF)] = sha(SELF)
    g.input_hashes[rel(Path(context_check.__file__))] = sha(Path(context_check.__file__))
    g.input_hashes[rel(Path(windows_fast.__file__))] = sha(Path(windows_fast.__file__))
    g.input_hashes[rel(Path(equation.__file__))] = sha(Path(equation.__file__))
    return g


def context_evidence(g):
    old = frozen_fast.checked_fast_generated_snapshot
    try:
        frozen_fast.checked_fast_generated_snapshot = windows_fast.checked_fast_generated_snapshot
        # One full four-module replay checks source34, actual group34, all
        # dependency records, kernel comparison and four existing certificates.
        evidence = context_check.validate_context_provider(context.MODULES[-1])
    finally:
        frozen_fast.checked_fast_generated_snapshot = old
    documents = {}
    for module in context.MODULES:
        stem = g.platform_module(module).split(".")[-1]
        path = context.DEST / "namespace-context/validation" / stem / "context-provider-validation.json"
        document = read(path)
        if not document.get("validated") or not document.get("full_def_values_equal"):
            raise ValueError("Actual context dependency certificate missing: " + module)
        documents[module] = {"path": rel(path), "sha256": sha(path)}
        g.input_hashes[rel(path)] = sha(path)
    for path in [context_check.SOURCE_CERT, context.DEST / "generated-snapshot/gi.json"]:
        g.input_hashes[rel(path)] = sha(path)
    return {"actual_readonly_context_replay": True, "certificates": documents,
            "Windows_drive_case_adapter": {"path": rel(Path(windows_fast.__file__)),
                                           "sha256": sha(Path(windows_fast.__file__))},
            "replayed_selected_module": evidence["module"]}


def reconstruct(g, manifest):
    selected = g.artifact_plan["definition_bundles"][MODULE]["units"]
    if manifest["selected_units"] != selected:
        raise ValueError("FormalLog selected command domain differs from authority")
    if manifest["renames"] or manifest["elaboration_only_helpers"] or manifest["kept_local_instances"]:
        raise ValueError("Private/rename/elaboration-only/instance case requires a separate interface")
    for key in selected:
        u = g.units[key]
        if (len(u["graph_names"]) != 1 or u["private"] or u["deprivate"]
                or u["is_instance_command"] or u["is_local_instance"]
                or u["graph_kinds"] not in [["def"], ["theorem"]]):
            raise ValueError("Unsupported nonordinary FormalLog command: " + key)
    raw = (ROOT / manifest["source"]).read_bytes()
    validate_facts(ROOT / manifest["source"], g._module_facts(MODULE), manifest["source_sha256"])
    imports = sorted(set(external_import_union(MODULE, g.imports) +
                         [g.platform_module(m) for m in g.artifact_plan["definition_bundles"][MODULE]["imports"]]))
    edits = declaration_edits(g.modules[MODULE]["units"], {g.units[k]["start"]["offset"] for k in selected})
    edits += import_edits(g.imports["modules"][MODULE]["imports"], imports)
    records = [{"start": e.start, "end": e.end, "reason": e.reason,
                "replacement": e.replacement.decode()} for e in edits]
    if (manifest["imports"] != imports or manifest["edits"] != records
            or (ROOT / manifest["output"]).read_bytes() != apply_edits(raw, edits, manifest["source_sha256"])):
        raise ValueError("Exact independent AST source subtraction/import reconstruction differs")
    return selected


def collisions(g, manifest):
    todo, modules = [MODULE], set()
    while todo:
        m = todo.pop()
        if m in modules:
            continue
        modules.add(m)
        todo.extend(g.artifact_plan["definition_bundles"][m]["imports"])
    providers = {}
    for m in sorted(modules):
        keys = list(g.artifact_plan["definition_bundles"][m]["units"])
        if m == MODULE:
            actual = manifest
        elif m in context.MODULES:
            stem = g.platform_module(m).split(".")[-1]
            actual = read(context.DEST / "namespace-context/Definitions" / (stem + ".manifest.json"))
        else:
            stem = g.platform_module(m).split(".")[-1]
            actual = read(V / "providers-complete-preview/all-shared-safe-leaves/Definitions" / (stem + ".manifest.json"))
        keys += [x["unit"] for x in actual.get("elaboration_only_helpers", [])]
        for key in keys:
            for name in g.units[key]["graph_names"]:
                if g.graph[name]["isPrivate"]:
                    raise ValueError("Public-only import closure unexpectedly contains private CI: " + name)
                prior = providers.get(name)
                if prior is not None and prior != m:
                    raise ValueError("Actual whole-import-closure duplicate public CI: " + name)
                providers[name] = m
    return {"modules": sorted(modules), "public_names": providers,
            "elaboration_only_helpers_included": True, "duplicate_public_constants": [],
            "actual_kernel_validation_required": True}


def snapshot_manifest(g, source, imports, requests, output, bindings_path, extra_pins=None):
    runtime, runtime_sha, *_ = runner.validate_runtime()
    pins = dict(g.input_hashes)
    for p in [V / "TypeOnlyTheoremSnapshotCore.inc", V / "TypeOnlyTheoremSnapshotCore.lineage.json",
              Path(frozen_fast.__file__), bindings_path]:
        pins[rel(p)] = sha(p)
    pins.update(extra_pins or {})
    module = source.stem
    return {"output": provider.workspace_relative(source), "output_sha256": sha(source),
            "imports": imports, "input_hashes": pins, "runtime_sha256": runtime_sha,
            "actual_import_oleans": runner.dependency_certificates(imports,
                runner.effective_search_path(runtime["environment"]["LEAN_PATH"]), {module}),
            "requests": requests, "expected_jsonl": rel(output),
            "source_request_bindings": rel(bindings_path), "source_request_bindings_sha256": sha(bindings_path),
            "theorem_values_null": True, "ordinary_def_values_complete": True,
            "partial_source_domain": True, "source_version": 875, "metadata_owner_count": 6148,
            "validated": False, "submission_ready": False}


def load_stage():
    g = generator()
    report_path = DEST / "generation-report.json"
    report = read(report_path)
    manifest_path = BATCH / "Definitions" / (STEM + ".manifest.json")
    manifest = read(manifest_path)
    if manifest != report["generated"] or manifest["input_hashes"] != report["input_hashes"]:
        raise ValueError("Exact FormalLog manifest/report binding differs")
    for p, digest in manifest["input_hashes"].items():
        if sha(TASK / p) != digest:
            raise ValueError("Frozen FormalLog input changed: " + p)
    reconstruct(g, manifest)
    return g, report, manifest_path, manifest


def prepare_generated():
    g, report, mp, manifest = load_stage()
    context_evidence(g)
    b = BATCH / "validation" / STEM / "b.json"
    record = context_check.record(ROOT / manifest["output"], b, "emit-olean", manifest["platform_module"], BATCH)
    requests = g.snapshot_requests(MODULE, True)
    folder = DEST / "generated-snapshot"
    source, output = folder / "SnapshotGeneratedFormalLogFast.lean", folder / "generated.jsonl"
    expected = context_check.render_group(requests, [manifest["platform_module"]], output)
    source_bytes(source, expected)
    bindings_path = BATCH / "snapshots" / STEM / "source-catalog-bindings.json"
    pins = {rel(mp): sha(mp), rel(b): sha(b), record["record"]: record["record_sha256"]}
    imports = ["Lean", manifest["platform_module"]]
    document = snapshot_manifest(g, source, imports, requests, output, bindings_path, pins)
    actual = next(d for d in document["actual_import_oleans"] if d["module"] == manifest["platform_module"])
    if actual["sha256_before"] != record["data"]["output_olean_sha256"]:
        raise ValueError("Generated snapshot does not resolve the exact emitted provider OLean")
    gi = folder / "gi.json"
    save(gi, document)
    eq_source, eq_manifest = equation_stage(g, manifest, bindings_path, record, pins)
    return {"generated_source": rel(source), "imports_manifest": rel(gi),
            "generated_equation_probe": rel(eq_source), "equation_imports_manifest": rel(eq_manifest),
            "actual_provider_olean_bound": True, "validated": False, "submission_ready": False}


def equation_stage(g, manifest, bindings_path, record=None, extra_pins=None):
    folder = DEST / "equation-provenance"
    source, output = folder / "ProbeGeneratedFormalLog.lean", folder / "generated.json"
    core = (V / "TypeOnlyTheoremSnapshotCore.inc").read_text(encoding="utf-8")
    body = ("import Lean\nimport Lean.Meta.Eqns\nimport " + manifest["platform_module"] + "\n\n" + core + equation.PROBE +
            "\nrun_meta do\n  PiExponentEquationProvenanceProbe.exportEquationSnapshot `" + equation.PRIMARY + " " +
            json.dumps(manifest["platform_module"]) + " " + json.dumps(provider.workspace_relative(output)) + " \"generated\"\n")
    source_bytes(source, body)
    original_files = [equation.STAGE / "ProbeOriginal.lean", equation.STAGE / "original.json", equation.STAGE / "probe-plan.json"]
    original_files += sorted(V.glob("preflight-ProbeOriginal-20261008-*.log"))
    witnesses = {rel(p): sha(p) for p in original_files}
    original = read(equation.STAGE / "original.json")
    if (original["expectedModule"] != MODULE or original["primaryBinding"]["actualName"] != equation.PRIMARY
            or original["actualEquationNames"] != [equation.REQUIRED]
            or original["equations"][0]["inversePrimary"] != equation.PRIMARY):
        raise ValueError("Original actual equation API witness differs from exact primary/equation pair")
    plan = {"primary_binding": equation.PRIMARY, "required_source_equation": equation.REQUIRED,
            "original_actual_witnesses": witnesses, "source_original_record_status": "legacy log/output pinned; full preflight sidecar not present here",
            "generated_probe": rel(source), "generated_probe_sha256": sha(source),
            "frozen_equation_exporter_sha256": provider.sha_bytes(equation.PROBE.encode()),
            "actual_provider_olean_required_before_generated_probe": True, "equation_names_must_come_from_Lean_Meta_API": True,
            "prefix_name_inference": False, "primary_closed_type_and_full_def_value_comparison_required": True,
            "equation_closed_type_and_Std3_comparison_required": True,
            "source18_fresh_primary_CI_required": True, "generated_certification_pending": True,
            "fresh_original_equation_api_output": rel(folder / "original.json"),
            "fresh_original_api_runs_in_source18_preflight": True,
            "validated": False, "submission_ready": False}
    # The plan is frozen before actual provider emission; actual runtime evidence
    # belongs to the later companion imports manifest, not a mutated probe plan.
    plan_path = folder / "equation-plan.json"
    save(plan_path, plan)
    import_manifest = folder / "ei.json"
    if record is not None:
        pins = dict(extra_pins or {})
        pins.update(witnesses)
        pins[rel(plan_path)] = sha(plan_path)
        pins[rel(Path(equation.__file__))] = sha(Path(equation.__file__))
        imports = ["Lean", "Lean.Meta.Eqns", manifest["platform_module"]]
        doc = snapshot_manifest(g, source, imports, [], output, bindings_path, pins)
        save(import_manifest, doc)
    return source, import_manifest


def prepare():
    if list(DEST.rglob("*.preflight.json")) or list(DEST.rglob("*validation*.json")):
        raise ValueError("Preserve existing FormalLog actual evidence before regeneration")
    g = generator()
    if g.module_name_risk(MODULE):
        raise ValueError("Unsupported FormalLog naming/context boundary: " + json.dumps(g.module_name_risk(MODULE)))
    dependencies = context_evidence(g)
    old = provider.OUTPUT
    try:
        provider.OUTPUT = DEST
        manifest = g.stage_bundle(MODULE, "formal-log")
    finally:
        provider.OUTPUT = old
    selected = reconstruct(g, manifest)
    original, generated = g.snapshot_requests(MODULE, False), g.snapshot_requests(MODULE, True)
    frozen_fast.validate_requests(original, MODULE)
    frozen_fast.validate_requests(generated, manifest["platform_module"])
    if len(original) != 18:
        raise ValueError("Only the exact18 ordinary FormalLog provider interface is supported")
    bindings = context.request_catalog_binding(g, original, generated)
    bindings_path = BATCH / "snapshots" / STEM / "source-catalog-bindings.json"
    save(bindings_path, bindings)
    whole_closure = collisions(g, manifest)
    manifest.update({"source_catalog_bindings": rel(bindings_path), "source_catalog_bindings_sha256": sha(bindings_path),
        "namespace_context_overlay": rel(context.DEST / "context-overlay.json"),
        "namespace_context_overlay_sha256": sha(context.DEST / "context-overlay.json"),
        "dependency_certificates": dependencies, "actual_import_closure_collision_check": whole_closure,
        "new_isolated_output_root": rel(DEST), "validated": False, "submission_ready": False})
    mp = BATCH / "Definitions" / (STEM + ".manifest.json")
    # stage_bundle just produced this new, uncompiled preview manifest.
    context.write(mp, manifest)
    b = BATCH / "validation" / STEM / "b.json"
    compact = {k: manifest[k] for k in ["output", "output_sha256", "source", "source_sha256", "original_source", "original_source_sha256", "imports", "input_hashes"]}
    compact["input_hashes"] = dict(compact["input_hashes"], **{rel(mp): sha(mp)})
    compact["runtime_sha256"] = sha(V / "lean-runtime.json")
    save(b, compact)
    source_folder = DEST / "source-snapshot"
    source, output = source_folder / "SourceFormalLogTruncationSnapshot.lean", source_folder / "source.jsonl"
    text = context_check.render_group(original, [MODULE], output)
    text = text.replace("import Lean\n", "import Lean\nimport Lean.Meta.Eqns\n", 1)
    equation_output = DEST / "equation-provenance/original.json"
    # Collect the exact source equation API relation in the SAME actual source18
    # run. Legacy 91-second output remains an immutable reference; it cannot
    # replace a missing sidecar or be promoted to a fresh certificate.
    text += equation.PROBE + (
        "\nrun_meta do\n  PiExponentEquationProvenanceProbe.exportEquationSnapshot `" + equation.PRIMARY + " " +
        json.dumps(MODULE) + " " + json.dumps(provider.workspace_relative(equation_output)) + " \"original\"\n")
    source_bytes(source, text)
    imports_manifest = source_folder / "si.json"
    source_manifest = snapshot_manifest(g, source, ["Lean", "Lean.Meta.Eqns", MODULE], original, output, bindings_path, {rel(mp): sha(mp)})
    source_manifest["expected_equation_api_json"] = rel(equation_output)
    source_manifest["equation_api_primary"] = equation.PRIMARY
    save(imports_manifest, source_manifest)
    generated_source = DEST / "generated-snapshot/SnapshotGeneratedFormalLogFast.lean"
    source_bytes(generated_source, context_check.render_group(generated, [manifest["platform_module"]], DEST / "generated-snapshot/generated.jsonl"))
    eq_source, _ = equation_stage(g, manifest, bindings_path)
    nodes = {k: v for k, v in g.artifact_plan["nodes"].items() if v["source_module"] == MODULE}
    report = {"generated": manifest, "input_hashes": manifest["input_hashes"], "selected_public_commands": selected,
              "source_snapshot": rel(source), "source_snapshot_manifest": rel(imports_manifest), "source_requests": len(original),
              "generated_snapshot_source": rel(generated_source), "generated_equation_probe": rel(eq_source),
              "bundle_imports_manifest": rel(b), "additional_definition_count": 1, "source_proof_nodes": nodes,
              "source_kernel_certificate_pending": True, "generated_kernel_certificate_pending": True,
              "source_full6148_certificate_claimed": False, "existing_context_evidence_unchanged": True,
              "lean_started": False, "api_used": False, "full_tree_ready": False, "submission_ready": False}
    save(DEST / "generation-report.json", report)
    return {"output_root": rel(DEST), "provider": manifest["output"], "provider_sha256": manifest["output_sha256"],
            "bundle_imports_manifest": rel(b), "source_snapshot": rel(source), "source_snapshot_imports_manifest": rel(imports_manifest),
            "source_requests": 18, "proof_nodes": len(nodes), "uncompiled": True, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--prepare-generated", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare_generated() if args.prepare_generated else prepare(), indent=2))


if __name__ == "__main__":
    main()
