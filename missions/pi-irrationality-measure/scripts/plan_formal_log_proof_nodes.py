"""Read-only source inspection for the four-node FormalLog proof frontier.

Writes only a new isolated planning report. No theorem stage, import readiness,
equation provider availability or submission certificate is granted.
"""
import argparse
import json
from pathlib import Path

import generate_formal_log_truncation_provider as formal
import generate_platform_provider_nodes as node_impl
import validate_formal_log_truncation_provider as formal_certificate
from restore_node_context import restore_context

TASK, V = formal.TASK, formal.V
DEST = V / "formal-log-nodes-preview"
NODE_DEST = DEST / "nodes"
SELF = Path(__file__).resolve()

NODE_KEYS = {
    "liftSeries_eq_toMvPowerSeries": formal.MODULE + ":356",
    "logTail_mem_rationalWeightedIdeal": formal.MODULE + ":12753",
    "shiftMap_truncatedFormalJet": formal.MODULE + ":14165",
    "formalLog_packets_surjective_iff_truncated": formal.MODULE + ":17060",
}

# These are existing, actual kernel certificates.  The new FormalLogTruncation
# provider is deliberately absent: nodes requiring it stay pending until its
# dedicated validator exposes the certified interface.
DEFINITION_CERTIFICATES = {
    "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrameDegree":
        V / "providers-complete-preview/all-shared-safe-leaves/validation/Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree/provider-validation-fast.json",
    "OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame":
        V / "providers-context-preview/namespace-context/validation/Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrame/context-provider-validation.json",
    "OAI.NumberTheory.PiExponent.Jets.JetGeometry":
        V / "providers-context-preview/namespace-context/validation/Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry/context-provider-validation.json",
    "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives":
        V / "providers-context-preview/namespace-context/validation/Def_OAI_NumberTheory_PiExponent_Jets_FormalJetDerivatives/context-provider-validation.json",
    "OAI.NumberTheory.PiExponent.Jets.FormalLogJet":
        V / "providers-context-preview/namespace-context/validation/Def_OAI_NumberTheory_PiExponent_Jets_FormalLogJet/context-provider-validation.json",
    "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation":
        V / "providers-formal-log-preview/formal-log/validation/Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation/provider-validation.json",
}


def certified_definition(module, platform_module):
    path = DEFINITION_CERTIFICATES.get(module)
    if path is None or not path.is_file():
        raise ValueError("No actual kernel certificate registered for Definition dependency: " + module)
    data = formal.read(path)
    if (data.get("validated") is not True or data.get("source_module") != module
            or data.get("platform_module") != platform_module
            or data.get("proof_axioms") != "Std3"):
        raise ValueError("Definition certificate is not the expected validated Std3 interface: " + module)
    if data.get("artifact_kind") in {"namespace-context-provider-kernel-certificate",
                                    "formal-log-provider-kernel-certificate"} and not all(
            data.get(field) is True for field in
            ("closed_types", "full_def_values_equal", "theorem_values_null", "Std3_only")):
        raise ValueError("Context Definition certificate lacks its full kernel comparison: " + module)
    olean = V / "staged-build/lib/lean" / Path(*platform_module.split(".")).with_suffix(".olean")
    if not olean.is_file():
        raise ValueError("Certified Definition OLean is missing: " + platform_module)
    return {"source_module": module, "platform_module": platform_module,
            "certificate": formal.rel(path), "certificate_sha256": formal.sha(path),
            "output_olean": formal.rel(olean), "output_lean_sha256": formal.sha(olean),
            "validated": True, "proof_axioms": "Std3"}


def prepare_compile_manifests(stage, manifest, certificates):
    """Pin exact bytes/imports for the four independent 300-second runs.

    This avoids the older standalone validator's zero-dependency-only closure
    rule and its legacy SnapshotGenerated import convention.  It does not run
    Lean and does not certify the node.
    """
    stage_certificate = stage / "certified-inputs-v2.json"
    formal.save(stage_certificate, {
        "schema_version": 1, "artifact_kind": "formal-log-node-certified-inputs",
        "node": manifest["node"], "theorem_name": manifest["theorem_name"],
        "definition_certificates": certificates, "child_certificates": [],
        "validated_node": False, "Lean_started": False, "submission_ready": False})
    common_pins = {
        formal.rel(stage / "manifest.json"): formal.sha(stage / "manifest.json"),
        formal.rel(stage_certificate): formal.sha(stage_certificate),
        formal.rel(SELF): formal.sha(SELF),
    }
    for row in certificates:
        common_pins[row["certificate"]] = row["certificate_sha256"]
        common_pins[row["output_olean"]] = row["output_lean_sha256"]
    source_module = manifest["source_components"][0]["source_module"]
    result = {}
    for index, filename in enumerate(manifest["outputs_sha256"], 1):
        source = stage / filename
        if filename == "SnapshotOriginal.lean":
            imports = ["Lean", source_module]
        else:
            imports = manifest["imports"]
        compilation_manifest = stage / (f"compile-v2-{index}.json")
        formal.save(compilation_manifest, {
            "schema_version": 1, "artifact_kind": "formal-log-node-file-import-certificate",
            "output": source.relative_to(formal.ROOT).as_posix(),
            "output_sha256": formal.sha(source), "imports": imports,
            "input_hashes": common_pins, "runtime_sha256": manifest["runtime_sha256"],
            "node": manifest["node"], "node_validated": False,
            "timeout_seconds": 300, "Lean_started": False, "submission_ready": False})
        result[filename] = {"manifest": formal.rel(compilation_manifest),
                            "manifest_sha256": formal.sha(compilation_manifest)}
    return result


def stage_node(requested):
    key = NODE_KEYS.get(requested, requested)
    if key not in NODE_KEYS.values():
        raise ValueError("Requested theorem is outside the four-node FormalLog frontier")
    old_dest = node_impl.DEST
    try:
        node_impl.DEST = NODE_DEST
        generator = node_impl.ProviderNodeGenerator()
        equation = None
        if key == NODE_KEYS["formalLog_packets_surjective_iff_truncated"]:
            equation = formal_certificate.validate_equation_certificate()
            certificate = equation["data"]
            if (certificate.get("required_source_equation") !=
                    "OAI.PiExponent.FormalLogTruncation.shiftMap.eq_1"
                    or certificate.get("generated_provider_availability_established") is not True
                    or certificate.get("prefix_name_inference") is not False):
                raise ValueError("Exact certified shiftMap equation interface is unavailable")
            preserved = generator.g.unit_plan["preserved_generated_commands"]
            if certificate["required_source_equation"] not in preserved:
                # Per-instance certified adapter only.  The frozen/global plan
                # and producer remain byte-for-byte unchanged.
                generator.g.unit_plan = dict(generator.g.unit_plan)
                generator.g.unit_plan["preserved_generated_commands"] = [
                    *preserved, certificate["required_source_equation"]]
        generated = generator.generate(key)
    finally:
        node_impl.DEST = old_dest
    stage = formal.TASK / generated["stage"]
    manifest = formal.read(stage / "manifest.json")
    certificates = [certified_definition(row["source_module"], row["platform_module"])
                    for row in manifest["definition_dependency_witnesses"]]
    if manifest["child_nodes"]:
        raise ValueError("Child node certificates must be supplied by the isolated validator before staging this node")
    compile_manifests = prepare_compile_manifests(stage, manifest, certificates)
    if equation is not None:
        equation_binding = {"certificate": equation["path"], "certificate_sha256": equation["sha256"],
                            "required_equation": equation["data"]["required_source_equation"],
                            "getter": equation["data"]["getter"], "inverse_getter": equation["data"]["inverse_getter"],
                            "inverse_primary": equation["data"]["inverse_primary"],
                            "global_plan_modified": False, "validated": True}
        formal.save(stage / "certified-equation-adapter.json", equation_binding)
    else:
        equation_binding = None
    result = {**generated, "certified_definition_dependencies": len(certificates),
              "compile_manifests": compile_manifests, "pure_python_prepared": True,
              "equation_adapter": equation_binding,
              "Lean_started": False, "validated": False, "submission_ready": False}
    formal.save(stage / "preparation-v2.json", result)
    return result


def check_staged_node(requested):
    key = NODE_KEYS.get(requested, requested)
    generator = node_impl.ProviderNodeGenerator()
    name = generator.node_name(key)
    stage = NODE_DEST / name.replace(".", "_")
    manifest = formal.read(stage / "manifest.json")
    preparation = formal.read(stage / "preparation-v2.json")
    if manifest["node"] != key or preparation["node"] != key:
        raise ValueError("Staged node identity differs")
    checked = {}
    for filename, item in preparation["compile_manifests"].items():
        source = stage / filename
        compilation_manifest = formal.TASK / item["manifest"]
        if formal.sha(compilation_manifest) != item["manifest_sha256"]:
            raise ValueError("Compilation manifest changed: " + filename)
        data = formal.read(compilation_manifest)
        formal.runner.verify_manifest_inputs(data)
        formal.runner.verify_source_certificate(source, data)
        imports = formal.runner.certified_imports(source, data)
        checked[filename] = {"source_sha256": formal.sha(source), "imports": len(imports),
                             "manifest_sha256": item["manifest_sha256"]}
    return {"node": key, "theorem_name": name, "exact_file_and_import_pins_checked": True,
            "files": checked, "Lean_started": False, "validated": False,
            "submission_ready": False}


def plan():
    g, provider_report, manifest_path, provider_manifest = formal.load_stage()
    n = node_impl.ProviderNodeGenerator.__new__(node_impl.ProviderNodeGenerator)
    n.preview, n.g = True, g
    n.runtime_sha = formal.sha(V / "lean-runtime.json")
    n.core_path = V / "TypeOnlyTheoremSnapshotCore.inc"
    n.core_sha = formal.sha(n.core_path)
    n.cache, n.layout_cache, n.inventory_cache = {}, {}, {}
    nodes = provider_report["source_proof_nodes"]
    edges = {key: set(row["node_dependencies"]) for key, row in nodes.items()}
    order = []
    while edges:
        ready = sorted(k for k, deps in edges.items() if not deps)
        if not ready:
            raise ValueError("FormalLog proof frontier is cyclic or lacks an external child")
        order += ready
        for key in ready:
            del edges[key]
        for deps in edges.values():
            deps.difference_update(ready)
    reports = []
    for key in order:
        p, unit = nodes[key], g.units[key]
        raw, facts, _, origin = n.load_module(unit["module"])
        scope = g.scope_for(unit)
        restored = restore_context(raw, facts, scope, origin["source_sha256"])
        row = {"node": key, "theorem_name": p["theorem_name_before_platform_renames"],
               "source_unit": unit, "source_witness": origin,
               "source_namespace": scope["namespace"], "source_scope": scope,
               "restored_scope_preview": restored,
               "planned_child_nodes": p["node_dependencies"],
               "planned_definition_modules": p["definition_modules"],
               "planned_inline_units": p["inline_units"],
               "inline_source_ranges": [{"unit": k, "names": g.units[k]["graph_names"],
                    "start": g.units[k]["start"], "end": g.units[k]["end"],
                    "source_private": g.units[k]["private"]} for k in p["inline_units"]],
               "source_private_inline_units": [k for k in p["inline_units"] if g.units[k]["private"]],
               "desired_solution_shape": "literal theorem solution at namespace root, original active section/context restored",
               "stage_files_to_verify": ["Thm", "Sol", "SnapshotOriginal", "SnapshotGenerated"],
               "each_file_timeout_seconds": 300,
               "public_inline_CI_type_and_Std3_comparison_required": True,
               "imported_Theorems_contain_statement_stubs": True,
               "generated_Sol_Std3_proves_stubs_are_not_used": False,
               "validated": False, "submission_ready": False}
        try:
            layout = n.node_layout(key)
            inventory = n.import_collision_inventory(key)
            row.update({"layout_status": "source-preview-only", "elaboration_only_helpers": layout["elaboration_only_helpers"],
                        "whole_import_closure_inventory": inventory,
                        "planned_definition_closure": sorted(layout["definitions"]),
                        "actual_Def_and_child_certificates_required_before_generation_claim": True})
        except ValueError as error:
            row.update({"layout_status": "strictly-refused", "refusal": str(error),
                        "actual_equation_certificate_required_before_retry": True})
            helper = next(u for u in g.modules[formal.MODULE]["units"] if u["graph_names"] ==
                          ["OAI.PiExponent.FormalLogTruncation.shiftEquiv_apply"])
            a, b = helper["valueStart"]["offset"], helper["end"]["offset"]
            value = raw[a:b].decode().replace("\r\n", "\n").strip()
            if value != ":= rfl" or helper["privateTok"] or helper["is_local_instance"]:
                raise ValueError("Final pending helper is not the exact atomic public rfl source binding")
            helper_graph = g.graph[helper["graph_names"][0]]
            row["pending_rfl_helper"] = {"unit": formal.MODULE + ":" + str(helper["start"]["offset"]), "source_graph_name": helper["graph_names"][0],
                "source_command_range": {"start": helper["start"], "end": helper["end"]},
                "source_value_range": {"start": helper["valueStart"], "end": helper["end"]},
                "source_value_text": value, "actual_project_kernel_deps": sorted(set(helper_graph["typeDeps"] + helper_graph["valueDeps"] + helper_graph["constructors"])),
                "required_equation": "OAI.PiExponent.FormalLogTruncation.shiftMap.eq_1",
                "generated_equation_getter_and_inverse_primary_cert_required": True,
                "helper_statement_kernel_type_and_proof_Std3_still_required": True,
                "availability_granted": False, "global_plan_modified": False}
        reports.append(row)
    pins = dict(provider_manifest["input_hashes"])
    for path in [SELF, manifest_path, formal.DEST / "generation-report.json", Path(node_impl.__file__),
                 TASK / "scripts/restore_node_context.py", TASK / "scripts/private_node_binding.py",
                 TASK / "scripts/platform_statement.py", TASK / "scripts/generate_platform_nodes.py"]:
        pins[formal.rel(path)] = formal.sha(path)
    report = {"schema_version": 1, "artifact_kind": "isolated-formal-log-proof-node-plan",
              "source_module": formal.MODULE, "node_order": order, "nodes": reports,
              "input_hashes": pins, "decl_graph_sha256": g.graph_sha,
              "source_equation_and_provider_certificate_location_pending": True,
              "generator_constructor_write_path_not_called": True,
              "existing_frozen_sources_unchanged": True, "Lean_started": False, "API_used": False,
              "proof_node_files_generated": False, "validated": False, "submission_ready": False,
              "next_actual_sequence": [
                  "certify source18 and its same-run original equation API result",
                  "emit/certify DefFormalLogTruncation and generated18 plus generated equation API pair",
                  "stage and verify :356 four exact files, then publish its statement/proof",
                  "stage and verify :12753 and :14165 four files with actual :356 certificate/import",
                  "accept only certified exact equation relationship for :17060's rfl helper; keep full helper CI checks",
                  "stage and verify :17060 with both actual child certificates and literal root theorem solution"]}
    # This report never pins ongoing actual-output JSONLs/sidecars; it pins only
    # the frozen source/AST plans being inspected during the root's compiler run.
    formal.save(DEST / "node-plan.json", report)
    return {"plan": formal.rel(DEST / "node-plan.json"), "plan_sha256": formal.sha(DEST / "node-plan.json"),
            "nodes": len(reports), "strict_refusals": [r["node"] for r in reports if r["layout_status"] == "strictly-refused"],
            "proof_node_files_generated": False, "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--stage-node", choices=sorted(NODE_KEYS))
    mode.add_argument("--check-stage", choices=sorted(NODE_KEYS))
    args = parser.parse_args()
    result = (stage_node(args.stage_node) if args.stage_node else
              check_staged_node(args.check_stage) if args.check_stage else plan())
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
