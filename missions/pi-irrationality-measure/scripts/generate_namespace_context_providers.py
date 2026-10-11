#!/usr/bin/env python3
"""Isolated AST-owned namespace-context provider overlay; no Lean/network.

The fixed four-module preview retains original scopes and real declarations.
Existing plans, 29 providers, producer, source catalog and certificates are read
only. Public source snapshot requests bind exact complete-catalog owner rows,
but metadata coverage never claims an actual source CI certificate.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path

import generate_platform_bundles as base
import generate_platform_provider_bundles as provider
from prepare_fast_provider_snapshot import FAST_RESOLVER, OLD_RESOLVER, validate_requests
from plan_platform_artifacts import build_artifacts
from plan_platform_units_providers import promote
from preflight_staged_module import validate_runtime, effective_search_path, dependency_certificates

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK/"verification"
DEST = V/"providers-context-preview"
PLAN_DIR = V/"provider-plans/all-shared-public"
CATALOG = V/"shared-source-snapshot/complete-source/CompleteSource875.owners.json"
SOURCE_SUBSET = V/"shared-source-snapshot/provider-subset/provider-subset-validation.json"
MODULES = ["OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame",
           "OAI.NumberTheory.PiExponent.Jets.JetGeometry",
           "OAI.NumberTheory.PiExponent.Jets.FormalJetDerivatives",
           "OAI.NumberTheory.PiExponent.Jets.FormalLogJet"]
CONSUMER = MODULES[-1]
NAMESPACE = "OAI.PiExponent.FormalJetDerivatives"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def task_relative(path):
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")


def comparable(value):
    return {k:v for k,v in value.items() if k not in {"provisional","ready_for_generation"}}


def readonly_generator():
    """Use the existing checked engine WITHOUT its live-inventory write path."""
    g = provider.ProviderGenerator.__new__(provider.ProviderGenerator)
    base.Generator.__init__(g, preview=True)
    if (not g.state.get("complete") or len(g.state["stage2"]) != 875
            or not g.inventory.get("complete_extraction") or g.inventory["extracted_modules"] != 875):
        raise ValueError("Namespace overlay requires complete exact 875-module metadata")
    g.base_unit_plan, g.base_artifact_plan = g.unit_plan, g.artifact_plan
    g.provider_unit_path = PLAN_DIR/"platform-unit-plan-provider-variant.json"
    g.provider_artifact_path = PLAN_DIR/"platform-artifact-plan-provider-variant.json"
    g.provider_manifest_path = PLAN_DIR/"provider-plan-manifest.json"
    manifest = read(g.provider_manifest_path)
    if manifest["basis"] != "verified complete 875-module preview":
        raise ValueError("Incomplete provider-plan basis")
    for relative, expected in manifest["input_hashes"].items():
        if sha(provider.resolve_recorded_input(relative)) != expected:
            raise ValueError("Provider plan input changed: "+relative)
    stored = read(g.provider_unit_path)
    roots = set(stored["provider_variant"]["root_units"])
    fresh, closure = promote(g.base_unit_plan, roots, "all-shared-public")
    if comparable(fresh) != comparable(stored):
        raise ValueError("Provider promotion differs from its frozen plan")
    artifacts = read(g.provider_artifact_path)
    rebuilt = build_artifacts(fresh, g.scopes, g.reuse)
    rebuilt["provider_variant"] = fresh["provider_variant"]
    if comparable(rebuilt) != comparable(artifacts):
        raise ValueError("Provider artifact plan differs from fresh authoritative rebuild")
    g.unit_plan, g.artifact_plan = stored, copy.deepcopy(artifacts)
    g.units = {x["id"]:x for x in stored["units"]}
    g.owner = {name:x["id"] for x in stored["units"] for name in x["graph_names"]}
    g.provider_roots, g.provider_closure = roots, closure
    g.graph_rows, g.graph_row_hashes, g.graph_sha = provider.load_graph_rows(V/"decl_graph.jsonl")
    g.new_private_units = {k for k in closure if g.units[k]["private"]
                           and {x["id"]:x for x in g.base_unit_plan["units"]}[k]["category"] not in base.DEFINITION_CATEGORIES}
    g._facts_by_module = {}
    # The pure builder reads existing exact source/facts; no frozen inventory is
    # rewritten even if its last capture observation differs.
    g.imports = provider.build_live_import_inventory(g.state)
    g.capture_observations = {"extraction_state":{"path":"verification/extraction-state.json",
        "sha256_at_capture":sha(V/"extraction-state.json"),"stage2_entries_at_capture":875,"complete_at_capture":True,
        "dependency":False,"reason":"selected per-module source/facts are exact dependencies"},
        "live_import_inventory":{"path":None,"written":False,"dependency":False,
        "reason":"rebuilt in memory; existing inventory untouched"}}
    for p in [g.provider_unit_path,g.provider_artifact_path,g.provider_manifest_path,Path(provider.__file__),
              Path(__file__),TASK/"scripts/plan_platform_units_providers.py",CATALOG,SOURCE_SUBSET]:
        g.input_hashes[task_relative(p)] = sha(p)
    return g


def dag_order(bundles):
    remaining = {m:set(b["imports"]) & set(bundles) for m,b in bundles.items()}
    order = []
    while remaining:
        ready = sorted(m for m,deps in remaining.items() if not deps)
        if not ready:
            raise ValueError("Namespace context edge creates a Definition cycle")
        order.extend(ready)
        for m in ready:del remaining[m]
        for deps in remaining.values():deps.difference_update(ready)
    return order


def context_overlay(g):
    bundle = g.artifact_plan["definition_bundles"][CONSUMER]
    risks = g.module_boundary_risks(CONSUMER)
    expected = [x for x in risks if x.get("owner_module") == MODULES[2]
                and x.get("resolved_prefixes") == [NAMESPACE]
                and x.get("reason") == "retained open namespace has a unique project owner module not imported"]
    if len(expected) != 1 or risks != expected:
        raise ValueError("Overlay supports exactly the authenticated FormalJetDerivatives retained-open case")
    risk = expected[0]
    fact_matches = [f for f in g._module_facts(CONSUMER) if f["kind"] == "command"
                    and f["syntax"]["range"] == risk["command_range"]]
    if len(fact_matches) != 1 or fact_matches[0]["syntax"]["syntaxKind"] != "Lean.Parser.Command.open":
        raise ValueError("Namespace context has no unique complete authoritative open command")
    syntax = fact_matches[0]["syntax"]
    identifiers = [x for x in provider.walk_syntax(syntax) if x.get("identifier")]
    if len(identifiers) != 1 or identifiers[0]["identifier"] != risk["identifier"]:
        raise ValueError("Mixed/ambiguous open command is unsupported")
    consumers = [k for k in bundle["units"] if any(x["range"] == risk["command_range"]
                 for x in g.scope_for(g.units[k])["context_commands"])]
    if not consumers:
        raise ValueError("Open command is not authoritative active context for retained declarations")
    owner = MODULES[2]
    owner_units = g.artifact_plan["definition_bundles"][owner]["units"]
    witness_names = sorted(n for k in owner_units for n in g.units[k]["graph_names"]
        if not g.graph[n]["isPrivate"] and g.graph[n]["module"] == owner
        and (n == NAMESPACE or n.startswith(NAMESPACE+".")))
    if not witness_names:
        raise ValueError("Namespace provider retains no actual public graph declaration under the namespace")
    raw_path = TASK/"port/lean"/Path(*CONSUMER.split(".")).with_suffix(".lean")
    a,b = risk["command_range"]["start"]["offset"],risk["command_range"]["end"]["offset"]
    raw_command = raw_path.read_bytes()[a:b]
    old_imports = list(bundle["imports"])
    bundle["imports"] = sorted(set(old_imports)|{owner})
    g.artifact_plan["definition_order"] = dag_order(g.artifact_plan["definition_bundles"])
    if g.module_boundary_risks(CONSUMER):
        raise ValueError("Authenticated context owner did not resolve all boundary risks")
    result = {"schema_version":1,"base_provider_artifact_plan":task_relative(g.provider_artifact_path),
        "base_provider_artifact_plan_sha256":sha(g.provider_artifact_path),"source_module":CONSUMER,
        "original_definition_imports":old_imports,"overlay_definition_imports":bundle["imports"],
        "context_dependencies":[{"owner_module":owner,"resolved_namespace":NAMESPACE,
            "command_range":risk["command_range"],"identifier_range":identifiers[0]["range"],
            "command_bytes_sha256":hashlib.sha256(raw_command).hexdigest(),
            "command_text":raw_command.decode("utf-8"),"syntaxKind":syntax["syntaxKind"],
            "active_retained_units":consumers,"provided_public_graph_names":witness_names,
            "owning_module_matches_graph":True,"namespace_available_only_after_actual_provider_compile":True}],
        "definition_dag_acyclic":True,"new_unit_promotions":[],"dummy_namespace_commands":[],
        "shared_global_plan_modified":False,"validated":False,"submission_ready":False}
    path = DEST/"context-overlay.json"
    write(path,result)
    g.input_hashes[task_relative(path)] = sha(path)
    return path,result


def request_catalog_binding(g, original, generated):
    names=[x["source_graph_name"] for x in original]
    if (len(original)!=len(generated) or len(set(names))!=len(names)
            or names!=[x["source_graph_name"] for x in generated]):
        raise ValueError("Original/generated source request domains differ or duplicate Names")
    catalog = read(CATALOG)
    if (catalog["source_version"] != 875 or catalog["owner_count"] != 6148
            or catalog["decl_graph_sha256"] != g.graph_sha
            or catalog["unit_plan_sha256"] != sha(V/"platform-unit-plan-preview.json")):
        raise ValueError("Complete source owner catalog basis changed")
    owners = {x["source_name"]:x for x in catalog["owners"]}
    if len(owners) != catalog["owner_count"]:
        raise ValueError("Complete source owner catalog has duplicate Names")
    subset = read(SOURCE_SUBSET)
    if (subset["validated"] is not True or subset["row_count"] != 174
            or subset["decl_graph_sha256"] != g.graph_sha
            or subset["catalog"]["full_owner_catalog_sha256"] != sha(CATALOG)):
        raise ValueError("Invalid source subset certificate")
    cached = set(subset["provided_names"])
    records = []
    for req,new in zip(original,generated):
        owner = owners.get(req["source_graph_name"])
        unit=g.units.get(req["command_unit"])
        if (owner is None or owner["source_module"] != req["expected_module"]
                or owner["command_unit"] != req["command_unit"] or owner["graph_kind"] != req["expected_kind"]
                or owner["decl_graph_sha256"] != req["decl_graph_sha256"]
                or owner["decl_graph_row_sha256"] != req["decl_graph_row_sha256"]
                or owner["source_private"] != req["source_was_private"] or unit is None
                or req["source_graph_name"] not in unit["graph_names"]
                or owner["source_sha256"] != g.modules[req["expected_module"]]["source_sha256"]
                or owner["stage2_facts_sha256"] != g.state["stage2"][req["expected_module"].replace(".","/")+".lean"]["facts_sha256"]
                or owner["unit_start_offset"] != unit["start"]["offset"]
                or owner["unit_end_offset"] != unit["end"]["offset"]):
            raise ValueError("Snapshot request differs from exact full-catalog owner row: "+req["source_graph_name"])
        records.append({"source_graph_name":req["source_graph_name"],"complete_catalog_owner":owner,
            "owner_row_sha256":hashlib.sha256(json.dumps(owner,sort_keys=True,separators=(",",":"),ensure_ascii=False).encode()).hexdigest(),
            "generated_request":new,"source_subset174_claimed_coverage":req["source_graph_name"] in cached,
            "metadata_binding_only":True,"actual_source_kernel_comparison_required":True})
    return {"full_source_catalog":task_relative(CATALOG),"full_source_catalog_sha256":sha(CATALOG),
        "full_source_owner_count":6148,"source_subset_certificate":task_relative(SOURCE_SUBSET),
        "source_subset_certificate_sha256":sha(SOURCE_SUBSET),"requests":records,
        "actual_source_certificate_outside174_pending":any(x["source_graph_name"] not in cached for x in records),
        "generated_kernel_certificate_pending":True,"validated":False}


def source_fast_group(g, reports):
    requests=[]
    for report in reports:
        module=report["source_module"]
        rows=g.snapshot_requests(module,False)
        validate_requests(rows,module)
        requests.extend(rows)
    if len({x["source_graph_name"] for x in requests}) != len(requests):
        raise ValueError("Grouped original source requests duplicate public Names")
    core=V/"TypeOnlyTheoremSnapshotCore.inc"
    folder=DEST/"source-snapshot"
    folder.mkdir(parents=True,exist_ok=True)
    source,output=folder/"ContextSourceSnapshot.lean",folder/"source.jsonl"
    body="import Lean\n"+"".join("import "+m+"\n" for m in MODULES)+"\n"+core.read_text(encoding="utf-8").rstrip()+"\n\n"
    if provider.PROVIDER_EXPORTER.count(OLD_RESOLVER)!=1:
        raise ValueError("Frozen exporter public resolver anchor changed")
    exporter=provider.PROVIDER_EXPORTER.replace(OLD_RESOLVER,FAST_RESOLVER,1)
    axiom_anchor='''    let row := Json.mkObj [
'''
    if exporter.count(axiom_anchor)!=1:
        raise ValueError("Source-fast CI exporter axiom guard anchor changed")
    exporter=exporter.replace(axiom_anchor,'''    unless axiomNames.all (fun n => n == "propext" || n == "Classical.choice" || n == "Quot.sound") do
      throwError "Source-fast CI contains nonstandard axioms: {name}"
'''+axiom_anchor,1)
    body+=exporter
    body+="\nopen PiExponentProviderSnapshot\n\ndef providerRequests : Array ProviderRequest := #[\n"
    body+=",\n".join(provider.render_request(x) for x in requests)+"\n  ]\n\nrun_meta do\n"
    body+="  exportProviderSnapshotJsonl providerRequests "+provider.lean_string(provider.workspace_relative(output))+"\n"
    source.write_text(body,encoding="utf-8")
    runtime,runtime_sha,*_=validate_runtime()
    dependencies=dependency_certificates(["Lean",*MODULES],effective_search_path(runtime["environment"]["LEAN_PATH"]),{"ContextSourceSnapshot"})
    bindings=request_catalog_binding(g,requests,requests)
    bindings["purpose"]="exact source-only original public CI snapshot; generated provider comparison remains required"
    bindings_path=folder/"source-request-bindings.json"
    write(bindings_path,bindings)
    pins=dict(g.input_hashes)
    for path in [core,Path(__file__),TASK/"scripts/prepare_fast_provider_snapshot.py",bindings_path]:pins[task_relative(path)]=sha(path)
    manifest={"output":provider.workspace_relative(source),"output_sha256":sha(source),"imports":["Lean",*MODULES],
        "input_hashes":pins,"runtime_sha256":runtime_sha,"actual_import_oleans":dependencies,
        "requests":requests,"source_request_bindings":task_relative(bindings_path),
        "source_request_bindings_sha256":sha(bindings_path),"expected_jsonl":task_relative(output),
        "theorem_values_null":True,"ordinary_def_values_complete":True,"Std3_comparison_required":True,
        "original_kernel_certificate_pending":True,"generated_kernel_comparison_required":True,
        "validated":False,"submission_ready":False}
    mp=folder/"source-imports.json"
    write(mp,manifest)
    return {"source":task_relative(source),"source_sha256":sha(source),"imports_manifest":task_relative(mp),
        "imports_manifest_sha256":sha(mp),"actual_source_imports":["Lean",*MODULES],"request_count":len(requests),
        "validated":False,"generated_comparison_required":True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only",action="store_true",required=True)
    args=parser.parse_args()
    if list(DEST.rglob("*.preflight.json")) or list(DEST.rglob("*validation*.json")):
        raise ValueError("Preserve existing compiler/certificate evidence before any context-stage regeneration")
    frozen=[Path(provider.__file__),V/"providers-complete-preview/live-import-inventory.json",CATALOG,SOURCE_SUBSET,
            PLAN_DIR/"platform-artifact-plan-provider-variant.json"]
    for root in [V/"providers-complete-preview/all-shared-safe-leaves/Definitions",
                 V/"providers-complete-preview/all-shared-safe-leaves/snapshots"]:
        frozen.extend(root.rglob("*.lean"));frozen.extend(root.rglob("*.manifest.json"))
    before={str(p):sha(p) for p in frozen}
    g=readonly_generator()
    overlay_path,overlay=context_overlay(g)
    old_output=provider.OUTPUT
    reports=[]
    try:
        provider.OUTPUT=DEST
        for module in MODULES:
            risks=g.module_name_risk(module)
            if risks:raise ValueError("Context provider unsupported naming/context: "+json.dumps(risks))
            report=g.stage_bundle(module,"namespace-context")
            requests=g.snapshot_requests(module,False)
            generated=g.snapshot_requests(module,True)
            validate_requests(requests,module);validate_requests(generated,report["platform_module"])
            bindings=request_catalog_binding(g,requests,generated)
            stem=Path(report["output"]).stem
            bindings_path=DEST/"namespace-context/snapshots"/stem/"source-catalog-bindings.json"
            write(bindings_path,bindings)
            report["namespace_context_overlay"]=task_relative(overlay_path)
            report["namespace_context_overlay_sha256"]=sha(overlay_path)
            report["source_catalog_bindings"]=task_relative(bindings_path)
            report["source_catalog_bindings_sha256"]=sha(bindings_path)
            report["new_isolated_output_root"]=task_relative(DEST)
            report["provider_variant"]="all-shared-public+namespace-context-1"
            report["actual_source_outside174_pending"]=bindings["actual_source_certificate_outside174_pending"]
            report["whole_provider_import_closure_collision_check_pending"]=True
            write((ROOT/report["output"]).with_suffix(".manifest.json"),report)
            reports.append(report)
        group=source_fast_group(g,reports)
    finally:
        provider.OUTPUT=old_output
    if before!={str(p):sha(p) for p in frozen}:
        raise ValueError("Frozen producer/stages/catalog changed during isolated generation")
    write(DEST/"generation-report.json",{"overlay":overlay,"input_hashes":g.input_hashes,"generated":reports,
        "source_fast_snapshot":group,"frozen_source_hashes_unchanged":True,"lean_started":False,"api_used":False,
        "full_tree_ready":False,"submission_ready":False,"actual_generated_olean_dependencies_pending":True})
    print(json.dumps({"output_root":task_relative(DEST),"modules":MODULES,"source_fast_snapshot":group,
        "generated":len(reports),"validated":False,"submission_ready":False},indent=2))


if __name__=="__main__":main()
