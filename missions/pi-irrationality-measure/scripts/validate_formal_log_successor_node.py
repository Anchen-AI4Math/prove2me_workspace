"""Certify f2/f3 from retained exact evidence; never run Lean or a network API.

The source-faithful node producer, f1 checker and C1 proved-child checker remain
frozen. Local validation leaves the server-parent gate to publication.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import generate_platform_provider_nodes as nodegen
import generate_formal_log_truncation_provider as formal
import stage_formal_log_successor_nodes_short as producer
import validate_formal_log_node as base
import validate_formal_log_proved_child as childcheck
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone
import formal_log_node_refs as refs

TASK, ROOT, V = formal.TASK, formal.ROOT, formal.V
SELF = Path(__file__).resolve()
CERT_NAME = "successor-node-validation.json"
PRODUCER_SHA = "4bebf8db0c4e0329bc5b288f6650bcc6e475b08610dae25582ca7e33aac02a85"
CHILD_CHECKER_SHA = "828afd8a0b732b1e222a67a60e52f60d09d15ac14d784cfd5c9c6075fa462ac0"
sha, read, rel, fail, file = context.sha, context.read, context.rel, context.fail, context.file


def stage_path(value):
    p = Path(value)
    if not p.is_absolute(): p = TASK / p if p.parts[0] == "verification" else V / "flp3" / p
    p = p.resolve()
    fail(p not in [(V / "flp3" / k).resolve() for k in producer.NODES] or not p.is_dir(), "Only actual short f2/f3 stages supported")
    return p


def reconstruct(stage, m, n):
    captured = {}
    def capture_bytes(path, data):
        fail(path.resolve().parent != stage or path.name in captured, "Unexpected/duplicate readonly producer write")
        captured[path.name] = bytes(data); return len(data)
    def capture_text(path, text, encoding=None, errors=None, newline=None):
        return capture_bytes(path, text.encode(encoding or "utf-8", errors or "strict"))
    original_sha = nodegen.sha
    def captured_sha(path):
        if path.resolve().parent == stage and path.name in captured: return hashlib.sha256(captured[path.name]).hexdigest()
        return original_sha(path)
    destination = producer.ShortDestination(m["theorem_name"].replace(".", "_"), stage)
    with patch.object(nodegen, "DEST", destination), patch.object(Path, "write_bytes", capture_bytes), \
         patch.object(Path, "write_text", capture_text), patch.object(Path, "mkdir", lambda *a, **k: None), \
         patch.object(nodegen, "sha", captured_sha): result = n.generate(m["node"])
    fail((TASK / result["stage"]).resolve() != stage, "Exact node identity/destination differs")
    expected = json.loads(captured.pop("manifest.json"))
    fail(expected != m or set(captured) != set(m["outputs_sha256"]) or len(captured) != 4, "Exact source/AST manifest reconstruction differs")
    for name, raw in captured.items():
        fail((stage / name).read_bytes() != raw or sha(stage / name) != m["outputs_sha256"][name], "Source skeleton bytes differ: " + name)
    return n.import_collision_inventory(m["node"])


def setup(stage):
    fail(sha(Path(producer.__file__)) != PRODUCER_SHA or sha(Path(childcheck.__file__)) != CHILD_CHECKER_SHA, "Frozen successor/child producer changed")
    m = read(stage / "manifest.json")
    fail(m["node"] != producer.NODES[stage.name] or m["source_commit"] != "adc7f1241b42e322a6451854ab7e4b4c146bf78a", "Exact successor key/commit differs")
    fail(any(m.get(k) is not False for k in ["validated", "submission_ready", "full_tree_ready", "lean_started", "api_used"]), "Preview flags mutated")
    fail(m["node_generated_names"] or m["source_to_generated_private_kernel_names"] is not None or m["restored_local_instances"]
         or m["definition_certificates"], "Private aliases/local instances need a separate actual kernel-map consumer")
    fail(m["theorem_name"] != m["source_graph_name"] or m["top_level_literal_theorem_solution"] is not True, "Target must remain public original name with literal solution")
    fail(m["child_nodes"] != {producer.EXPECTED_CHILD: childcheck.emitter.THEOREM}, "Only exact C1 proved theorem child allowed")
    for p,h in m["input_hashes"].items(): fail(sha(file(p)) != h, "Frozen global input changed: " + p)
    for p,h in m["implementation_sha256"].items(): fail(sha(TASK / "scripts" / p) != h, "Frozen node producer changed: " + p)
    fail(sha(file(m["snapshot_core"])) != m["snapshot_core_sha256"] or sha(V / "decl_graph.jsonl") != m["source_graph_sha256"], "Core/Graph SHA changed")
    n = base.readonly_generator(m)
    inventory = reconstruct(stage, m, n)
    fail(inventory != m["whole_import_closure_inventory"] or inventory["collisions"], "Whole public import inventory/collision domain differs")
    target = n.g.units[m["node"]]
    fail(target["private"] or target["deprivate"] or target["graph_kinds"] != ["theorem"] or target["graph_names"] != [m["source_graph_name"]], "Target is not one unchanged public theorem")
    for r in m["public_inline_ci_requests"]:
        u = n.g.units[r["source_unit"]]
        fail(u["private"] or u["deprivate"] or u["graph_kinds"] != ["theorem"] or r["generated_name"] != r["source_graph_name"]
             or r["source_graph_name"] not in u["graph_names"], "Only retained unchanged public inline theorem CIs supported")
    return m,n,inventory


def child_interface():
    result = childcheck.validate_proved_child(V / "flp3/c1")
    d,c = result["certificate"]["data"], result["certificate"]
    fail(d["validated"] is not True or d["parent_node"] != producer.EXPECTED_CHILD or d["Std3_only"] is not True
         or d["actual_imported_owner"] is not True or d["exact_certified_solution_rebinding"] is not True,
         "C1 actual imported owner/type/proof certificate missing")
    return {"node": producer.EXPECTED_CHILD, "theorem_name": d["theorem_name"], "module": d["module"],
        "certificate": c["path"], "certificate_sha256": c["sha256"], "output_olean": d["output_olean"],
        "output_olean_sha256": d["output_olean_sha256"], "validated": True, "proof_axioms": "Std3"}


def preparations(stage,m,definitions,child):
    ci = stage / "certified-inputs.json"
    expected_ci = {"schema_version": 1, "artifact_kind": "formal-log-successor-node-certified-inputs", "node": m["node"],
        "definition_certificates": definitions, "child_certificates": [child], "server_parent_pending": True,
        "validated_node": False, "Lean_started": False, "submission_ready": False}
    fail(read(ci) != expected_ci, "Certified direct Definitions/proved child input domain differs")
    p = read(stage / "preparation.json")
    base_snapshot, generated, output = stage / "SnapshotGenerated.lean", stage / "SnapshotGeneratedWithRefs.lean", stage / "proof-references.json"
    addon = producer.repaired_refs_addon(m["public_inline_ci_requests"], output)
    fail(generated.read_bytes() != base_snapshot.read_bytes() + addon, "WithRefs is not the exact old prefix plus narrow corrected exporter")
    # Independently constrain the two identifier edits on the frozen original
    # addon, instead of granting an arbitrary source-transform function.
    original_addon = producer.base.proof_reference_addon(m["public_inline_ci_requests"], output).encode()
    exact_addon = original_addon
    for old,new in [(b"def export (", b"def exportProofRefs ("),
                    (b"FormalLogProofReferenceSnapshot.export ", b"FormalLogProofReferenceSnapshot.exportProofRefs ")]:
        fail(exact_addon.count(old) != 1 or exact_addon.count(new), "Exact identifier anchors differ")
        exact_addon = exact_addon.replace(old,new,1)
    fail(exact_addon != addon or len(addon)-len(original_addon) != 18, "Corrected exporter differs outside the two identifiers")
    checked = {"node": m["node"], "theorem_name": m["theorem_name"], "stage": rel(stage), "attempt_root": rel(stage.parent), "short_stage": rel(stage),
        "base_snapshot": rel(base_snapshot), "base_snapshot_sha256": sha(base_snapshot), "generated_with_refs": rel(generated), "generated_with_refs_sha256": sha(generated),
        "generated_with_refs_prefix_bytes": base_snapshot.stat().st_size, "proof_reference_addon_sha256": hashlib.sha256(addon).hexdigest(),
        "proof_reference_output": rel(output), "proof_reference_requests": ["solution", *[r["generated_name"] for r in m["public_inline_ci_requests"]]],
        "certified_definition_dependencies": len(definitions), "certified_child_dependencies": [child], "exact_old_snapshot_prefix": True,
        "server_parent_pending": True, "pure_python_prepared": True, "Lean_started": False, "validated": False, "submission_ready": False}
    for k,v in checked.items(): fail(p.get(k) != v, "Exact successor preparation binding differs: " + k)
    pins = {rel(Path(producer.__file__)): sha(Path(producer.__file__)), rel(Path(producer.base.__file__)): sha(Path(producer.base.__file__)),
        rel(Path(producer.plan.__file__)): sha(Path(producer.plan.__file__)), rel(Path(childcheck.__file__)): sha(Path(childcheck.__file__)),
        rel(stage / "manifest.json"): sha(stage / "manifest.json"), rel(ci): sha(ci),
        child["certificate"]: child["certificate_sha256"], child["output_olean"]: child["output_olean_sha256"]}
    for d in definitions:
        pins[d["certificate"]] = d["certificate_sha256"]; pins[d["output_olean"]] = d["output_lean_sha256"]
    filenames = [Path(m["statement"]).name, Path(m["solution"]).name, "SnapshotOriginal.lean", generated.name]
    fail(set(p["compile_manifests"]) != set(filenames), "Expected exactly the four actual compiler files")
    manifests = {}
    for i,name in enumerate(filenames,1):
        source,mp = stage / name, stage / (f"c{i}.json")
        imports = ["Lean",m["source_components"][0]["source_module"]] if name == "SnapshotOriginal.lean" else m["imports"]
        expected = {"schema_version": 1, "artifact_kind": "formal-log-successor-node-file-import-certificate", "output": source.relative_to(ROOT).as_posix(),
            "output_sha256": sha(source), "imports": imports, "input_hashes": pins, "runtime_sha256": m["runtime_sha256"], "node": m["node"],
            "node_validated": False, "server_parent_pending": True, "timeout_seconds": 300, "Lean_started": False, "submission_ready": False}
        fail(read(mp) != expected or p["compile_manifests"][name] != {"manifest": rel(mp), "manifest_sha256": sha(mp)}, "Exact successor actual compile manifest differs")
        manifests[name] = mp
    return generated,output,manifests


def certify(stage):
    m,n,inventory = setup(stage)
    child = child_interface()
    definitions,provided = base.definition_interfaces(m)
    generated_source,output,manifests = preparations(stage,m,definitions,child)
    records = {name:context.record(stage/name,mp,"modecheck",(stage/name).stem,stage) for name,mp in manifests.items()}
    for name,pf in records.items():
        if name == "SnapshotOriginal.lean": continue
        for interface in definitions:
            dep = next(d for d in pf["data"]["dependency_oleans"] if d["module"] == interface["platform_module"])
            fail(dep["sha256_before"] != interface["output_lean_sha256"], "Actual Definition OLean differs from certified current interface")
        dep = next(d for d in pf["data"]["dependency_oleans"] if d["module"] == child["module"])
        fail(dep["sha256_before"] != child["output_olean_sha256"], "Actual child theorem OLean differs from proved C1 artifact")
    original_pf,generated_pf = records["SnapshotOriginal.lean"],records[generated_source.name]
    original = base.kernel_rows(stage/"original-type.json",[m["source_graph_name"]],original_pf)
    generated = base.kernel_rows(stage/"generated-type.json",[m["theorem_name"],"solution"],generated_pf)
    for row in generated: base.same_type(original[0],row)
    old_names,new_names = [r["source_graph_name"] for r in m["public_inline_ci_requests"]],[r["generated_name"] for r in m["public_inline_ci_requests"]]
    old_inline = base.kernel_rows(ROOT/m["public_inline_type_json_outputs"]["original"],old_names,original_pf)
    new_inline = base.kernel_rows(ROOT/m["public_inline_type_json_outputs"]["generated"],new_names,generated_pf)
    for a,b in zip(old_inline,new_inline,strict=True):base.same_type(a,b)
    for side,pf in [("original",original_pf),("generated",generated_pf)]:base.kernel_rows(ROOT/m["inline_type_json_outputs"][side],[],pf)
    audits = {"source":standalone.audit_axioms(file(original_pf["data"]["log"]),m["source_graph_name"]),
        "snapshot_solution":standalone.audit_axioms(file(generated_pf["data"]["log"]),"solution"),
        "exact_solution":standalone.audit_axioms(file(records[Path(m["solution"]).name]["data"]["log"]),"solution")}
    proof_rows = refs.checked_output(stage,m,generated_pf,output)
    fail(set(proof_rows[0]["axioms"]) != set(audits["snapshot_solution"]), "Same-run proof axioms differ")
    fail(child["theorem_name"] in provided or child["theorem_name"] in new_names, "Duplicate actual proved child/public Definition/inline constant")
    fail(bool(set(provided) & set(new_names)), "Retained public inline CI duplicates an actual imported Definition constant")
    allowed = set(provided)|set(new_names)|{child["theorem_name"]}; graph_names = set(n.g.graph); reference_audits=[]
    for row in proof_rows:
        names = set(row["typeRefs"]+row["valueRefs"])
        fail(m["theorem_name"] in names or "solution" in names or row["name"] in names,
             "Proof refers to its target stub, solution, or own inline binding")
        project = {p for p in names if p in graph_names or p.startswith(("OAI.","Definitions.","Theorems.","Solutions.","_private.OAI."))}
        fail(not project <= allowed, "Proof uses unavailable project declarations: "+str(sorted(project-allowed)))
        reference_audits.append({"name":row["name"],"actual_project_refs":sorted(project),"available_project_refs_only":True,
            "closed_type_and_proof":True,"axioms":row["axioms"],"actual_owner":row["owner"]})
    implementation = dict(base.implementation_pins())
    for p in [SELF,Path(producer.__file__),Path(childcheck.__file__),Path(refs.__file__)]:implementation[rel(p)]=sha(p)
    outputs = [stage/"original-type.json",stage/"generated-type.json",output,
        *[ROOT/m[field][side] for field in ["public_inline_type_json_outputs","inline_type_json_outputs"] for side in ["original","generated"]]]
    return {"schema_version":1,"artifact_kind":"formal-log-successor-proof-node-kernel-certificate","validated":True,
        "node":m["node"],"theorem_name":m["theorem_name"],"source_commit":m["source_commit"],"manifest":rel(stage/"manifest.json"),"manifest_sha256":sha(stage/"manifest.json"),
        "statement_sha256":m["statement_sha256"],"solution_sha256":m["solution_sha256"],"original_four_files_sha256":m["outputs_sha256"],
        "generated_with_refs":rel(generated_source),"generated_with_refs_sha256":sha(generated_source),
        "generated_with_refs_manifest_sha256":sha(manifests[generated_source.name]),"definition_certificates":definitions,
        "actual_definition_provided_names":provided,"child_certificates":[child],"source_components":m["source_components"],"source_graph_sha256":m["source_graph_sha256"],
        "source_command_witness":base.source_command_witness(m,n),"source_skeleton_and_inventory_reconstructed":True,"public_import_duplicate_constants":[],
        "kernel_types_equal":True,"inline_kernel_types_equal":True,"source_target_solution_universes_equal":True,"only_universe_parameter_names_normalized":True,
        "theorem_values_null":True,"theorem_proof_values_exported":False,"solution_proof_reference_evidence":reference_audits,
        "target_stub_unused":True,"actual_project_reference_coverage_complete":True,"allowed_project_names":sorted(allowed),"proof_reference_getter":"Lean.Expr.getUsedConstants",
        "Std3_only":True,"proof_axioms":"Std3","axioms":audits,"preflights":records,"max_file_seconds":max(pf["data"]["seconds"] for pf in records.values()),
        "output_json_sha256":{p.name:sha(p) for p in outputs},"input_hashes":m["input_hashes"],"implementation_hashes":implementation,
        "server_parent_pending":True,"submission_ready":False,"full_tree_ready":False,"source_scope_partial":True}


def validate_formal_successor_node(stage):
    """Read-only publisher entry point; current source/CI/child replay required."""
    stage=stage_path(stage);c=certify(stage);p=stage/CERT_NAME
    fail(not p.is_file() or read(p)!=c,"Successor certificate missing/stale after full readonly replay")
    m=read(stage/"manifest.json")
    return {"stage":stage,"manifest":stage/"manifest.json","manifest_data":m,"certificate":{"path":rel(p),"sha256":sha(p),"data":c},
        "statement_bytes":(ROOT/m["statement"]).read_bytes(),"solution_bytes":(ROOT/m["solution"]).read_bytes(),"source_command_witness":c["source_command_witness"],
        "validated":True,"server_parent_pending":True,"submission_ready":False}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("stage");g=p.add_mutually_exclusive_group(required=True)
    g.add_argument("--check-only",action="store_true");g.add_argument("--certify-existing",action="store_true");g.add_argument("--validate-only",action="store_true");a=p.parse_args()
    try:
        stage=stage_path(a.stage)
        if a.check_only:
            m,*_=setup(stage);out={"node":m["node"],"source_and_exact_bytes_checked":True,"validated":False,"submission_ready":False}
        elif a.certify_existing:
            c=certify(stage);path=stage/CERT_NAME;context.write_exact(path,c);out={"validated":True,"certificate":rel(path),"sha256":sha(path),"max_file_seconds":c["max_file_seconds"],"submission_ready":False}
        else:
            result=validate_formal_successor_node(stage);out={"validated":True,"certificate":result["certificate"]["path"],"sha256":result["certificate"]["sha256"],"submission_ready":False}
        print(json.dumps(out,indent=2))
    except (ValueError,KeyError,FileNotFoundError,TypeError,StopIteration) as e:
        print(json.dumps({"validated":False,"status":"rejected","error":str(e)}));raise SystemExit(2)


if __name__=="__main__":main()
