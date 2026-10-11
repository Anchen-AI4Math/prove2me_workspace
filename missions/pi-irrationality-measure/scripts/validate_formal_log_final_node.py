"""Certify f4 from retained exact evidence; never run Lean or a network API.

The repaired source producer, exact genuine rfl AST adapter and c2/c3 child
checker remain frozen. Server-parent gates belong only to publication.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from unittest.mock import patch

import generate_platform_provider_nodes as nodegen
import generate_formal_log_truncation_provider as formal
import stage_formal_log_final_node_short_repaired as producer
import stage_formal_log_successor_nodes_short as source_stage
import formal_log_rfl_helper_adapter as rfl
import validate_formal_log_node as base
import validate_formal_log_successor_children_repaired as childcheck
import validate_formal_log_f3_extra_ci as e3check
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone
import formal_log_node_refs as refs

TASK, ROOT, V = formal.TASK, formal.ROOT, formal.V
SELF = Path(__file__).resolve()
CERT_NAME = "final-node-validation.json"
PRODUCER_SHA = "2661e0a8c4fb5d913ddf00c8e59e1faf7a77ee4fb4c06b9f0dce88af6b71d9c1"
RFL_SHA = "681b5a6c7688501d0491907837e94bfcd2ad105dc07003cf396b6a808e06bed8"
BASELINE_SHA = "20f761f0d169c7af296faea379bb7547909abd56f79d0bdba03a207d7617bfb4"
import validate_formal_log_successor_node as frozenbaseline
CHILD_CHECKER_SHA = "92b265ebf16b00afb98fd4c70012b6dc46bc07ce6cab86d5249ba23dfa389eff"
sha, read, rel, fail, file = context.sha, context.read, context.rel, context.fail, context.file



def stage_path(value=producer.STAGE):
    p=Path(value)
    if not p.is_absolute(): p=TASK/p if p.parts and p.parts[0]=='verification' else V/'flp3'/p
    p=p.resolve()
    fail(p!=producer.STAGE.resolve() or not p.is_dir(),'Only actual short f4 supported')
    return p


def reconstruct(stage,m,n):
    captured={}
    def capture_bytes(path,data):
        fail(path.resolve().parent!=stage or path.name in captured,'Unexpected readonly f4 producer write')
        captured[path.name]=bytes(data);return len(data)
    def capture_text(path,text,encoding=None,errors=None,newline=None):
        return capture_bytes(path,text.encode(encoding or 'utf-8',errors or 'strict'))
    old_sha=nodegen.sha
    def captured_sha(path):
        if path.resolve().parent==stage and path.name in captured:return hashlib.sha256(captured[path.name]).hexdigest()
        return old_sha(path)
    dest=source_stage.ShortDestination(m['theorem_name'].replace('.','_'),stage)
    with patch.object(nodegen,'DEST',dest),patch.object(Path,'write_bytes',capture_bytes), \
         patch.object(Path,'write_text',capture_text),patch.object(Path,'mkdir',lambda *a,**k:None), \
         patch.object(nodegen,'sha',captured_sha):generated=n.generate(m['node'])
    fail((TASK/generated['stage']).resolve()!=stage,'Exact final-node destination differs')
    fail(json.loads(captured.pop('manifest.json'))!=m or set(captured)!=set(m['outputs_sha256']) or len(captured)!=4,
         'Exact f4 source/AST manifest reconstruction differs')
    for name,raw in captured.items():
        fail((stage/name).read_bytes()!=raw or sha(stage/name)!=m['outputs_sha256'][name],'Exact f4 skeleton differs: '+name)
    return n.import_collision_inventory(m['node']),generated


def setup(stage):
    fail(sha(Path(producer.__file__))!=PRODUCER_SHA or sha(Path(rfl.__file__))!=RFL_SHA
         or sha(Path(childcheck.__file__))!=CHILD_CHECKER_SHA or sha(Path(frozenbaseline.__file__))!=BASELINE_SHA,
         'Frozen final-node producer/adapter/shared consumer changed')
    fail(sha(Path(producer.retained.__file__))!=producer.RETAINED_SHA,'Retained failed producer changed')
    m=read(stage/'manifest.json')
    fail(m['node']!=producer.NODE or m['source_commit']!='adc7f1241b42e322a6451854ab7e4b4c146bf78a','Wrong final-node key/commit')
    fail(any(m.get(k) is not False for k in ['validated','submission_ready','full_tree_ready','lean_started','api_used']),'Preview flags mutated')
    fail(m['node_generated_names'] or m['source_to_generated_private_kernel_names'] is not None
         or m['restored_local_instances'] or m['definition_certificates'],'Private aliases/instances not supported')
    fail(m['theorem_name']!=m['source_graph_name'] or m['top_level_literal_theorem_solution'] is not True,
         'Target must retain original source name and literal top-level solution')
    expected_children={producer.child_stage.NODES[c]:producer.child_stage.THEOREMS[c] for c in ['c2','c3']}
    fail(m['child_nodes']!=expected_children,'Only the two exact proved successor children are supported')
    for p,h in m['input_hashes'].items():fail(sha(file(p))!=h,'Frozen global input changed: '+p)
    for p,h in m['implementation_sha256'].items():fail(sha(TASK/'scripts'/p)!=h,'Frozen node generator changed: '+p)
    fail(sha(file(m['snapshot_core']))!=m['snapshot_core_sha256'] or sha(V/'decl_graph.jsonl')!=m['source_graph_sha256'],'Core/Graph SHA changed')
    # Match the repaired producer: f2-seeded builder, full equation API replay,
    # then one genuine AST/Graph public helper classification normalization.
    n=base.readonly_generator(read(V/'flp3/f2/manifest.json'))
    fail(n.g.input_hashes!=m['input_hashes'],'Exact final-node current global input domain differs')
    equation=producer.formalci.validate_equation_certificate()
    rfl.install(n,equation);n.node_layout(m['node']);n.import_collision_inventory(m['node'])
    inventory,generated=reconstruct(stage,m,n)
    fail(inventory!=m['whole_import_closure_inventory'] or inventory['collisions'],'Whole import inventory differs/collides')
    target=n.g.units[m['node']]
    fail(target['private'] or target['deprivate'] or target['graph_kinds']!=['theorem'] or target['graph_names']!=[m['source_graph_name']],
         'Target is not one unchanged public theorem')
    requests=m['public_inline_ci_requests'];ledger=n.certified_rfl_helper_normalization
    fail(len(requests)!=5 or set(ledger)!={rfl.UNIT} or len({r['generated_name'] for r in requests})!=5,
         'Expected exact five public inline theorem CIs and one actual rfl helper')
    for row in requests:
        if row['source_unit']==rfl.UNIT:
            fail(row['source_graph_name']!=rfl.HELPER or row['generated_name']!=rfl.HELPER or row['source_module']!=rfl.MODULE
                 or row['source_command_range']!=ledger[rfl.UNIT]['source_command_range'],
                 'Actual rfl request differs from strict AST/Graph normalization ledger')
        else:
            u=n.g.units[row['source_unit']]
            fail(u['private'] or u['deprivate'] or u['graph_kinds']!=['theorem'] or row['generated_name']!=row['source_graph_name']
                 or row['source_graph_name'] not in u['graph_names'],'Only retained unchanged public inline theorem CIs supported')
    fail(sum(r['source_unit']==rfl.UNIT for r in requests)!=1,'Actual rfl inline helper missing/duplicated')
    return m,n,inventory,equation,generated


def preparations(stage,m,definitions,children,equation,generated,n):
    ci=stage/'certified-inputs.json';eq={'path':equation['path'],'sha256':equation['sha256']}
    expected_ci={'schema_version':1,'artifact_kind':'formal-log-final-node-certified-inputs','node':m['node'],
        'definition_certificates':definitions,'child_certificates':children,'equation_certificate':eq,
        'server_parent_pending':True,'validated_node':False,'Lean_started':False,'submission_ready':False}
    fail(read(ci)!=expected_ci,'Exact certified Definitions/two children/equation inputs differ')
    snapshot,with_refs,output=stage/'SnapshotGenerated.lean',stage/'SnapshotGeneratedWithRefs.lean',stage/'proof-references.json'
    addon=source_stage.repaired_refs_addon(m['public_inline_ci_requests'],output)
    fail(with_refs.read_bytes()!=snapshot.read_bytes()+addon,'WithRefs differs from exact frozen snapshot prefix/addon')
    pins={rel(p):sha(p) for p in [Path(producer.__file__),Path(producer.retained.__file__),Path(rfl.__file__),Path(source_stage.__file__),
        Path(childcheck.__file__),Path(base.__file__),Path(producer.formalci.__file__),Path(producer.plan.__file__),stage/'manifest.json',ci]}
    pins[equation['path']]=equation['sha256']
    for d in definitions:pins[d['certificate']]=d['certificate_sha256'];pins[d['output_olean']]=d['output_lean_sha256']
    for child in children:pins[child['certificate']]=child['certificate_sha256'];pins[child['output_olean']]=child['output_olean_sha256']
    names=[Path(m['statement']).name,Path(m['solution']).name,'SnapshotOriginal.lean',with_refs.name];manifests={};bindings={}
    for i,name in enumerate(names,1):
        path=stage/f'c{i}.json';source=stage/name
        imports=['Lean',m['source_components'][0]['source_module']] if name=='SnapshotOriginal.lean' else m['imports']
        expected={'schema_version':1,'artifact_kind':'formal-log-final-node-file-import-certificate',
            'output':source.relative_to(ROOT).as_posix(),'output_sha256':sha(source),'imports':imports,'input_hashes':pins,
            'runtime_sha256':m['runtime_sha256'],'node':m['node'],'node_validated':False,'timeout_seconds':300,
            'server_parent_pending':True,'Lean_started':False,'submission_ready':False}
        fail(read(path)!=expected,'Exact final-node compiler manifest differs: '+name)
        manifests[name]=path;bindings[name]={'manifest':rel(path),'manifest_sha256':sha(path)}
    prep={**generated,'attempt_root':rel(stage.parent),'short_stage':rel(stage),'base_snapshot':rel(snapshot),'base_snapshot_sha256':sha(snapshot),
        'generated_with_refs':rel(with_refs),'generated_with_refs_sha256':sha(with_refs),'generated_with_refs_prefix_bytes':snapshot.stat().st_size,
        'proof_reference_addon_sha256':hashlib.sha256(addon).hexdigest(),'proof_reference_output':rel(output),
        'proof_reference_requests':['solution',*[r['generated_name'] for r in m['public_inline_ci_requests']]],
        'source_helper_shape_normalization':n.certified_rfl_helper_normalization,
        'retained_failed_producer':{'path':rel(Path(producer.retained.__file__)),'sha256':producer.RETAINED_SHA,
            'failure_before_files':'raw genuine public AST rfl unit missing workflow private field'},
        'certified_definition_dependencies':len(definitions),'certified_child_dependencies':children,'equation_certificate':eq,
        'compile_manifests':bindings,'exact_old_snapshot_prefix':True,'server_parent_pending':True,'pure_python_prepared':True,
        'Lean_started':False,'validated':False,'submission_ready':False}
    prep['maximum_absolute_path_length']=max(source_stage.path_budget(stage,prep).values())
    fail(read(stage/'preparation.json')!=prep,'Exact final-node preparation differs')
    return with_refs,output,manifests


def auxiliary_interfaces(definitions,proof_rows,equation):
    names={name for row in proof_rows for name in row['typeRefs']+row['valueRefs']};allowed=[];certificates=[]
    if rfl.EQUATION in names:
        fail(equation['sha256']!=rfl.CERT_SHA,'Required shiftMap actual paired equation certificate differs')
        allowed.append(rfl.EQUATION)
        certificates.append({'path':equation['path'],'sha256':equation['sha256'],'provided_names':[rfl.EQUATION],'evidence_role':'formal-equation'})
    e3names=e3check.gen.REQUIRED+[e3check.gen.AUX]
    if set(e3names)&names:
        c=e3check.validate_extra_ci(definitions);fail(c['data']['provided_names']!=e3names,'Only exact three paired extra CIs supported')
        allowed.extend(e3names);certificates.append({'path':c['path'],'sha256':c['sha256'],'provided_names':e3names,'evidence_role':'extra-ci'})
    # shiftEquiv._proof_* remains unavailable until an independently complete
    # actual paired CI consumer is installed and hash-pinned here.
    return sorted(set(allowed)),certificates


def certify(stage):
    m,n,inventory,equation,generated = setup(stage)
    children = producer.child_interfaces()
    definitions,provided = base.definition_interfaces(m)
    generated_source,output,manifests = preparations(stage,m,definitions,children,equation,generated,n)
    records = {name:context.record(stage/name,mp,"modecheck",(stage/name).stem,stage) for name,mp in manifests.items()}
    for name,pf in records.items():
        if name == "SnapshotOriginal.lean": continue
        for interface in definitions:
            dep = next(d for d in pf["data"]["dependency_oleans"] if d["module"] == interface["platform_module"])
            fail(dep["sha256_before"] != interface["output_lean_sha256"], "Actual Definition OLean differs from certified current interface")
        for child in children:
            dep = next(d for d in pf["data"]["dependency_oleans"] if d["module"] == child["module"])
            fail(dep["sha256_before"] != child["output_olean_sha256"], "Actual child theorem OLean differs from proved c2/c3 artifact")
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
    for child in children:
        fail(child["theorem_name"] in provided or child["theorem_name"] in new_names, "Duplicate actual proved child/public Definition/inline constant")
    fail(bool(set(provided) & set(new_names)), "Retained public inline CI duplicates an actual imported Definition constant")
    auxiliary, auxiliary_certificates = auxiliary_interfaces(definitions, proof_rows, equation)
    allowed = set(provided)|set(new_names)|{c["theorem_name"] for c in children}|set(auxiliary); graph_names = set(n.g.graph); reference_audits=[]
    for row in proof_rows:
        names = set(row["typeRefs"]+row["valueRefs"])
        fail(m["theorem_name"] in names or "solution" in names or row["name"] in names,
             "Proof refers to its target stub, solution, or own inline binding")
        project = {p for p in names if p in graph_names or p.startswith(("OAI.","Definitions.","Theorems.","Solutions.","_private.OAI."))}
        fail(not project <= allowed, "Proof uses unavailable project declarations: "+str(sorted(project-allowed)))
        reference_audits.append({"name":row["name"],"actual_project_refs":sorted(project),"available_project_refs_only":True,
            "closed_type_and_proof":True,"axioms":row["axioms"],"actual_owner":row["owner"]})
    implementation = dict(base.implementation_pins())
    for p in [SELF,Path(producer.__file__),Path(childcheck.__file__),Path(refs.__file__),Path(rfl.__file__),Path(source_stage.__file__),Path(frozenbaseline.__file__)]:implementation[rel(p)]=sha(p)
    outputs = [stage/"original-type.json",stage/"generated-type.json",output,
        *[ROOT/m[field][side] for field in ["public_inline_type_json_outputs","inline_type_json_outputs"] for side in ["original","generated"]]]
    return {"schema_version":1,"artifact_kind":"formal-log-final-proof-node-kernel-certificate","validated":True,
        "node":m["node"],"theorem_name":m["theorem_name"],"source_commit":m["source_commit"],"manifest":rel(stage/"manifest.json"),"manifest_sha256":sha(stage/"manifest.json"),
        "statement_sha256":m["statement_sha256"],"solution_sha256":m["solution_sha256"],"original_four_files_sha256":m["outputs_sha256"],
        "generated_with_refs":rel(generated_source),"generated_with_refs_sha256":sha(generated_source),
        "generated_with_refs_manifest_sha256":sha(manifests[generated_source.name]),"definition_certificates":definitions,
        "actual_definition_provided_names":provided,"child_certificates":children,"equation_certificate":{"path":equation["path"],"sha256":equation["sha256"]},
        "auxiliary_ci_certificates":auxiliary_certificates,"actual_auxiliary_provided_names":auxiliary,
        "source_helper_shape_normalization":n.certified_rfl_helper_normalization,"source_components":m["source_components"],"source_graph_sha256":m["source_graph_sha256"],
        "source_command_witness":base.source_command_witness(m,n),"source_skeleton_and_inventory_reconstructed":True,"public_import_duplicate_constants":[],
        "kernel_types_equal":True,"inline_kernel_types_equal":True,"source_target_solution_universes_equal":True,"only_universe_parameter_names_normalized":True,
        "theorem_values_null":True,"theorem_proof_values_exported":False,"solution_proof_reference_evidence":reference_audits,
        "target_stub_unused":True,"actual_project_reference_coverage_complete":True,"allowed_project_names":sorted(allowed),"proof_reference_getter":"Lean.Expr.getUsedConstants",
        "Std3_only":True,"proof_axioms":"Std3","axioms":audits,"preflights":records,"max_file_seconds":max(pf["data"]["seconds"] for pf in records.values()),
        "output_json_sha256":{p.name:sha(p) for p in outputs},"input_hashes":m["input_hashes"],"implementation_hashes":implementation,
        "server_parent_pending":True,"submission_ready":False,"full_tree_ready":False,"source_scope_partial":True}


def validate_formal_final_node(stage=producer.STAGE):
    """Read-only publisher entry point; current source/CI/child replay required."""
    stage=stage_path(stage);c=certify(stage);p=stage/CERT_NAME
    fail(not p.is_file() or read(p)!=c,"Successor certificate missing/stale after full readonly replay")
    m=read(stage/"manifest.json")
    return {"stage":stage,"manifest":stage/"manifest.json","manifest_data":m,"certificate":{"path":rel(p),"sha256":sha(p),"data":c},
        "statement_bytes":(ROOT/m["statement"]).read_bytes(),"solution_bytes":(ROOT/m["solution"]).read_bytes(),"source_command_witness":c["source_command_witness"],
        "validated":True,"server_parent_pending":True,"submission_ready":False}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--stage',default='verification/flp3/f4')
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--check-only',action='store_true')
    g.add_argument('--certify-existing',action='store_true');g.add_argument('--validate-only',action='store_true');a=p.parse_args()
    try:
        stage=stage_path(a.stage)
        if a.check_only:
            m,*_=setup(stage);out={'source_and_exact_skeleton_checked':True,'node':m['node'],'validated':False,'submission_ready':False}
        elif a.certify_existing:
            c=certify(stage);path=stage/CERT_NAME;context.write_exact(path,c)
            out={'validated':True,'certificate':rel(path),'sha256':sha(path),'max_file_seconds':c['max_file_seconds'],'submission_ready':False}
        else:
            v=validate_formal_final_node(stage);out={'validated':True,'certificate':v['certificate']['path'],
                'sha256':v['certificate']['sha256'],'submission_ready':False}
        print(json.dumps(out,indent=2))
    except (ValueError,KeyError,OSError,TypeError,StopIteration) as e:
        print(json.dumps({'validated':False,'status':'rejected','error':str(e)}));raise SystemExit(2)


if __name__=='__main__':main()


