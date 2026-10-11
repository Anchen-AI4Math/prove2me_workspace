"""Stage only f4 using two actually proved successor child OLeans.

All compilation remains with the root agent. Parent server acceptance is a
publication gate; local source preparation requires actual child certificates.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from unittest.mock import patch
import stage_formal_log_successor_nodes_short as source_stage
import stage_formal_log_successor_children_repaired as child_stage
import validate_formal_log_successor_children_repaired as childcheck
import validate_formal_log_node as readonly
import validate_formal_log_truncation_provider as formalci
import validate_namespace_context_providers as context
import plan_formal_log_proof_nodes as plan
import generate_platform_provider_nodes as nodegen

TASK,ROOT,V=readonly.TASK,readonly.ROOT,readonly.V
SELF=Path(__file__).resolve()
STAGE=V/'flp3/f4'
NODE=plan.NODE_KEYS['formalLog_packets_surjective_iff_truncated']
CHILD_CHECKER_SHA='92b265ebf16b00afb98fd4c70012b6dc46bc07ce6cab86d5249ba23dfa389eff'
SOURCE_STAGE_SHA='4bebf8db0c4e0329bc5b288f6650bcc6e475b08610dae25582ca7e33aac02a85'
sha,read,rel,fail=context.sha,context.read,context.rel,context.fail

def child_interfaces():
    fail(sha(Path(childcheck.__file__))!=CHILD_CHECKER_SHA or sha(Path(source_stage.__file__))!=SOURCE_STAGE_SHA,
         'Frozen final-node source/child consumer changed')
    interfaces=[]
    for which in ['c2','c3']:
        result=childcheck.validate_successor_child(which)['certificate'];d=result['data']
        fail(d['parent_node']!=child_stage.NODES[which] or d['theorem_name']!=child_stage.THEOREMS[which]
             or any(d[k] is not True for k in ['validated','Std3_only','actual_imported_owner','exact_certified_solution_rebinding']),
             'Final node requires exact actual proved c2/c3 child interface')
        interfaces.append({'node':d['parent_node'],'theorem_name':d['theorem_name'],'module':d['module'],
            'certificate':result['path'],'certificate_sha256':result['sha256'],'output_olean':d['output_olean'],
            'output_olean_sha256':d['output_olean_sha256'],'validated':True,'proof_axioms':'Std3'})
    return interfaces

def prepare():
    children=child_interfaces()
    # The readonly builder restores the exact f4 source equation witness from
    # the already certified getEqnsFor?/isEqnThm? relationship. It never runs
    # the ordinary constructor that writes live shared inventories.
    seed=read(V/'flp3/f2/manifest.json')
    n=readonly.readonly_generator(seed)
    equation=formalci.validate_equation_certificate()
    name=equation['data']['required_source_equation']
    preserved=n.g.unit_plan['preserved_generated_commands']
    if name not in preserved:
        n.g.unit_plan=dict(n.g.unit_plan)
        n.g.unit_plan['preserved_generated_commands']=[*preserved,name]
    theorem=n.node_name(NODE)
    with patch.object(nodegen,'DEST',source_stage.ShortDestination(theorem.replace('.','_'),STAGE)):
        generated=n.generate(NODE)
    fail((TASK/generated['stage']).resolve()!=STAGE.resolve(),'Exact f4 short destination differs')
    m=read(STAGE/'manifest.json')
    fail(m['child_nodes']!={c['node']:c['theorem_name'] for c in children},'Final node child statement domain differs')
    definitions=[plan.certified_definition(r['source_module'],r['platform_module']) for r in m['definition_dependency_witnesses']]
    snapshot=STAGE/'SnapshotGenerated.lean';with_refs=STAGE/'SnapshotGeneratedWithRefs.lean';output=STAGE/'proof-references.json'
    addon=source_stage.repaired_refs_addon(m['public_inline_ci_requests'],output)
    source_stage.base.write_exact(with_refs,snapshot.read_bytes()+addon)
    ci=STAGE/'certified-inputs.json'
    context.write_exact(ci,{'schema_version':1,'artifact_kind':'formal-log-final-node-certified-inputs','node':NODE,
        'definition_certificates':definitions,'child_certificates':children,
        'equation_certificate':{'path':equation['path'],'sha256':equation['sha256']},
        'server_parent_pending':True,'validated_node':False,'Lean_started':False,'submission_ready':False})
    pins={rel(p):sha(p) for p in [SELF,Path(source_stage.__file__),Path(childcheck.__file__),Path(readonly.__file__),
        Path(formalci.__file__),Path(plan.__file__),STAGE/'manifest.json',ci]}
    pins[equation['path']]=equation['sha256']
    for d in definitions:
        pins[d['certificate']]=d['certificate_sha256'];pins[d['output_olean']]=d['output_lean_sha256']
    for c in children:
        pins[c['certificate']]=c['certificate_sha256'];pins[c['output_olean']]=c['output_olean_sha256']
    files=[STAGE/Path(m['statement']).name,STAGE/Path(m['solution']).name,STAGE/'SnapshotOriginal.lean',with_refs]
    manifests={}
    for i,source in enumerate(files,1):
        imports=['Lean',m['source_components'][0]['source_module']] if source.name=='SnapshotOriginal.lean' else m['imports']
        path=STAGE/f'c{i}.json'
        context.write_exact(path,{'schema_version':1,'artifact_kind':'formal-log-final-node-file-import-certificate',
            'output':source.relative_to(ROOT).as_posix(),'output_sha256':sha(source),'imports':imports,'input_hashes':pins,
            'runtime_sha256':m['runtime_sha256'],'node':NODE,'node_validated':False,'timeout_seconds':300,
            'server_parent_pending':True,'Lean_started':False,'submission_ready':False})
        manifests[source.name]={'manifest':rel(path),'manifest_sha256':sha(path)}
    prep={**generated,'attempt_root':rel(STAGE.parent),'short_stage':rel(STAGE),'base_snapshot':rel(snapshot),
        'base_snapshot_sha256':sha(snapshot),'generated_with_refs':rel(with_refs),'generated_with_refs_sha256':sha(with_refs),
        'generated_with_refs_prefix_bytes':snapshot.stat().st_size,'proof_reference_addon_sha256':hashlib.sha256(addon).hexdigest(),
        'proof_reference_output':rel(output),'proof_reference_requests':['solution',*[r['generated_name'] for r in m['public_inline_ci_requests']]],
        'certified_definition_dependencies':len(definitions),'certified_child_dependencies':children,
        'equation_certificate':{'path':equation['path'],'sha256':equation['sha256']},'compile_manifests':manifests,
        'exact_old_snapshot_prefix':True,'server_parent_pending':True,'pure_python_prepared':True,'Lean_started':False,
        'validated':False,'submission_ready':False}
    budget=source_stage.path_budget(STAGE,prep)
    prep['maximum_absolute_path_length']=max(budget.values())
    context.write_exact(STAGE/'preparation.json',prep)
    # Compiler imports and input maps are checked using the same reviewed
    # evidence; no second graph replay is performed for the prepare/check pair.
    for name,row in manifests.items():
        manifest=read(TASK/row['manifest']);source=STAGE/name
        readonly.formal.runner.verify_manifest_inputs(manifest)
        readonly.formal.runner.verify_source_certificate(source,manifest)
        readonly.formal.runner.certified_imports(source,manifest)
    return prep

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--prepare',action='store_true',required=True);p.parse_args()
    print(json.dumps(prepare(),indent=2))

if __name__=='__main__':main()
