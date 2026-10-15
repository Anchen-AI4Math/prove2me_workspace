"""Pure AP17 candidate/final stage for the already Open source017 arithmetic minor target."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import stage_actual_minor_arithmetic_lower_bound_source017_route as route
import stage_selected_minor_lower_child_mirror as child
import stage_selected_minor_lower_child_mirror_probe_v5 as mirror
MIRROR_STAGE=mirror.STAGE
TASK,ROOT,V=route.TASK,route.ROOT,route.V
SELF=Path(__file__).resolve();STAGE=route.STAGE
COMMIT=route.COMMIT;TARGET=route.SOURCE_NAME;PLATFORM_NAME=route.PLATFORM_NAME
TARGET_MODULE=route.SOURCE_MODULE;TARGET_ID=route.TARGET_ID
TARGET_OUTPUT='Theorems/Thm_'+PLATFORM_NAME.replace('.','_')+'.lean'
SOLUTION_MODULE='Solutions.Sol_actual_minor_lower_source017_ap17'
SOLUTION_OUTPUT=SOLUTION_MODULE.replace('.','/')+'.lean'
SOURCE_SNAPSHOT,GENERATED_SNAPSHOT='SourceSnapshot.lean','GeneratedSnapshot.lean'
SOURCE_TYPE_JSON,GENERATED_TYPE_JSON='source-types.json','generated-types.json'
SOURCE_REFS_JSON,GENERATED_REFS_JSON='source-proof-references.json','generated-proof-references.json'
FILES=[TARGET_OUTPUT,SOLUTION_OUTPUT,SOURCE_SNAPSHOT,GENERATED_SNAPSHOT]
MODES=['modecheck','emit-olean','modecheck','modecheck'];MANIFESTS=['c1.json','c2.json','c3.json','c4.json']
CERTIFICATE='node-validation.json';CONSUMER=TASK/'scripts/certify_actual_minor_arithmetic_lower_bound_source017_node.py'
RUNNER=child.RUNNER;LEGACY_RUNNER=child.LEGACY_RUNNER
clearing=child.parent.clearing
read,sha,sha_bytes,encode,need,rel=route.read,route.sha,route.sha_bytes,route.encode,route.need,route.rel
workspace_rel,verification_rel=child.parent.workspace_rel,child.parent.verification_rel

def snapshot(side,names,boundary):
    module=TARGET_MODULE if side=='source' else SOLUTION_MODULE
    owners=[TARGET_MODULE,'SourceSnapshot'] if side=='source' else [SOLUTION_MODULE,child.MODULE,'GeneratedSnapshot']
    typ=SOURCE_TYPE_JSON if side=='source' else GENERATED_TYPE_JSON
    refs=SOURCE_REFS_JSON if side=='source' else GENERATED_REFS_JSON
    roots='#['+', '.join('`'+n for n in names)+']'
    return ('import Lean\nimport '+module+'\n\n'+child.parent.clearing.SNAPSHOT_CORE.read_text(encoding='utf-8').rstrip()+'\n'+child.parent.clearing.base.ap8.PROBE+'\n'+child.parent.clearing.PROBE+'\nrun_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot '+roots+' '+json.dumps(workspace_rel(STAGE/typ))+'\n  SelectedMinorProofSnapshot.exportBundle '+json.dumps(side)+' '+json.dumps(workspace_rel(STAGE/refs))+' '+roots+' #['+', '.join(json.dumps(n) for n in owners)+'] #['+', '.join(json.dumps(n) for n in sorted(boundary))+']\n#print axioms '+names[-1]+'\n').encode()

def proof_files():
    route.check_only();graph,closure,provided,rows,commands,pins,renamed,actual,det=route.source_units()
    target=commands[-1][2];u=rows[-1];a=u['start'];ns=u['ast']['nameRange']['start']['offset']-a;ne=u['ast']['nameRange']['end']['offset']-a;vs=u['ast']['valueStart']['offset']-a
    wire=route.OPEN_WIRE.read_bytes();target_imports=[line.removeprefix('import ').strip() for line in actual['preamble'].splitlines() if line.startswith('import ')]
    need(child.parent.clearing.base.runner.certified_imports(route.OPEN_WIRE,{'imports':target_imports,'output':workspace_rel(route.OPEN_WIRE),'output_sha256':sha(route.OPEN_WIRE)})==target_imports,'Saved wire imports differ')
    imports=target_imports+[child.MODULE]
    parts=[(''.join('import '+m+'\n' for m in imports)+'\nnamespace '+route.PREFIX[:-1]+'\n\nopen Filter\nopen scoped Topology\n\n').encode()]
    for _,name,command in commands[:-1]:parts.append(command+b'\n\n')
    parts += [('end '+route.PREFIX[:-1]+'\n\nopen OAI.PiExponent OAI.PiExponent.DeterminantContradiction\n\n').encode(),target[:ns]+b'solution'+target[ne:]+b'\n']
    body=b''.join(parts);need(body.count(b'theorem solution ')==1 and b'sorry' not in body and b'FixedDeterminantFamily' not in body and body[body.rindex(b':= by'):].rstrip()==target[vs:].rstrip(),'Original AP17 global solution proof or boundary differs')
    helpers=[r['name'] for r in rows[:-1]];source_names=helpers+[TARGET];generated_names=helpers+['solution'];boundary=closure&provided
    outputs={TARGET_OUTPUT:wire,SOLUTION_OUTPUT:body,SOURCE_SNAPSHOT:snapshot('source',source_names,boundary),GENERATED_SNAPSHOT:snapshot('generated',generated_names,boundary),'wire-theorem-source.lean':wire,'academic-metadata.json':encode({'title':'Arithmetic lower bound for the actual interpolation minor','statement':r'For the original fixed admissible data $d$, a positive height $H$, and any selected square minor $A$ with $\det A\ne0$, the normalized logarithmic determinant satisfies $\log\lVert\det A\rVert/(N H)\ge -(1-\mu)-E$. Here $N$ is the actual row count, $\mu$ is the normalized mean row weight, and $E=d.\mathrm{arithmeticError}$. All quantities use the original source definitions.','explanation':'The two original denominator/weight interface lemmas reduce this statement to the original generic selected-minor arithmetic lower bound. Only that genuine proved parent theorem is reused.','source_commit':COMMIT,'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean#L74-L86','tags':['number-theory','linear-algebra','openai-pi-exponent-017']})}
    return outputs,rows,closure,boundary,pins,actual,imports,target_imports

def candidate_files():
    files,rows,closure,boundary,pins,actual,imports,target_imports=proof_files()
    for p in [SELF,CONSUMER,child.SELF,child.CONSUMER,mirror.SELF,mirror.CONSUMER,RUNNER,LEGACY_RUNNER,child.STAGE/'candidate-spec.json',child.STAGE/child.CANDIDATE,child.STAGE/child.PROBE_CANDIDATE,route.STAGE/'route-preparation.json']:pins[rel(p)]=sha(p)
    outputs={'candidate/'+f+'.txt':raw for f,raw in files.items()}
    outputs['candidate-spec.json']=encode({'schema_version':1,'artifact_kind':'ap17-source017-minor-arithmetic-candidate','source_commit':COMMIT,'source_name':TARGET,'platform_name':PLATFORM_NAME,'platform_theorem_id':TARGET_ID,'source_module':TARGET_MODULE,'target_ast':rows[-1]['ast'],'inline_exact_source_units':rows,'original_proof_AST_units':3,'original_source_lines':17,'inline_helper_names':[r['name'] for r in rows[:-1]],'source_type_only_names':[r['name'] for r in rows],'generated_type_only_names':[r['name'] for r in rows[:-1]]+['solution'],'provider_subtracted_names':sorted(boundary),'generic_lower_public_boundary_name':route.GENERIC_LOWER,'exact_saved_Open_wire_sha256':sha(route.OPEN_WIRE),'preamble':actual['preamble'],'formal_statement':actual['formal_statement'],'target_imports':target_imports,'solution_imports':imports,'files':{f:sha_bytes(raw) for f,raw in files.items()},'only_target_binding_name_changed':True,'all_original_proof_suffixes_unchanged':True,'existing_port_adaptations':[],'generic_lower_actual_kernel_certificate_pending':True,'generic_lower_real_Accepted_Proved_pending':True,'generic_lower_closed_private_mirror_certificate_pending':True,'compiler_manifests_finalized':False,'input_hashes':pins,'validated':False,'submission_ready':False,'Lean_started':False,'API_used':False})
    return outputs

def check_candidate():
    outputs=candidate_files()
    for f,raw in outputs.items():need((STAGE/f).read_bytes()==raw,'Immutable AP17 candidate differs: '+f)
    return {'checked_files':len(outputs),'original_AST_units':3,'original_source_lines':17,'exact_existing_Open_wire':True,'real_generic_lower_boundary_pending':True,'compiler_manifests_finalized':False,'Lean_started':False,'API_used':False}

def final_files():
    check_candidate();cert_path=MIRROR_STAGE/mirror.CERTIFICATE
    need(cert_path.is_file(),'AP17 final contexts await genuine Accepted generic lower private-mirror certificate')
    import certify_selected_minor_lower_child_mirror_probe_v5 as child_consumer
    cert=child_consumer.validate();need(encode(cert)==cert_path.read_bytes() and cert['validated'] is True and cert['accepted_parent_Proved'] is True and cert['public_platform_boundary_names']==[route.GENERIC_LOWER],'Actual generic lower closed boundary certificate differs')
    files,rows,closure,boundary,pins,actual,imports,target_imports=proof_files();p=read(STAGE/'candidate-spec.json');inputs=dict(p['input_hashes'])
    for path,h in read(MIRROR_STAGE/'preparation.json')['input_hashes'].items():need(sha(TASK/path)==h,'Mirror immutable compiler input changed');inputs[path]=h
    for pf in cert['preflights'].values():
        path=TASK/pf['record'];need(sha(path)==pf['record_sha256'],'Mirror actual preflight sidecar changed');inputs[rel(path)]=sha(path)
        for key in ['source','manifest','log']:
            path=child.context.file(pf['data'][key]);inputs[rel(path)]=sha(path)
    for path in [cert_path,mirror.ACCEPTED,MIRROR_STAGE/'preparation.json',child.STAGE/child.OUTPUT,MIRROR_STAGE/mirror.SNAPSHOT,Path(child_consumer.__file__),STAGE/'candidate-spec.json',TASK/cert['provider_olean']]:inputs[rel(path)]=sha(path)
    for path,h in cert['implementation_hashes'].items():need(sha(TASK/path)==h,'Mirror implementation hash changed');inputs[path]=h
    for f,h in cert['generated_json_sha256'].items():need(sha(MIRROR_STAGE/f)==h,'Mirror kernel JSON changed');inputs[rel(MIRROR_STAGE/f)]=h
    manifests={};commands=[]
    for i,(output,mode,imps) in enumerate(zip(FILES,MODES,[target_imports,imports,['Lean',TARGET_MODULE],['Lean',SOLUTION_MODULE]],strict=True),1):
        files[f'c{i}.json']=encode({'schema_version':1,'artifact_kind':'ap17-source017-minor-arithmetic-bounded-manifest','output':workspace_rel(STAGE/output),'output_sha256':sha_bytes(files[output]),'imports':imps,'input_hashes':inputs,'runtime_sha256':sha(child.parent.clearing.RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'bounded_runner':rel(RUNNER),'bounded_runner_sha256':sha(RUNNER),'legacy_runner_sha256':sha(LEGACY_RUNNER),'validated':False,'submission_ready':False})
        manifests[output]={'sha256':sha_bytes(files[output]),'mode':mode,'emit_olean':mode=='emit-olean','manifest':f'c{i}.json','imports':imps}
        commands.append('python scripts/preflight_staged_module_windows_bounded.py '+verification_rel(STAGE/output)+' --root ap17/actual-minor-arithmetic-lower-bound --imports-manifest ap17/actual-minor-arithmetic-lower-bound/c'+str(i)+'.json --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    prep=dict(p);prep.update({'artifact_kind':'ap17-source017-minor-arithmetic-node-preparation','generic_lower_actual_kernel_certificate_pending':False,'generic_lower_real_Accepted_Proved_pending':False,'generic_lower_closed_private_mirror_certificate_pending':False,'compiler_manifests_finalized':True,'generic_lower_mirror_certificate':rel(cert_path),'generic_lower_mirror_certificate_sha256':sha(cert_path),'generic_lower_accepted_readback_sha256':sha(child.ACCEPTED),'input_hashes':inputs,'files':manifests,'compile_commands':commands})
    files['preparation.json']=encode(prep);files['compile-commands.txt']=('\n'.join(commands)+'\n').encode();return files

def check_only():
    outputs=final_files()
    for f,raw in outputs.items():need((STAGE/f).read_bytes()==raw,'Immutable AP17 final stage differs: '+f)
    return {'checked_files':len(outputs),'original_AST_units':3,'original_source_lines':17,'Lean_started':False,'API_used':False,'validated':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);g=p.add_mutually_exclusive_group(required=True)
    for flag in ['prepare-candidate','check-candidate','prepare','check-only']:g.add_argument('--'+flag,action='store_true')
    a=p.parse_args()
    if a.prepare_candidate or a.prepare:
        for f,raw in (final_files() if a.prepare else candidate_files()).items():
            path=STAGE/f
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+f)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only() if a.prepare or a.check_only else check_candidate(),indent=2))
if __name__=='__main__':main()
