"""Pure staging of the source shifted-truncation Gaussian coefficient theorem."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import stage_grouped_actual_mean_bounds_node as mean

TASK,ROOT,V=mean.TASK,mean.ROOT,mean.V
STAGE=V/'ap13/shifted-gaussian'
SELF=Path(__file__).resolve()
COMMIT=mean.COMMIT
AST,SCOPES,GRAPH,RUNTIME,SNAPSHOT_CORE=mean.AST,mean.SCOPES,mean.GRAPH,mean.RUNTIME,mean.SNAPSHOT_CORE
TARGET_MODULE='OAI.NumberTheory.PiExponent.Approximation.Arithmetic'
TARGET='OAI.PiExponent.Arithmetic.shifted_truncation_product_coeff_gaussian'
PLATFORM_NAME=TARGET
TARGET_OUTPUT='Theorems/Thm_'+TARGET.replace('.','_')+'.lean'
SOLUTION_MODULE='Solutions.Sol_OAI_PiExponent_Arithmetic_shifted_truncation_product_coeff_gaussian_ap13_global'
SOLUTION_OUTPUT=SOLUTION_MODULE.replace('.','/')+'.lean'
SOURCE_SNAPSHOT,GENERATED_SNAPSHOT='SourceSnapshot.lean','GeneratedSnapshot.lean'
SOURCE_TYPE_JSON,GENERATED_TYPE_JSON='source-types.json','generated-types.json'
SOURCE_REFS_JSON,GENERATED_REFS_JSON='source-proof-references.json','generated-proof-references.json'
FILES=[TARGET_OUTPUT,SOLUTION_OUTPUT,SOURCE_SNAPSHOT,GENERATED_SNAPSHOT]
MODES=['modecheck','emit-olean','modecheck','modecheck']
MANIFESTS=['c1.json','c2.json','c3.json','c4.json']
CERTIFICATE='node-validation.json'
DEFINITION_MODULE='Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic'
IMPORTS=['Mathlib.Algebra.Polynomial.Eval.Subring','Mathlib.LinearAlgebra.Matrix.Determinant.Basic','Mathlib.NumberTheory.Chebyshev','Mathlib.NumberTheory.Zsqrtd.GaussianInt','Mathlib.RingTheory.PowerSeries.Log','Mathlib.RingTheory.PowerSeries.Trunc','Mathlib.Tactic',DEFINITION_MODULE]
HELPER_SHORTS=['dvd_lcmUpto_of_pos_le','lcm_mul_log_coeff_gaussian','cleared_log_trunc_mem','gaussian_C_mem','cleared_shifted_log_trunc_mem','cleared_polynomial_power_mem','cleared_polynomial_product_mem','common_denominator_coeff_gaussian']
HELPER_NAMES={TARGET_MODULE:HELPER_SHORTS}
PREFIX='OAI.PiExponent.Arithmetic.'
SOURCE_SHA='a1c5ccc7f5644ef75b932bc511909df81780ed6169b7b0faf85d8dc4076b5d9f'
read,encode,sha,sha_bytes,need,rel,workspace_rel,verification_rel=mean.read,mean.encode,mean.sha,mean.sha_bytes,mean.need,mean.rel,mean.workspace_rel,mean.verification_rel
base=mean.base
PROBE=mean.PROBE.replace('ActualMeanBoundsProofSnapshot','ShiftedGaussianProofSnapshot')

def source_path(tree='port'):return base.source_path(TARGET_MODULE,tree)

def provider():
    coverage=read(base.ap9.COVERAGE);r=next(r for r in coverage['records'] if r['definition_name']==DEFINITION_MODULE.removeprefix('Definitions.Def_'));path=TASK/r['publication_record'];pub=read(path);body=pub['target_readback']['body']['definition'].encode()
    need(sha(path)==r['publication_record_sha256'] and sha_bytes(body)==r['literal_source_sha256'] and body==pub['publish_intent']['payload']['definition'].encode() and pub['last_publish_verdict']['body']['status']=='PUBLISHED','Published Arithmetic literal provider differs')
    return {'module':DEFINITION_MODULE,'publication_record':rel(path),'publication_record_sha256':sha(path),'literal_source_sha256':sha_bytes(body),'definition_id':pub['definition_id'],'provided_declarations':['OAI.PiExponent.Arithmetic.lcmConstant','OAI.PiExponent.Arithmetic.lcmConstant_pos'],'used_by_target_proof':False,'import_basis':'Existing original Arithmetic namespace/data package, with exactly the same seven original Mathlib imports.'},path

def authority():
    port=source_path();original=source_path('source');raw=port.read_bytes();orig=original.read_bytes().replace(b'\r\n',b'\n')
    am=next(m for m in read(AST)['modules'] if m['module']==TARGET_MODULE);sm=next(m for m in read(SCOPES)['modules'] if m['source']==TARGET_MODULE.replace('.','/')+'.lean')
    need(am['source_sha256']==sm['source_sha256']==sha(port)==SOURCE_SHA,'Pinned actual source inventory differs')
    graph={r['name']:r for r in map(json.loads,GRAPH.read_text(encoding='utf-8').splitlines())};closure=set();todo=[TARGET]
    while todo:
        n=todo.pop()
        if n in closure:continue
        need(n in graph,'Unknown source graph name');closure.add(n);todo+=graph[n]['typeDeps']+graph[n]['valueDeps']
    names=[PREFIX+n for n in HELPER_SHORTS]+[TARGET];need(closure==set(names) and len(names)==9,'Exact nine-CI source closure differs')
    rows=[];commands=[];adaptations=[]
    for name in names:
        u=next(u for u in am['units'] if name in u['graph_names']);s=next(s for s in sm['declarations'] if s['verified_name']==name);a,b=u['start']['offset'],u['end']['offset'];command=raw[a:b];normalized=command.replace(b'\r\n',b'\n');equal=orig.count(normalized)==1
        need(u['graph_names']==[name] and u['graph_kinds']==['theorem'] and u['privateTok'] is None and not u['is_instance_command'] and not u['is_local_instance'] and s['namespace']=='OAI.PiExponent.Arithmetic' and all(x['kind']=='namespace' for x in s['scope_stack']) and s['context_commands']==[],'Original theorem AST/scope differs: '+name)
        if not equal:
            need(name==PREFIX+'lcm_mul_log_coeff_gaussian' and normalized.count(b'if_neg hk0')==1 and orig.count(normalized.replace(b'if_neg hk0',b'ite_eq_right hk0'))==1,'Unrecorded original/port command difference')
            original_command=normalized.replace(b'if_neg hk0',b'ite_eq_right hk0')
            vs=u['valueStart']['offset']-a;need(command[:vs].replace(b'\r\n',b'\n')==original_command[:original_command.index(b':=')],'Compatibility edit changed theorem statement')
            adaptations.append({'name':name,'original_proof_step':'rw [PowerSeries.coeff_log, ite_eq_right hk0, hm]','ported_proof_step':'rw [PowerSeries.coeff_log, if_neg hk0, hm]','original_normalized_command_sha256':sha_bytes(original_command),'ported_raw_command_sha256':sha_bytes(command),'statement_unchanged':True,'existing_port_not_modified':True})
        else:original_command=normalized
        rows.append({'name':name,'module':TARGET_MODULE,'kind':'theorem','ast':u,'scope':s,'graph':graph[name],'source':rel(port),'source_sha256':sha(port),'original':rel(original),'original_sha256':sha(original),'start':a,'end':b,'command_sha256':sha_bytes(command),'original_port_command_equal_modulo_line_endings':equal,'original_normalized_command_sha256':sha_bytes(original_command)})
        commands.append((a,name,command,original_command))
    need([n for _,n,_,_ in sorted(commands)]==names and len(adaptations)==1,'Source order/adaptation domain differs')
    witness,pubpath=provider();pins={rel(p):sha(p) for p in [port,original,pubpath,base.ap9.COVERAGE]}
    return graph,closure,set(),rows,commands,pins,adaptations,witness

def snapshot(side,names):
    module=TARGET_MODULE if side=='source' else SOLUTION_MODULE;owner=module
    typeout=SOURCE_TYPE_JSON if side=='source' else GENERATED_TYPE_JSON;refsout=SOURCE_REFS_JSON if side=='source' else GENERATED_REFS_JSON
    ns='#['+', '.join('`'+n for n in names)+']'
    return ('import Lean\nimport '+module+'\n\n'+SNAPSHOT_CORE.read_text(encoding='utf-8').rstrip()+'\n'+base.ap8.PROBE+'\n'+PROBE+'\nrun_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot '+ns+' '+json.dumps(workspace_rel(STAGE/typeout))+'\n  ShiftedGaussianProofSnapshot.exportBundle '+json.dumps(side)+' '+json.dumps(workspace_rel(STAGE/refsout))+' '+ns+' #['+json.dumps(owner)+'] #[]\n#print axioms '+names[-1]+'\n').encode()

def metadata():
    return {'title':'Gaussian integrality of cleared shifted logarithm product coefficients','statement':r'Let $S$ be a finite index set; let $T_i,q_i,e_i,d_i$ be natural numbers, $z_i\in\mathbb Z[\mathrm i]$, and $P\in\mathbb Z[\mathrm i][X]$. Assume $d_i\le e_i$ for $i\in S$. Write $L_i=\operatorname{lcm}(1,\ldots,T_i)$ and $\ell_{T_i}(X)$ for the order-$T_i$ polynomial truncation of $\log(1+X)$. For every natural $k$,'+'\n\n'+r'$$\left(\prod_{i\in S}L_i^{e_i}\right)[X^k]\left(P(X)\prod_{i\in S}(z_i+q_i\ell_{T_i}(X))^{d_i}\right)\in\mathbb Z[\mathrm i]\subset\mathbb C.$$'+'\n\n'+r'This is the exact coefficient-integrality statement used to clear denominators in the interpolation matrix entries.','explanation':'The least common multiple clears each truncated logarithm coefficient. Shift by a Gaussian integer and multiply by a natural number, take powers using d_i≤e_i, then multiply the cleared factors and extract a coefficient.','tags':['number-theory','polynomial','linear-algebra','openai-pi-exponent-017'],'source_commit':COMMIT,'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Approximation/Arithmetic.lean#L270-L279'}

def stage_files():
    graph,closure,provided,rows,commands,pins,adaptations,witness=authority();targetrow=rows[-1];command=commands[-1][2];unit=targetrow['ast'];a=targetrow['start'];ns,ne=unit['nameRange']['start']['offset']-a,unit['nameRange']['end']['offset']-a;vs=unit['valueStart']['offset']-a
    need([a,targetrow['end']]==[12720,13370] and command[vs:vs+5]==b':= by','Pinned target AST proof boundary changed')
    preamble=(''.join('import '+m+'\n' for m in IMPORTS)+'\nopen OAI.PiExponent.Arithmetic\n\n').encode();formal=command[:ns]+PLATFORM_NAME.encode()+command[ne:vs]+b':= by\n  sorry\n';target=preamble+formal
    renamed=command[:ns]+b'solution'+command[ne:];need(renamed[renamed.find(b':= by'):]==command[vs:],'Target literal port proof changed')
    solution=(''.join('import '+m+'\n' for m in IMPORTS)+'\nnamespace OAI.PiExponent.Arithmetic\n\n').encode()+b'\n\n'.join(c[2] for c in commands[:-1])+b'\n\nend OAI.PiExponent.Arithmetic\n\nopen OAI.PiExponent.Arithmetic\n\n'+renamed+b'\n'
    names=[r['name'] for r in rows[:-1]]
    generated={TARGET_OUTPUT:target,SOLUTION_OUTPUT:solution,'wire-theorem-source.lean':target,'original-target-command.lean.txt':command,'academic-metadata.json':encode(metadata()),SOURCE_SNAPSHOT:snapshot('source',names+[TARGET]),GENERATED_SNAPSHOT:snapshot('generated',names+['solution']),'port-adaptation.json':encode(adaptations)}
    for _,name,raw,orig in commands:
        generated['source-units/'+name.replace('.','_')+'.port.lean.txt']=raw;generated['source-units/'+name.replace('.','_')+'.original-normalized.lean.txt']=orig
    inputs={rel(p):sha(p) for p in [SELF,Path(mean.__file__),Path(base.__file__),AST,SCOPES,GRAPH,RUNTIME,SNAPSHOT_CORE,Path(base.ap8.__file__),Path(base.runner.__file__)]};inputs.update(pins)
    files={};compile_commands=[]
    for output,mode,mf,imports in zip(FILES,MODES,MANIFESTS,[IMPORTS,IMPORTS,['Lean',TARGET_MODULE],['Lean',SOLUTION_MODULE]],strict=True):
        files[output]={'sha256':sha_bytes(generated[output]),'mode':mode,'emit_olean':mode=='emit-olean','manifest':mf,'imports':imports}
        generated[mf]=encode({'schema_version':1,'artifact_kind':'ap13-shifted-gaussian-bounded-compiler-manifest','output':workspace_rel(STAGE/output),'output_sha256':sha_bytes(generated[output]),'imports':imports,'input_hashes':inputs,'runtime_sha256':sha(RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'validated':False,'submission_ready':False})
        compile_commands.append('python scripts/preflight_staged_module.py '+verification_rel(STAGE/output)+' --root ap13/shifted-gaussian --imports-manifest '+verification_rel(STAGE/mf)+' --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    generated['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap13-shifted-gaussian-node-preparation','source_name':TARGET,'platform_name':PLATFORM_NAME,'source_module':TARGET_MODULE,'source_commit':COMMIT,'target_ast':unit,'target_source_command_sha256':sha_bytes(command),'target_proof_suffix_sha256':sha_bytes(command[vs:]),'target_original_command_equal_modulo_line_endings':True,'global_solution_preserves_literal_port_proof':True,'all_helper_proofs_copied_from_immutable_port':True,'all_helper_proofs_literal_original':False,'existing_port_adaptations':adaptations,'preamble':preamble.decode(),'formal_statement':formal.decode(),'graph_closure_names':sorted(closure),'provider_subtracted_names':[],'inline_helper_names':names,'inline_exact_source_units':rows[:-1],'target_exact_source_unit':targetrow,'source_type_only_names':names+[TARGET],'generated_type_only_names':names+['solution'],'source_theorem_values_null':True,'generated_theorem_values_null':True,'source_total_AST_units':9,'source_total_lines':89,'published_arithmetic_provider':witness,'direct_original_Mathlib_imports':IMPORTS[:-1],'blanket_Mathlib_import':False,'input_hashes':inputs,'files':files,'compile_commands':compile_commands,'metadata':metadata(),'exactName_lookup_required_by_root':PLATFORM_NAME,'Lean_started':False,'API_used':False,'validated':False,'submission_ready':False,'proposal_status':'Draft'})
    generated['compile-commands.txt']=('\n'.join(compile_commands)+'\n').encode();return generated

def check_only():
    generated=stage_files()
    for filename,raw in generated.items():need((STAGE/filename).is_file() and (STAGE/filename).read_bytes()==raw,'Immutable stage differs: '+filename)
    for output,mf in zip(FILES,MANIFESTS,strict=True):
        m=read(STAGE/mf);base.runner.verify_manifest_inputs(m);base.runner.verify_source_certificate(STAGE/output,m)
    return {'checked_files':len(generated),'source_AST_units':9,'inline_helpers':8,'source_lines':89,'original_port_compatibility_edits':1,'all_hashes_match':True,'Lean_started':False,'API_used':False,'validated':False,'submission_ready':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);m=p.add_mutually_exclusive_group(required=True);m.add_argument('--prepare',action='store_true');m.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        for filename,raw in stage_files().items():
            path=STAGE/filename
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+filename)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),ensure_ascii=False,indent=2))
if __name__=='__main__':main()
