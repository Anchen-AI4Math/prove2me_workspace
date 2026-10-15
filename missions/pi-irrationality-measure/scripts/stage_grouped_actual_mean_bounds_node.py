"""Pure source-faithful staging of the bounded grouped actualMean_bounds proof."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import stage_grouped_collision_rate_node as base

TASK,ROOT,V=base.TASK,base.ROOT,base.V
STAGE=V/'ap12/mean-bounds'
SELF=Path(__file__).resolve()
COMMIT=base.COMMIT
AST,SCOPES,GRAPH,RUNTIME,SNAPSHOT_CORE=base.AST,base.SCOPES,base.GRAPH,base.RUNTIME,base.SNAPSHOT_CORE
TARGET='OAI.PiExponent.DeterminantContradiction.actualMean_bounds'
PLATFORM_NAME=TARGET
TARGET_MODULE=base.TARGET_MODULE
TARGET_OUTPUT='Theorems/Thm_'+PLATFORM_NAME.replace('.','_')+'.lean'
SOLUTION_MODULE='Solutions.Sol_OAI_PiExponent_DeterminantContradiction_actualMean_bounds_ap12_global'
SOLUTION_OUTPUT=SOLUTION_MODULE.replace('.','/')+'.lean'
SOURCE_SNAPSHOT,GENERATED_SNAPSHOT='SourceSnapshot.lean','GeneratedSnapshot.lean'
SOURCE_TYPE_JSON,GENERATED_TYPE_JSON='source-types.json','generated-types.json'
SOURCE_REFS_JSON,GENERATED_REFS_JSON='source-proof-references.json','generated-proof-references.json'
FILES=[TARGET_OUTPUT,SOLUTION_OUTPUT,SOURCE_SNAPSHOT,GENERATED_SNAPSHOT]
MODES=['modecheck','emit-olean','modecheck','modecheck']
MANIFESTS=['c1.json','c2.json','c3.json','c4.json']
CERTIFICATE='node-validation.json'
IMPORTS=['Mathlib.Tactic',base.ap10.config('determinant')['platform_module']]
HELPER_NAMES={
 'OAI.NumberTheory.PiExponent.Polynomials.SimplexCounting':['mem_realWeightedSimplex','mem_strictWeightedSimplex'],
 'OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix':['row_mem_iff','row_weight_lt'],
 'OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic':['actual_row_card_pos','ceil_log_weight_pos','row_weighted_cost_le','meanRowWeight_nonneg','meanRowWeight_le_theta'],
 TARGET_MODULE:['finiteDenominators_two_le'],
}
PREFIXES={m:base.PREFIXES[m] for m in HELPER_NAMES}
read,encode,sha,sha_bytes,need,rel,workspace_rel,verification_rel=base.read,base.encode,base.sha,base.sha_bytes,base.need,base.rel,base.workspace_rel,base.verification_rel

def authority():
    bindings,pins,_=base.ap10.published_bindings();provided=set(bindings)
    records=[V/'ap10/interpolation/publication/publication.json',V/'ap10/arithmetic/publication/publication.json',V/'ap10/determinant/publication-helper-v2/publication.json']
    for key in base.ap10.CONFIGS:
        c=base.ap10.config(key); provided.update(c['names'])
        cert=c['stage']/('actual-provider-validation-helper-v2.json' if key=='determinant' else 'actual-provider-validation.json')
        report=read(cert);need(report['validated'] is True and report['Std3_only'] is True and report['provided_names']==c['names'],'Missing actual certified core provider')
        for path in [c['stage']/'preparation.json',c['stage']/c['provider_file'],cert]:pins[rel(path)]=sha(path)
    for path in records:
        r=read(path);body=r['target_readback']['body']
        need(r['last_publish_verdict']['body']['status']=='PUBLISHED' and body['status']=='Definition' and body['definition']==r['publish_intent']['payload']['definition'],'Core provider actual publication differs')
        pins[rel(path)]=sha(path)
    graph={x['name']:x for x in map(json.loads,GRAPH.read_text(encoding='utf-8').splitlines())}
    closure=set();pending=[TARGET]
    while pending:
        n=pending.pop()
        if n in closure:continue
        need(n in graph,'Unknown actual source dependency: '+n);closure.add(n);pending+=graph[n]['typeDeps']+graph[n]['valueDeps']
    helpers={PREFIXES[m]+n for m,names in HELPER_NAMES.items() for n in names}
    need(len(closure)==36 and len(helpers)==10 and closure-provided==helpers|{TARGET},'Actual 36-name source closure changed')
    ast_modules={m['module']:m for m in read(AST)['modules']};scope_modules={m['source']:m for m in read(SCOPES)['modules']}
    commands={};rows=[]
    for module,names in HELPER_NAMES.items():
        port=base.source_path(module);original=base.source_path(module,'source');raw=port.read_bytes();orig=original.read_bytes().replace(b'\r\n',b'\n')
        am=ast_modules[module];sm=scope_modules[module.replace('.','/')+'.lean'];need(am['source_sha256']==sm['source_sha256']==sha(port),'Actual source inventory changed')
        for path in [port,original]:pins[rel(path)]=sha(path)
        selected=[]
        for short in names:
            name=PREFIXES[module]+short;u=next(u for u in am['units'] if name in u['graph_names']);s=next(s for s in sm['declarations'] if s['verified_name']==name);a,b=u['start']['offset'],u['end']['offset'];command=raw[a:b]
            contexts=[raw[x['range']['start']['offset']:x['range']['end']['offset']].decode() for x in s['context_commands']]
            expected=['open Filter','open scoped Topology'] if module==TARGET_MODULE else ['open scoped BigOperators']+(['open Filter Topology'] if module.endswith('SimplexCounting') else [])
            need(u['graph_names']==[name] and u['graph_kinds']==['theorem'] and u['privateTok'] is None and not u['is_instance_command'] and not u['is_local_instance'] and all(x['kind']=='namespace' for x in s['scope_stack']) and contexts==expected and s['namespace']==PREFIXES[module][:-1] and orig.count(command.replace(b'\r\n',b'\n'))==1,'Original helper AST/scope changed: '+name)
            selected.append((a,name,command));rows.append({'name':name,'module':module,'kind':'theorem','ast':u,'scope':s,'graph':graph[name],'source':rel(port),'source_sha256':sha(port),'original':rel(original),'original_sha256':sha(original),'start':a,'end':b,'command_sha256':sha_bytes(command)})
        need([n for _,n,_ in sorted(selected)]==[PREFIXES[module]+n for n in names],'Source helper order changed');commands[module]=selected
    return graph,closure,provided,rows,commands,pins

PROBE=r'''
namespace ActualMeanBoundsProofSnapshot
open Lean Meta FullRowMinorProofSnapshot
def exportBundle (side output : String) (roots : Array Name) (owners boundary : Array String) : MetaM Unit := do
  let env ← getEnv
  let mut pending := roots.toList
  let mut seen : Array Name := #[]
  let mut found : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !seen.contains n && !boundary.contains n.toString then
      seen := seen.push n
      if owners.contains (← ownerModule env n) then
        found := found.push n
        let some ci := env.find? n | throwError "Missing actual proof CI: {n}"
        let some value := valueOf ci | throwError "Missing actual proof value: {n}"
        pending := pending ++ (refs (mkApp ci.type value)).toList
  for root in roots do
    unless found.contains root do throwError "Actual proof root was not exported: {root}"
  found := found.qsort (fun a b => a.toString < b.toString)
  let rows ← found.mapM (fun n => do pure <| Json.mkObj (← ciRow n true))
  IO.FS.writeFile output (Json.mkObj [
    ("schemaVersion",toJson (1 : Nat)),("side",toJson side),
    ("probeMainModule",toJson env.mainModule.toString),
    ("rootNames",toJson (roots.map Name.toString)),
    ("boundaryNames",toJson boundary),("rows",Json.arr rows)] |>.compress)
end ActualMeanBoundsProofSnapshot
'''

def snapshot(side,roots,owners,boundary):
    module=TARGET_MODULE if side=='source' else SOLUTION_MODULE
    out=SOURCE_TYPE_JSON if side=='source' else GENERATED_TYPE_JSON;refsout=SOURCE_REFS_JSON if side=='source' else GENERATED_REFS_JSON
    return ('import Lean\nimport '+module+'\n\n'+SNAPSHOT_CORE.read_text(encoding='utf-8').rstrip()+'\n\n'+base.ap8.PROBE+'\n'+PROBE+'\nrun_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #['+', '.join('`'+n for n in roots)+'] '+json.dumps(workspace_rel(STAGE/out))+'\n  ActualMeanBoundsProofSnapshot.exportBundle '+json.dumps(side)+' '+json.dumps(workspace_rel(STAGE/refsout))+' #['+', '.join('`'+n for n in roots)+'] #['+', '.join(json.dumps(x) for x in owners)+'] #['+', '.join(json.dumps(x) for x in sorted(boundary))+']\n#print axioms '+roots[-1]+'\n').encode()

def metadata():
    return {'title':'Bounds for the original mean row weight of admissible interpolation data','statement':r'Let $\nu$ be real and let $d$ be fixed admissible data from the original determinant construction. At every positive real height $H$, its normalized mean row weight $b_d(H)$ satisfies'+'\n\n'+r'$$0\le b_d(H)\le\theta_d.$$'+'\n\n'+r'Here $\theta_d$ is the theta parameter of the fixed base data, and $b_d(H)$ is the weighted row sum divided by the row count times $H$. This controls the mean used in the conditional determinant contradiction.','explanation':'Every row has nonnegative logarithmic cost, and the defining strict weighted simplex bounds its cost by the height times theta. Sum the row bounds and divide by the positive row count and height.','tags':['number-theory','linear-algebra','openai-pi-exponent-017'],'source_commit':COMMIT,'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean#L87-L92'}

def stage_files():
    graph,closure,provided,rows,commands,pins=authority()
    module=next(m for m in read(AST)['modules'] if m['module']==TARGET_MODULE);unit=next(u for u in module['units'] if TARGET in u['graph_names']);port=base.source_path(TARGET_MODULE);raw=port.read_bytes();a,b=unit['start']['offset'],unit['end']['offset'];command=raw[a:b]
    need([a,b]==[4002,4395] and unit['privateTok'] is None and unit['graph_names']==[TARGET] and base.source_path(TARGET_MODULE,'source').read_bytes().replace(b'\r\n',b'\n').count(command.replace(b'\r\n',b'\n'))==1,'Exact target AST changed')
    ns,ne=unit['nameRange']['start']['offset']-a,unit['nameRange']['end']['offset']-a;vs=unit['valueStart']['offset']-a
    need(command[vs:vs+5]==b':= by','Target proof delimiter changed')
    preamble=(''.join('import '+x+'\n' for x in IMPORTS)+'\nopen OAI.PiExponent OAI.PiExponent.DeterminantContradiction\nopen Filter\nopen scoped Topology\n\n').encode()
    formal=command[:ns]+PLATFORM_NAME.encode()+command[ne:vs]+b':= by\n  sorry\n';target=preamble+formal
    parts=[(''.join('import '+x+'\n' for x in IMPORTS)+'\n').encode()]
    for m,selected in commands.items():
        header=base.GROUP_HEADERS[m]
        if m.endswith('SimplexCounting'):header+=b'open Filter Topology\n\n'
        parts+=[header]+[u+b'\n\n' for _,_,u in selected]+[base.GROUP_FOOTERS[m]]
    renamed=command[:ns]+b'solution'+command[ne:];need(renamed[renamed.find(b':= by'):]==command[vs:],'Literal target proof changed')
    parts+=[b'open OAI.PiExponent OAI.PiExponent.DeterminantContradiction\nopen Filter\nopen scoped Topology\n\n',renamed+b'\n']
    names=[r['name'] for r in rows];boundary=closure&provided
    generated={TARGET_OUTPUT:target,SOLUTION_OUTPUT:b''.join(parts),'wire-theorem-source.lean':target,'original-target-command.lean.txt':command,'academic-metadata.json':encode(metadata()),SOURCE_SNAPSHOT:snapshot('source',names+[TARGET],list(HELPER_NAMES),boundary),GENERATED_SNAPSHOT:snapshot('generated',names+['solution'],[SOLUTION_MODULE],boundary)}
    for _,selected in commands.items():
        for _,name,u in selected:generated['source-helpers/'+name.replace('.','_')+'.lean.txt']=u
    inputs={rel(p):sha(p) for p in [SELF,Path(base.__file__),AST,SCOPES,GRAPH,RUNTIME,SNAPSHOT_CORE,Path(base.runner.__file__),Path(base.ap8.__file__),Path(base.ap9.__file__),Path(base.ap10.__file__)]};inputs.update(pins)
    files={};compile_commands=[]
    for output,mode,mf,imports in zip(FILES,MODES,MANIFESTS,[IMPORTS,IMPORTS,['Lean',TARGET_MODULE],['Lean',SOLUTION_MODULE]],strict=True):
        files[output]={'sha256':sha_bytes(generated[output]),'mode':mode,'emit_olean':mode=='emit-olean','manifest':mf,'imports':imports}
        generated[mf]=encode({'schema_version':1,'artifact_kind':'ap12-actual-mean-bounds-bounded-compiler-manifest','output':workspace_rel(STAGE/output),'output_sha256':sha_bytes(generated[output]),'imports':imports,'input_hashes':inputs,'runtime_sha256':sha(RUNTIME),'mode':mode,'emit_olean':mode=='emit-olean','timeout_seconds':300,'validated':False,'submission_ready':False})
        compile_commands.append('python scripts/preflight_staged_module.py '+verification_rel(STAGE/output)+' --root ap12/mean-bounds --imports-manifest '+verification_rel(STAGE/mf)+' --timeout-seconds 300'+(' --emit-olean' if mode=='emit-olean' else ''))
    generated['preparation.json']=encode({'schema_version':1,'artifact_kind':'ap12-grouped-actual-mean-bounds-node-preparation','source_name':TARGET,'platform_name':PLATFORM_NAME,'source_module':TARGET_MODULE,'source_commit':COMMIT,'target_ast':unit,'target_source_command_sha256':sha_bytes(command),'target_proof_suffix_sha256':sha_bytes(command[vs:]),'target_original_command_equal_modulo_line_endings':True,'global_solution_preserves_literal_source_proof':True,'preamble':preamble.decode(),'formal_statement':formal.decode(),'graph_closure_names':sorted(closure),'provider_subtracted_names':sorted(boundary),'inline_helper_names':names,'inline_exact_source_units':rows,'source_type_only_names':names+[TARGET],'generated_type_only_names':names+['solution'],'source_theorem_values_null':True,'generated_theorem_values_null':True,'proof_reference_probe':'actual closed type/value refs, owners, Std3, all roots plus genuinely compiler-discovered same-owner automatic CI; no full theorem proof JSON','target_modecheck_only':True,'solution_module':SOLUTION_MODULE,'input_hashes':inputs,'files':files,'compile_commands':compile_commands,'metadata':metadata(),'names_need_root_authoritative_exact_lookup':True,'Lean_started':False,'API_used':False,'validated':False,'submission_ready':False,'proposal_status':'Draft'})
    generated['compile-commands.txt']=('\n'.join(compile_commands)+'\n').encode()
    return generated

def check_only():
    generated=stage_files()
    for filename,raw in generated.items():need((STAGE/filename).is_file() and (STAGE/filename).read_bytes()==raw,'Immutable stage differs: '+filename)
    for output,mf in zip(FILES,MANIFESTS,strict=True):
        m=read(STAGE/mf);base.runner.verify_manifest_inputs(m);base.runner.verify_source_certificate(STAGE/output,m)
    return {'checked_files':len(generated),'graph_closure_names':36,'inline_helpers':10,'all_hashes_match':True,'Lean_started':False,'API_used':False,'validated':False,'submission_ready':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);m=p.add_mutually_exclusive_group(required=True);m.add_argument('--prepare',action='store_true');m.add_argument('--check-only',action='store_true');a=p.parse_args()
    if a.prepare:
        for filename,raw in stage_files().items():
            path=STAGE/filename
            if path.exists():need(path.read_bytes()==raw,'Refusing overwrite: '+filename)
            else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(check_only(),ensure_ascii=False,indent=2))
if __name__=='__main__':main()
