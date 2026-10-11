"""Independent clean-object replay of actual Injectivity platform sources."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
HERE=Path(__file__).resolve().parent; BATCH=HERE.parent; TASK=BATCH.parents[2]; ROOT=TASK.parents[1]
PROJECT=HERE/'project'
PIN='0df444a360eaa60ab8c11dca51a86af692955474'
EXPECTED={'CoefficientMap':'e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03','CoefficientMapJet':'e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a','CoefficientMapInjectivity':'ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095'}
NS='ZetaNine.CoefficientMapInjectivity'
TARGETS=['all_local_coefficients_zero_implies_zero','fullLocalCoefficientMap_injective','quartic_is_proper']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):
    p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def rows(p):return [json.loads(s) for s in p.read_text(encoding='utf-8-sig').splitlines() if s.startswith('{')]
assert not (PROJECT/'.lake/build').exists(),'Fresh project must start without native/staged objects'
for n,h in EXPECTED.items():assert sha(TASK/f'formalization/{n}.lean')==h
write(PROJECT/'lakefile.lean',f'''import Lake
open Lake DSL
package zeta9InjectivityTransplantIndependent
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "{PIN}"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapInjectivity]
  globs := #[.one `missions.zeta9.formalization.CoefficientMap, .one `missions.zeta9.formalization.CoefficientMapJet, .one `missions.zeta9.formalization.CoefficientMapInjectivity]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
''')
for n in ['lake-manifest.json','lean-toolchain']:write(PROJECT/n,(ROOT/n).read_bytes())
(PROJECT/'.lake').mkdir(exist_ok=True)
p=subprocess.run(['cmd','/c','mklink','/J',str(PROJECT/'.lake/packages'),str(ROOT/'.lake/packages')],capture_output=True)
assert p.returncode==0,(p.stdout+p.stderr).decode(errors='replace')
for n in EXPECTED:write(PROJECT/f'missions/zeta9/formalization/{n}.lean',(TASK/f'formalization/{n}.lean').read_bytes())
plan=load(BATCH/'root-copy-plan.json')
for f in plan['required_existing_Definitions']:
    write(PROJECT/f['root_relative'],(TASK/f['task_relative']).read_bytes());assert sha(PROJECT/f['root_relative'])==f['sha256']
for f in plan['files']:
    write(PROJECT/f['root_relative_destination'],(TASK/f['staged_task_relative']).read_bytes());assert sha(PROJECT/f['root_relative_destination'])==f['sha256']
# Only wrapper copies are made; official parser/metaprogram bodies are unchanged.
for name in ['extract_decl_graph.lean','extract_header.lean']+[f'extract_{n}_sketch.lean' for n in EXPECTED]:
    code=(BATCH/name).read_bytes();write(PROJECT/name,code)
env=os.environ.copy();env.pop('LEAN_PATH',None)
receipt={'source_sha256':EXPECTED,'mathlib_rev':PIN,'fresh_project_without_objects_at_start':True,'native_or_staged_olean_borrowed':False,'root_writes':False,'API_called':False,'rows':[]}
def run(label,args,stdout_file=None):
    p=subprocess.run(args,cwd=PROJECT,env=env,capture_output=True)
    log=HERE/(label+'.log');write(log,p.stdout+p.stderr);write(HERE/(label+'-exit.txt'),str(p.returncode)+'\n')
    if stdout_file:write(HERE/stdout_file,p.stdout);write(HERE/(label+'-stderr.log'),p.stderr)
    receipt['rows'].append({'label':label,'command':args,'working_directory':str(PROJECT),'exit_code':p.returncode,'log':log.name,'log_sha256':sha(log)})
    write(HERE/'compile-receipt.json',json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
    print(label+': exit '+str(p.returncode),flush=True)
    for n,h in EXPECTED.items():assert sha(TASK/f'formalization/{n}.lean')==h
    if p.returncode:print(log.read_text(encoding='utf-8-sig'),flush=True)
    assert p.returncode==0
run('toolchain',['lake','env','lean','--version'])
for n in EXPECTED:run('build-native-'+n,['lake','--no-cache','build','missions.zeta9.formalization.'+n])
run('stage1-extract',['lake','env','lean','extract_decl_graph.lean'])
for n in EXPECTED:
    dest='sketch_info.jsonl' if n.endswith('Injectivity') else n+'-sketch_info.jsonl'
    run('stage2-'+n,['lake','env','lean','--run','extract_'+n+'_sketch.lean','missions/zeta9/formalization/'+n+'.lean','ZetaNine'],dest)
run('stage2-header',['lake','env','lean','--run','extract_header.lean','missions/zeta9/formalization/CoefficientMapInjectivity.lean'],'header_info.jsonl')
for i,f in enumerate(plan['required_existing_Definitions']):run('build-dependency-Def-'+str(i),['lake','--no-cache','build',f['root_relative'].removesuffix('.lean').replace('/','.')])
for i,f in enumerate(plan['files']):run('build-staged-'+str(i),['lake','--no-cache','build',f['root_relative_destination'].removesuffix('.lean').replace('/','.')])
graph=rows(HERE/'decl_graph.jsonl')
byname={g['name']:g for g in graph}
core=[g for g in graph if g['module'].endswith('.CoefficientMapInjectivity') and g['startLine']>0]
reached=set();work=[g['name'] for g in core]+[g['name'] for g in graph if g['isInstance']]
while work:
    n=work.pop()
    if n in reached:continue
    reached.add(n);work.extend(byname[n]['typeDeps']+byname[n]['valueDeps'])
helpers=sorted([byname[n] for n in reached if not byname[n]['module'].endswith('.CoefficientMapInjectivity') and byname[n]['kind']=='theorem' and byname[n]['startLine']>0],key=lambda g:(g['module'],g['startLine']))
defs=[g['name'] for g in graph if g['kind']=='def' and g['startLine']>0]
assert len(defs)==25 and len(core)==25 and len(helpers)==7
REPORT='''import MODULE
import Lean
open Lean
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  let emit (label : String) (name : Name) : Lean.Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← Lean.Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo d => pure (some (← Lean.Meta.ppExpr d.value).pretty)
      | _ => pure none
    let axioms ← Lean.collectAxioms name
    IO.println (Json.mkObj [("label", Json.str label), ("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("value", toJson value), ("axioms", toJson (axioms.toList.map Name.toString))]).compress
'''
def report(label,module,bindings):
    write(PROJECT/(label+'.lean'),REPORT.replace('MODULE',module)+''.join(f'  emit "{l}" `{n}\n' for l,n in bindings));run(label,['lake','env','lean',label+'.lean'])
report('types_original','missions.zeta9.formalization.CoefficientMapInjectivity',[(n,n) for n in defs+[NS+'.'+t for t in TARGETS]])
report('types_definition','Definitions.Def_ZetaNine_CoefficientMapInjectivity',[(n,n) for n in defs])
for i,t in enumerate(TARGETS):
    for kind,prefix,n in [('solution','Solutions.Sol_','solution'),('reference','Theorems.Thm_',NS+'.'+t)]:
        report(f'types_{i}_{kind}',prefix+'ZetaNine_CoefficientMapInjectivity_'+t,[(n,n) for n in defs]+[(NS+'.'+t,n)])
    names=[g['name'] for g in core if g['kind']=='theorem']+[g['name'] for g in helpers]+['solution']
    names=[NS+'.checked_'+t if n==NS+'.'+t else n for n in names]
    report('helpers_'+str(i),'Solutions.Sol_ZetaNine_CoefficientMapInjectivity_'+t,[(n,n) for n in names])
receipt['complete']=True;receipt['actual_successful_runs']=len(receipt['rows'])
write(HERE/'compile-receipt.json',json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
print('Independent native, nine Def/Sol/reference modules, oracle, eight type/value and three helper replays complete.',flush=True)
