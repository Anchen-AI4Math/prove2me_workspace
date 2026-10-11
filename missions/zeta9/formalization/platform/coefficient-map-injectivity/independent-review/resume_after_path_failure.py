"""Resume at failed Solution output only; preserve every successful prior run."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
HERE=Path(__file__).resolve().parent;BATCH=HERE.parent;TASK=BATCH.parents[2];PROJECT=HERE/'project'
NS='ZetaNine.CoefficientMapInjectivity'
TARGETS=['all_local_coefficients_zero_implies_zero','fullLocalCoefficientMap_injective','quartic_is_proper']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def rows(p):return [json.loads(s) for s in p.read_text(encoding='utf-8-sig').splitlines() if s.startswith('{')]
def write(p,s):
    p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
receipt=load(HERE/'compile-receipt.json')
assert len(receipt['rows'])==13 and receipt['rows'][-1]['label']=='build-staged-1' and receipt['rows'][-1]['exit_code']==1
assert all(r['exit_code']==0 for r in receipt['rows'][:-1])
failure=(HERE/'build-staged-1.log').read_text(encoding='utf-8-sig')
assert "'solution' depends on axioms: [propext, Classical.choice, Quot.sound]" in failure and 'failed to create file' in failure
for r in receipt['rows']:assert sha(HERE/r['log'])==r['log_sha256']
plan=load(BATCH/'root-copy-plan.json')
env=os.environ.copy();env.pop('LEAN_PATH',None)
def run(label,args):
    p=subprocess.run(args,cwd=PROJECT,env=env,capture_output=True)
    log=HERE/(label+'.log');write(log,p.stdout+p.stderr);write(HERE/(label+'-exit.txt'),str(p.returncode)+'\n')
    receipt['rows'].append({'label':label,'command':args,'working_directory':str(PROJECT),'exit_code':p.returncode,'log':log.name,'log_sha256':sha(log)})
    write(HERE/'compile-receipt.json',json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
    print(label+': exit '+str(p.returncode),flush=True)
    for n,h in receipt['source_sha256'].items():assert sha(TASK/f'formalization/{n}.lean')==h
    if p.returncode:print(log.read_text(encoding='utf-8-sig'),flush=True)
    assert p.returncode==0
objects=HERE/'objects';objects.mkdir(exist_ok=True)
object_copies=[]
for i,f in enumerate(plan['files'][1:],start=1):
    temporary=objects/('stage_'+str(i)+'.olean')
    # Short output avoids Lean's temporary-file expansion at the Windows limit.
    # The exact frozen source, existing independently compiled Definitions and
    # own fresh native objects are retained without rebuilding successes.
    run('build-staged-'+str(i)+'-short-output',['lake','env','lean',f['root_relative_destination'],'-o',str(temporary)])
    destination=PROJECT/'.lake/build/lib/lean'/Path(f['root_relative_destination']).with_suffix('.olean')
    for p in sorted(objects.glob('stage_'+str(i)+'.olean*')):
        suffix=p.name.removeprefix('stage_'+str(i)+'.olean')
        target=Path(str(destination)+suffix);write(target,p.read_bytes())
        assert sha(target)==sha(p)
        object_copies.append({'source':p.relative_to(HERE).as_posix(),'destination':target.relative_to(PROJECT).as_posix(),'sha256':sha(target),'only_independent_project_written':True})
    assert destination.exists()
graph=rows(HERE/'decl_graph.jsonl');byname={g['name']:g for g in graph}
core=[g for g in graph if g['module'].endswith('.CoefficientMapInjectivity') and g['startLine']>0]
found=set();work=[g['name'] for g in core]+[g['name'] for g in graph if g['isInstance']]
while work:
    n=work.pop()
    if n in found:continue
    found.add(n);work.extend(byname[n]['typeDeps']+byname[n]['valueDeps'])
helpers=sorted([byname[n] for n in found if not byname[n]['module'].endswith('.CoefficientMapInjectivity') and byname[n]['kind']=='theorem' and byname[n]['startLine']>0],key=lambda g:(g['module'],g['startLine']))
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
receipt['complete']=True
receipt['actual_successful_runs']=sum(r['exit_code']==0 for r in receipt['rows'])
receipt['retained_failed_attempts']=[{'label':'build-staged-1','exit_code':1,'evidence':'build-staged-1.log','reason':'Lean elaborated and printed standard axioms, then failed writing the long Windows output path; short independent outputs succeeded','final_repair':'six remaining exact staged modules compiled via lake env lean with short temporary output, newly generated own objects copied into this independent cache'}]
receipt['independent_object_copies']=object_copies
write(HERE/'compile-receipt.json',json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
print('Resumed replay complete: '+str(receipt['actual_successful_runs'])+' actual successful runs; initial output-path failure preserved.',flush=True)
