from pathlib import Path
import hashlib,json,os,re,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parent.parent;P=OUT/'p'
SOURCE=TASK/'formalization/CoefficientMapConnection.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
receipt=json.loads((OUT/'compile-receipt.json').read_text())
last=receipt['rows'][-1];assert last['exit_code']==0 and last['source_sha256']==sha(SOURCE)
assert sha(OUT/last['object'])==last['object_sha256']
names=re.findall(r'^(def|theorem)\s+(\w+)',SOURCE.read_text(encoding='utf-8'),re.M)
code='''import missions.zeta9.formalization.CoefficientMapConnection
import Lean
open Lean
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true
run_meta do
  let emit (name : Name) : Lean.Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← Lean.Meta.ppExpr ci.type
    let (kind, val, raw) ← match ci with
      | .defnInfo d => pure ("def", some (← Lean.Meta.ppExpr d.value).pretty, some (reprStr d.value))
      | .thmInfo _ => pure ("theorem", none, none)
      | _ => pure ("other", none, none)
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("kind",Json.str kind),
      ("type",Json.str typ.pretty),("type_expression_repr",Json.str (reprStr ci.type)),
      ("value",toJson val),("definition_expression_repr",toJson raw),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
'''
code+=''.join('  emit `ZetaNine.CoefficientMapConnection.'+n+'\n' for kind,n in names)
write(OUT/'type-audit.lean',code)
rp=OUT/'type-audit-receipt.json'
r=json.loads(rp.read_text()) if rp.exists() else {'source_sha256':sha(SOURCE),'rows':[],'complete':False}
env=os.environ.copy();env.pop('LEAN_PATH',None);env['LEAN_NUM_THREADS']='1'
labels=sys.argv[1:] or ['type-audit','boundary-audit']
assert all(label in ['type-audit','boundary-audit'] for label in labels)
for label in labels:
 src=OUT/(label+'.lean');write(P/src.name,src.read_bytes())
 attempt=1+sum(x['label']==label for x in r['rows'])
 dest=OUT/f'{label}-attempt-{attempt:02}'
 write(dest/src.name,src.read_bytes())
 cmd=['lake','env','lean',src.name]
 rr=subprocess.run(cmd,cwd=P,env=env,capture_output=True)
 write(dest/'compile.log',rr.stdout+rr.stderr);write(dest/'exit.txt',str(rr.returncode)+'\n')
 row={'label':label,'attempt':attempt,'command':cmd,'exit_code':rr.returncode,'source':str((dest/src.name).relative_to(OUT)),'source_sha256':sha(src),'log':str((dest/'compile.log').relative_to(OUT)),'log_sha256':sha(dest/'compile.log'),'exit_file':str((dest/'exit.txt').relative_to(OUT)),'exit_sha256':sha(dest/'exit.txt'),'native_source_sha256':sha(SOURCE),'native_object_sha256':last['object_sha256']}
 r['rows'].append(row);write(rp,json.dumps(r,indent=2)+'\n')
 print(label+': actual exit '+str(rr.returncode),flush=True)
 if rr.returncode:
  print('\n'.join(x for x in (rr.stdout+rr.stderr).decode('utf-8',errors='replace').splitlines() if not x.startswith('{')),flush=True)
  sys.exit(rr.returncode)
 rows=[json.loads(x) for x in rr.stdout.decode('utf-8').splitlines() if x.startswith('{')]
 assert rows and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in rows)
 assert len(rows)==len(names) if label=='type-audit' else len(rows)==12
 write(OUT/(label+'.json'),json.dumps({'source_sha256':sha(SOURCE),'actual_exit_code':0,'records':rows},ensure_ascii=False,indent=2)+'\n')
 print(str(len(rows))+' records; standard axioms only',flush=True)
r['complete']=all(any(x['label']==label and x['exit_code']==0 for x in r['rows']) for label in ['type-audit','boundary-audit']);write(rp,json.dumps(r,indent=2)+'\n')
