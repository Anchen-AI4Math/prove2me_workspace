"""Rebind final current native sources without executing Lean or replacing old preparation."""
from pathlib import Path
import hashlib,json,sys,re
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/pi1';AUTHOR=TASK/'verification/formalization-coefficient-map-parameter-shift-2026-10-04'
SOURCE_SHA='5e472326fd47f4ad470cf89493fa75e57e22806cd1b1ac12697c878b06f69065'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def binding(p):return {'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
def main():
 assert not(PROJECT/'b').exists() and not(PROJECT/'.lake/build').exists()
 old=load(OUT/'preparation-state.json');rows=[]
 for r in old['source_bindings']:
  p=ROOT/r['root_relative']
  expected=SOURCE_SHA if p.name=='CoefficientMapParameterShift.lean' else r['sha256']
  assert sha(p)==expected
  write(PROJECT/r['root_relative'],p.read_bytes());rows.append(binding(p))
 assert len(rows)==14
 names={r['root_relative'].removesuffix('.lean').replace('/','.') for r in rows}
 for r in rows:
  imports=re.findall(r'^import (\S+)',(ROOT/r['root_relative']).read_text(encoding='utf-8-sig'),re.M)
  assert all(i.startswith('Mathlib.') or i in names for i in imports)
 lake=(PROJECT/'lakefile.lean').read_text(encoding='utf-8')
 assert 'globs := #[.one `missions.zeta9.formalization.CoefficientMapParameterShift]' in lake
 write(PROJECT/'lakefile.lean',lake.replace('globs := #[.one `missions.zeta9.formalization.CoefficientMapParameterShift]', 'globs := #[.submodules `missions.zeta9.formalization]'))
 controls=[]
 for name in ['source-full-audit.lean','expected-types.lean','independent-boundary.lean']:
  write(PROJECT/name,(OUT/name).read_bytes());controls.append(binding(OUT/name))
 write(PROJECT/'author-type-audit.lean',(AUTHOR/'type-audit.lean').read_bytes())
 runtime=[binding(ROOT/n) for n in ['lean-toolchain','lake-manifest.json']]
 for n in ['lean-toolchain','lake-manifest.json']:assert (PROJECT/n).read_bytes()==(ROOT/n).read_bytes()
 package=PROJECT/'.lake/packages';assert package.is_junction() and package.resolve()==(ROOT/'.lake/packages').resolve()
 guards=[{'root_relative':r['root_relative'],'object_path_plus64':len(str(PROJECT/'b/lib/lean'/r['root_relative'].removesuffix('.lean')))+len('.olean')+64} for r in rows]
 assert max(r['object_path_plus64'] for r in guards)<=259
 for filename in ['attempt-01/receipt.json','audit-01/receipt.json']:
  r=load(AUTHOR/filename);assert r['source_sha256']==SOURCE_SHA and r['actual_exit']==0
  assert sha(AUTHOR/r['log'])==r['log_sha256'] and sha(AUTHOR/r['exit_file'])==r['exit_sha256']
 report={'status':'FINAL_CURRENT_SOURCE_REBOUND_WAIT_AUTHOR_FREEZE','Lean_Lake_invocations':0,'source_sha256':SOURCE_SHA,
  'source_bindings':rows,'controls':controls,'runtime_bindings':runtime,'author_actual_receipts':[binding(AUTHOR/n) for n in ['attempt-01/receipt.json','audit-01/receipt.json']],
  'cache_absent':True,'old_dc6299_snapshot_and_pure_preparation_unchanged':True,'author_objects_borrowed':False,
  'only_Mathlib_package_cache_shared':True,'Root_API_credentials_writes':False,'path_guards':guards,'await_exact_parent_freeze':True}
 write(OUT/'final-preparation.json',json.dumps(report,ensure_ascii=False,indent=2)+'\n')
 print('Final source rebind',len(rows),'actual sources; cache absent; no Lean execution; SHA',sha(OUT/'final-preparation.json'))
if __name__=='__main__':main()
