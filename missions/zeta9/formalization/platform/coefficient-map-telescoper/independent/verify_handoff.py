"""Read-only future freeze/root gate. Does not invoke Lean or create proof objects."""
from pathlib import Path
import hashlib,json,re
OUT=Path(__file__).resolve().parent;BATCH=OUT.parent;TASK=OUT.parents[3];ROOT=TASK.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def verify():
 handoff_file=OUT/'frozen-handoff.json'
 assert handoff_file.exists(), 'Await explicit parent frozen author controls and completed Root evidence'
 handoff=load(handoff_file)
 assert handoff['status']=='PARENT_FROZEN_AUTHOR_AND_ROOT_HANDOFF'
 controls=handoff['author_controls'];root_hashes=handoff['root_evidence_sha256']
 assert set(controls)=={'author-audit.json','root-copy-plan.json','source-manifest.json','SHA256SUMS.txt'}
 assert set(root_hashes)=={'root-install-receipt.json','task-build.log','task-build-exit.txt','task-check.log','task-check-exit.txt'}
 for n,h in {**controls,**root_hashes}.items():assert re.fullmatch('[0-9a-f]{64}',h) and sha(BATCH/n)==h
 author=load(BATCH/'author-audit.json');assert author['verdict']=='PASS' and all(c['pass'] for c in author['checks'])
 enrollment=load(OUT/'preparation-enrollment.json')
 for m,h in enrollment['original_source_hashes'].items():assert sha(TASK/'formalization'/(m+'.lean'))==h
 for r in enrollment['source_bindings']:
  p=OUT/'p'/r['project_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'] and p.read_bytes()==(ROOT/r['original_root_relative']).read_bytes()
 for r in load(BATCH/'source-manifest.json')['files']:
  p=TASK/r['task_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
 for line in (BATCH/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
  h,rel=line.split('  ',1);assert sha(BATCH/rel)==h
 plan=load(BATCH/'root-copy-plan.json');assert len(plan['files'])==7 and len(plan['required_existing_Definitions'])==9
 for r in plan['files']:
  root=ROOT/r['root_relative_destination'];stage=TASK/r['staged_task_relative'];assert sha(root)==r['sha256'] and root.read_bytes()==stage.read_bytes() and root.stat().st_size==r['bytes']
 for r in plan['required_existing_Definitions']:
  assert sha(ROOT/r['root_relative'])==r['sha256'] and (ROOT/r['root_relative']).read_bytes()==(TASK/r['task_relative']).read_bytes()
 assert (BATCH/'task-build-exit.txt').read_text().strip()=='0'
 log=(BATCH/'task-build.log').read_text(encoding='utf-8-sig');jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)\.',log).group(1));assert jobs==handoff['observed_build_jobs']
 issues=[s for s in (BATCH/'task-check.log').read_text(encoding='utf-8-sig').splitlines() if s.strip()]
 assert (BATCH/'task-check-exit.txt').read_text().strip()=='1' and len(issues)==2 and all('Sol_TaoFivePrimes_' in s and 'Unassigned solution' in s for s in issues)
 scope=load(TASK/'scope.json')
 for n in enrollment['targets']:assert 'Solutions/Sol_ZetaNine_CoefficientMapTelescoper_'+n+'.lean' in scope['build']
 return handoff
if __name__=='__main__':
 h=verify();print('Frozen author and Root handoff verified; this gate runs no Lean and claims no independent PASS.')
