"""Reuse exact same-author PS parent objects in a separate task-only project."""
from pathlib import Path
import hashlib,json,subprocess
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1];ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/ft1';PARENT=TASK/'.rt/ps1'
AUTHOR=TASK/'verification/formalization-coefficient-map-parameter-shift-2026-10-04'
AUTHOR_SHA='4a8dbe4ff74047e223054a4b14ca034ca73c900513ed205dcdd8ff91bd670642'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def bind(p):return {'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
assert not PROJECT.exists()
assert sha(AUTHOR/'author-audit.json')==AUTHOR_SHA
a=load(AUTHOR/'author-audit.json');assert a['verdict']=='PASS' and len(a['stable_files'])==59
for r in a['stable_files']:
 p=ROOT/r['root_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
design=TASK/'verification/coefficient-map-formal-transport-design-2026-10-04/design-freeze.json'
d=load(design)
for r in d['files']:
 p=TASK/r['task_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
assert sha(TASK/'formalization/CoefficientMapFormalTransportData.lean')=='ae9f4eab8efecd88aaae5d4b13da7ba4bed7db89bbf257d3b0645e1b8584fb27'
first=load(AUTHOR/'first-build-receipt.json');assert len(first['rows'])==14 and all(r['actual_exit']==0 for r in first['rows'][:13])
last=load(AUTHOR/'attempt-01/receipt.json');assert last['actual_exit']==0 and last['source_sha256']==a['source_sha256']
write(PROJECT/'lakefile.lean','import Lake\nopen Lake DSL\npackage zeta9FormalTransportAuthor where\n  buildDir := "b"\nrequire mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"\nlean_lib Native where\n  globs := #[.submodules `missions.zeta9.formalization]\nlean_lib Definitions\n')
for name in ['lean-toolchain','lake-manifest.json']:write(PROJECT/name,(ROOT/name).read_bytes())
packages=PROJECT/'.lake/packages';packages.parent.mkdir(parents=True,exist_ok=True)
cmd=['powershell','-NoProfile','-Command',f"New-Item -ItemType Junction -Path '{packages}' -Target '{ROOT/'.lake/packages'}' | Out-Null"]
result=subprocess.run(cmd,capture_output=True);write(OUT/'junction.log',result.stdout+result.stderr);write(OUT/'junction-exit.txt',str(result.returncode)+'\n');assert result.returncode==0
assert packages.is_junction() and packages.resolve()==(ROOT/'.lake/packages').resolve()
bindings=[];copies=[];modules=[]
for r in load(AUTHOR/'preparation-state.json')['sources']:
 p=ROOT/r['root_relative'];q=PARENT/r['project_relative'];assert p.read_bytes()==q.read_bytes()
 write(PROJECT/r['project_relative'],p.read_bytes());bindings.append(bind(p));copies.append(bind(PROJECT/r['project_relative']))
 module=r['project_relative'][:-5].replace('/','.');modules.append(module)
 base=PARENT/'b/lib/lean'/r['project_relative'][:-5]
 for extension in ['.olean','.ilean']:
  obj=base.with_suffix(extension);assert obj.is_file()
  destination=PROJECT/'b/lib/lean'/obj.relative_to(PARENT/'b/lib/lean')
  write(destination,obj.read_bytes());bindings.append(bind(obj));copies.append(bind(destination))
  if extension=='.olean' and module.endswith('CoefficientMapParameterShift'):assert sha(obj)==last['retained_object_sha256']
for name in ['CoefficientMapFormalTransportData','CoefficientMapFormalTransportBounds']:
 p=TASK/'formalization'/(name+'.lean');write(PROJECT/'missions/zeta9/formalization'/p.name,p.read_bytes())
assert len(modules)==14 and not any('Matrix' in m for m in modules)
state={'status':'SAME_AUTHOR_PARENT_OBJECTS_REUSED_NEW_MODULES_NOT_YET_COMPILED','author_report_sha256':AUTHOR_SHA,
 'design_freeze':bind(design),'frozen_data_sha256':sha(TASK/'formalization/CoefficientMapFormalTransportData.lean'),
 'parent_source_and_objects':bindings,'new_project_copies':copies,'parent_modules':modules,
 'pinned_runtime':[bind(ROOT/'lean-toolchain'),bind(ROOT/'lake-manifest.json')],
 'parent_cache_reused':True,'fresh_parent_build_claimed':False,'independent_objects_borrowed':False,'parent_or_Root_written':False,
 'new_project':str(PROJECT),'scope':'Only actual Data and chosen witness/Gamma restoration/proper numerator/zeros bridge, not universal PF/five-output/HasSum transport'}
write(OUT/'preparation-state.json',json.dumps(state,indent=2)+'\n')
print('Bound14 same-author parent source/object pairs; frozen Data unchanged; Lean invocations0')
