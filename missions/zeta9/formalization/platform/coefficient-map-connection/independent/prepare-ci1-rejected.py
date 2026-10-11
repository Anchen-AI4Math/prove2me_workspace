"""Pure preparation for Connection transplant independent replay in ci1."""
from pathlib import Path
import hashlib,json,subprocess
OUT=Path(__file__).resolve().parent;AUTHOR=OUT.parent;TASK=OUT.parents[3];ROOT=TASK.parents[1];PROJECT=TASK/'.rt/ci1'
ASH='876033891293bc5fdf4f8846d26d099631a5124c6f6c245e5c1ad996bd8779e5'
RSH='4222330db9e0e92c0a992a6cbd406e03db8eb174f2429bcd74173f95e7a4e3de'
CSH='19dd8f1d73b41cb10c1d85c9822ad80deb5082c0c721158488684a48d1a18d66'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(s if isinstance(s,bytes) else s.encode('utf-8'))
def bind(p):return {'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
def verify(rows,base):
 for r in rows:
  p=base/r.get('root_relative',r.get('task_relative',''));assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
assert not PROJECT.exists()
assert sha(AUTHOR/'author-audit.json')==ASH and sha(AUTHOR/'root-copy-plan.json')==CSH
a=load(AUTHOR/'author-audit.json');assert a['verdict']=='PASS' and len(a['checks'])==33 and len(a['stable_files'])==372
verify(a['stable_files'],TASK)
rpath=TASK/'verification/formalization-coefficient-map-connection-root-preflight-2026-10-04/root-build-freeze.json'
assert sha(rpath)==RSH;r=load(rpath);assert r['root_actual_build_exit']==0 and r['root_actual_build_jobs']==3824 and len(r['stable_files'])==5
verify(r['stable_files'],TASK)
for f in load(AUTHOR/'root-copy-plan.json')['files']:
 p=TASK/f['staged_task_relative'];q=ROOT/f['root_relative_destination'];assert sha(p)==sha(q)==f['sha256'] and p.read_bytes()==q.read_bytes()
native_review=TASK/'verification/formalization-coefficient-map-connection-independent-2026-10-04/independent-review.json'
assert sha(native_review)=='92940f9b02161210e55af39c625e0cd233eaf7a5bf9d5c1aa2238f0506e28d82'
nr=load(native_review);assert nr['verdict']=='PASS' and len(nr['stable_files'])==108
verify(nr['stable_files'],ROOT)
write(PROJECT/'lakefile.lean',(TASK/'.rt/ca1/lakefile.lean').read_bytes().replace(b'zeta9ConnectionPlatformAuthor',b'zeta9ConnectionPlatformIndependent'))
for n in ['lean-toolchain','lake-manifest.json']:write(PROJECT/n,(ROOT/n).read_bytes())
packages=PROJECT/'.lake/packages';packages.parent.mkdir(parents=True,exist_ok=True)
j=subprocess.run(['powershell','-NoProfile','-Command',f"New-Item -ItemType Junction -Path '{packages}' -Target '{ROOT/'.lake/packages'}' | Out-Null"],capture_output=True)
write(OUT/'junction.log',j.stdout+j.stderr);write(OUT/'junction-exit.txt',str(j.returncode)+'\n');assert j.returncode==0
assert packages.is_junction() and packages.resolve()==(ROOT/'.lake/packages').resolve()
source=TASK/'formalization/CoefficientMapConnection.lean';assert sha(source)==a['source_sha256']=='098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8'
write(PROJECT/'missions/zeta9/formalization'/source.name,source.read_bytes())
for p in AUTHOR.glob('*.lean'):
 write(OUT/p.name,p.read_bytes());write(PROJECT/p.name,p.read_bytes())
for n in ['embed_definition_fields.py','target-plan.json','integration-provenance.json','embedded-field-provenance.json','definitions-request.json','problems-request.json','root-copy-plan.json']:
 write(OUT/n,(AUTHOR/n).read_bytes())
for p in (AUTHOR/'staged').rglob('*.lean'):
 rel=p.relative_to(AUTHOR/'staged');write(OUT/'staged'/rel,p.read_bytes());write(PROJECT/rel,p.read_bytes())
driver=(AUTHOR/'author_driver.py').read_text(encoding='utf-8-sig')
driver=driver.replace("TASK = OUT.parents[2]","TASK = OUT.parents[3]").replace("PROJECT = TASK/'.rt/ca1'","PROJECT = TASK/'.rt/ci1'")
start=driver.index('def preconditions():');end=driver.index('\ndef configure():',start)
driver=driver[:start]+'''def preconditions():
    gate = load(OUT/'frozen-handoff.json')
    assert gate['explicit_parent_lane1_authorized']
    parent=OUT.parent
    assert sha(parent/'author-audit.json') == gate['author_sha256']
    for r in load(parent/'author-audit.json')['stable_files']:
        p=TASK/r['task_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
    rootfreeze=TASK/gate['Root_freeze']['task_relative']
    assert sha(rootfreeze)==gate['Root_freeze']['sha256']
    for r in load(rootfreeze)['stable_files']:
        p=TASK/r['task_relative'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
    assert sha(TASK/'formalization/CoefficientMapConnection.lean')==SOURCE_SHA
    assert sha(PROJECT/(NATIVE.replace('.','/')+'.lean'))==SOURCE_SHA
    assert (PROJECT/'.lake/packages').is_junction()
    assert (PROJECT/'.lake/packages').resolve()==(ROOT/'.lake/packages').resolve()
''' +driver[end:]
driver=driver.replace("role='platform author actual executions'","role='independent platform replay actual executions'")
# The actual environment wrapper has no fixed ca1 paths, only its own parent.
write(PROJECT/'lean_call.py',(TASK/'.rt/ca1/lean_call.py').read_bytes())
write(OUT/'review_driver.py',driver)
state={'status':'PURE_PREPARATION_COMPLETE','explicit_parent_lane1_authorized':True,'author_sha256':ASH,'copyplan_sha256':CSH,
 'Root_freeze':{'task_relative':rpath.relative_to(TASK).as_posix(),'sha256':RSH},'Root5':r['stable_files'],
 'native_review':bind(native_review),'native_source':bind(source),'cache_initially_absent':not(PROJECT/'b').exists(),
 'native_and_staged_objects_borrowed':False,'Root_API_credentials_scope_writes':False,'Lean_invocations':0,
 'author_bindings_verified':372,'Root_bindings_verified':5,'native_bindings_verified':108,
 'root_scope_check1_only_preexisting_other_task_errors':r['scope_check_only_preexisting_other_task_errors']}
write(OUT/'frozen-handoff.json',json.dumps(state,ensure_ascii=False,indent=2)+'\n')
assert state['cache_initially_absent']
print('Exact author372, Root5/7installed, native108 verified; independent empty ci1 ready; Lean0')
