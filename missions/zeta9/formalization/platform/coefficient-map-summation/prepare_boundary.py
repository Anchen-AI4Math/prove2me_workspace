"""Actual old boundary statements replayed against the complete new staged Solution."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent; TASK=OUT.parents[2]; PROJECT=OUT/'project'
original=TASK/'verification/formalization-coefficient-map-summation-independent-2026-10-04/independent-boundary-audit.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
s=original.read_text(encoding='utf-8-sig')
review=TASK/'verification/formalization-coefficient-map-summation-independent-2026-10-04/independent-review.json'
assert sha(review)=='fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa'
bound=json.loads(review.read_text(encoding='utf-8'))['stable_files']
assert sha(original)==next(r['sha256'] for r in bound if r['root_relative']==original.relative_to(TASK.parents[1]).as_posix())
old='actualSeries_hasSum_exactL'; new='checked_'+old
s=s.replace('import missions.zeta9.formalization.CoefficientMapSummation','import Solutions.Sol_ZetaNine_CoefficientMapSummation_actualSeries_hasSum_exactL')
s=s.replace(old,new).replace('Sol_ZetaNine_CoefficientMapSummation_'+new,'Sol_ZetaNine_CoefficientMapSummation_'+old)
for p in [OUT/'stage-boundary-audit.lean',PROJECT/'stage-boundary-audit.lean']:p.write_text(s,encoding='utf-8',newline='\n')
provenance={'native_boundary_source':original.relative_to(TASK).as_posix(),'native_boundary_source_sha256':sha(original),
 'native_review_sha256':'fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa',
 'changes':'Only full staged Solution import and selected HasSum theorem name; original boundary statements/proofs unchanged.',
 'extra_hypotheses':[],'API_calls':False,'root_scope_writes':False}
(OUT/'stage-boundary-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n',encoding='utf-8')
env=os.environ.copy();env.pop('LEAN_PATH',None)
p=subprocess.run(['lake','env','lean','stage-boundary-audit.lean'],cwd=PROJECT,env=env,capture_output=True)
(OUT/'stage-boundary-audit.log').write_bytes(p.stdout+p.stderr)
(OUT/'stage-boundary-audit-exit.txt').write_text(str(p.returncode)+'\n',encoding='utf-8')
rs=[json.loads(l) for l in p.stdout.decode('utf-8-sig').splitlines() if l.startswith('{')]
(OUT/'stage-boundary-report.json').write_text(json.dumps({'exit_code':p.returncode,'records':rs,
 'all_standard_axioms':all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in rs),
 'log_sha256':sha(OUT/'stage-boundary-audit.log')},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'boundary_exit':p.returncode,'records':len(rs)}),flush=True)
if p.returncode:print((p.stdout+p.stderr).decode('utf-8-sig'),flush=True)
assert p.returncode==0
