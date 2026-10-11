"""Replay the fixed 35 native author and 54 independent records against staged Sol."""
from pathlib import Path
import hashlib,json,os,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[2];ROOT=TASK.parents[1];PROJECT=OUT/'p'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mathfile=TASK/'verification/formalization-coefficient-map-telescoper-independent-2026-10-04/independent-review.json'
assert sha(mathfile)=='cac46e0ea0674bcd4b2dca543326ab2d9bdd3cd8a409cba8988bfea0130a556a'
math=json.loads(mathfile.read_text(encoding='utf-8'))
bound={r['root_relative']:r['sha256'] for r in math['stable_files']}
env=os.environ.copy();env.pop('LEAN_PATH',None)
selected='actual_polynomial_quotient_degree_bound'; replacement='checked_'+selected
inputs=[('stage-native-author-audit','verification/formalization-coefficient-map-telescoper-2026-10-04/type-audit.lean',35),
        ('stage-independent-boundary-audit','verification/formalization-coefficient-map-telescoper-independent-2026-10-04/independent-boundary.lean',54)]
reports=[]
for label,rel,count in inputs:
 original=TASK/rel;assert sha(original)==bound[original.relative_to(ROOT).as_posix()]
 s=original.read_text(encoding='utf-8-sig')
 oldimport='import missions.zeta9.formalization.CoefficientMapTelescoper'
 newimport='import Solutions.Sol_ZetaNine_CoefficientMapTelescoper_'+selected
 assert s.count(oldimport)==1
 s=s.replace(selected,replacement).replace(oldimport,newimport)
 for p in [OUT/(label+'.lean'),PROJECT/(label+'.lean')]:p.write_text(s,encoding='utf-8',newline='\n')
 provenance={'native_source_task_relative':rel,'native_source_sha256':sha(original),'expected_records':count,
  'changes':'Only actual complete staged Solution import and selected quotient-degree theorem name; original statements and proofs retained.',
  'extra_hypotheses':[],'root_scope_API_credential_writes':False}
 (OUT/(label+'-provenance.json')).write_text(json.dumps(provenance,indent=2)+'\n',encoding='utf-8')
 p=subprocess.run(['lake','env','lean',label+'.lean'],cwd=PROJECT,env=env,capture_output=True)
 log=OUT/(label+'.log');log.write_bytes(p.stdout+p.stderr)
 (OUT/(label+'-exit.txt')).write_text(str(p.returncode)+'\n',encoding='utf-8')
 rs=[json.loads(l) for l in p.stdout.decode('utf-8-sig').splitlines() if l.startswith('{')]
 report={'label':label,'exit_code':p.returncode,'records':rs,'expected_records':count,'log_sha256':sha(log),
  'all_standard_axioms':all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in rs)}
 (OUT/(label+'-report.json')).write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
 print(json.dumps({'label':label,'exit_code':p.returncode,'records':len(rs)}),flush=True)
 if p.returncode:print((p.stdout+p.stderr).decode('utf-8-sig'),flush=True)
 assert p.returncode==0 and len(rs)==count and report['all_standard_axioms']
 reports.append(report)
(OUT/'stage-boundary-report.json').write_text(json.dumps({'runs':reports,'all_zero':True,'records':89},ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
