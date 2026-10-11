"""Finish the authorized KernelBridge author lane after its main driver ends."""
from pathlib import Path
import json,subprocess,sys
sys.stdout.reconfigure(encoding='utf-8')
p=Path(__file__).resolve().parent
r=json.loads((p/'compile-receipt.json').read_text(encoding='utf-8-sig'))
assert r.get('complete') and len(r['rows'])==47 and all(x['exit_code']==0 for x in r['rows']), 'Main47 must actually complete before this serial continuation'
steps=[('aggregate-full-value-replay','prepare_data_equivalence.py',['--alias-source-task-relative','formalization/platform/coefficient-map-aggregate/native-value-comparison-definition.lean','--alias-source-sha256','4187ed313d634e9a85f284f67835d63f4543487eee01e359dbc3f68adeda0fc8','--alias-namespace','ZetaNine.CoefficientMapAggregateValueComparison','--aggregate-author-audit-sha256','f7062cfecbbe14e5d36e69165e159630f4e090bbe1989b5d79ddc9bae2435ddf','--aggregate-SHA256SUMS-sha256','43cdcb1650722dd4ceb92d068e4ff23b9d7b59f707fe0901028f6e7a59796c83']),('kernel-full-value-replay','prepare_kernel_data_equivalence.py',[]),('original-boundary-replay','prepare_boundaries.py',[])]
completed=[]
for label,script,args in steps:
 q=subprocess.Popen([sys.executable,str(p/script)]+args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 lines=[]
 for line in iter(q.stdout.readline,b''):
  lines.append(line);print(line.decode('utf-8-sig'),end='',flush=True)
 code=q.wait();(p/(label+'-driver.log')).write_bytes(b''.join(lines));(p/(label+'-driver-exit.txt')).write_text(str(code)+'\n',encoding='utf-8')
 completed.append({'python_helper':script,'helper_exit_code':code,'log':label+'-driver.log','not_a_separate_Lean_execution':True})
 (p/'auxiliary-driver-receipt.json').write_text(json.dumps({'complete':False,'helpers':completed},indent=2)+'\n',encoding='utf-8')
 assert code==0
(p/'auxiliary-driver-receipt.json').write_text(json.dumps({'complete':True,'helpers':completed,'actual_additional_Lean_executions':10,'serial_only':True},indent=2)+'\n',encoding='utf-8')
print('All57 actual author Lean runs finished successfully; author gate still required.',flush=True)