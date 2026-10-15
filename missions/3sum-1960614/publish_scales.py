"""Publish the verified executable schedules, resuming existing jobs safely."""
import json
from pathlib import Path
from platform import api, save

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
STATE = HERE/'verification/scales-definition-state.json'
code = (ROOT/'Definitions/Def_ThreeSum1960614_Scales.lean').read_text(encoding='utf-8')
log = (HERE/'verification/scales-rounding-build.txt').read_text(encoding='utf-8')
assert 'Built Definitions.Def_ThreeSum1960614_Scales' in log
assert 'sorry' not in code and 'axiom ' not in code
payload = {
 'definition_name':'ThreeSum1960614_Scales',
 'definition_title':'Executable rational block and band schedules for the quartic 3SUM parameters',
 'definition':code,
 'natural_language_statement':r'''For an input size $n$, let $m=\lfloor\log_2 n\rfloor$. The even microblock size is $s(m)=2\lfloor\lfloor m^{1/3}\rfloor/2\rfloor$. The number of blocks is $J(m)=20\lfloor e m/(20s(m))\rfloor$ with the exact rational $e=0.203889696$, and the total size is $\mu(m)=J(m)s(m)$. The band divisor is $2^{\lfloor-b\mu(m)\rfloor}$ with $b=-0.062656016$. All functions use natural-number integer arithmetic, including integer cube root and quotients. At $s(m)=0$, the totalized natural quotient returns zero, so $J(m)=\mu(m)=0$ and the divisor is one. The complete solver must supply its exceptional-size fallback. These functions specify the executable schedule; correctness and resource costs of the full 3SUM program are separate theorem obligations.''',
 'source':'User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, Section 4.1, 14 October 2026; even microblock inherited from c0ldzy17/three-sum-lean@2b639655e07421b9ac743de9090459bab473a7c0, Submission/ThreeSum/Scales.lean.',
 'tags':['3sum','integer-schedules','word-ram'],
 'env':'0df444a360eaa60ab8c11dca51a86af692955474'}
if STATE.exists():
    state = json.loads(STATE.read_text(encoding='utf-8'))
    assert state['payload']==payload
else:
    response = api('POST','/submit-definition',payload)
    save('scales-definition-response.json',response)
    state = {'payload':payload,'job_id':response['job_id']}
    STATE.write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
job = api('GET','/publish-jobs/'+state['job_id'])
save('scales-definition-job.json',job)
print('scales definition',job['status'],flush=True)
if job['status']=='PUBLISHED':
    state['definition_id']=job['theorem_id']
    STATE.write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
elif job['status'] in ('FAILED','ERROR'):
    raise RuntimeError(job)
