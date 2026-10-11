"""Resume only these two original milestones, with one local checker."""
import json
import hashlib
import re
import subprocess
import sys
import time
from pathlib import Path
import generate_milestone_certificate
import pipeline
import publish
from finalize import BASELINE

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]

def run(script,*args):
    subprocess.run([sys.executable,'-B',str(HERE/script),*args],cwd=ROOT,check=True)

def stage(name):
    (HERE/'verification'/'milestones-progress.json').write_text(json.dumps({'stage':name},indent=2)+'\n',encoding='utf-8')
    print('STAGE',name,flush=True)

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    policy=HERE/'verification'/'resource-policy.json'
    if policy.exists() and not json.loads(policy.read_text(encoding='utf-8'))['local_lean_enabled']:
        raise RuntimeError('This local-check runner is disabled; use platform-side milestone verification.')
    stage('wait-strategy-local')
    out=HERE/'verification'/'milestone-strategy3-stdout.log'
    err=HERE/'verification'/'milestone-strategy3-stderr.log'
    while 'LOCAL PASS milestone-Strategy35' not in out.read_text(encoding='utf-8'):
        if err.stat().st_size:
            raise RuntimeError('Strategy checker failed; inspect '+str(err))
        time.sleep(5)
    stage('submit-strategy')
    run('submit_milestone.py','strategy')
    stage('check-certificate-probe')
    run('check_milestones.py','probe')
    stage('generate-full-certificate')
    generate_milestone_certificate.main()
    source=ROOT/'Solutions'/'SnakyMilestones'/'Certificate35.lean'
    (HERE/'platform'/'milestone-certificate-proof.lean').write_bytes(source.read_bytes())
    stage('check-full-certificate')
    run('check_milestones.py','certificate')
    stage('submit-certificate')
    run('submit_milestone.py','certificate')
    stage('workspace-build')
    path=HERE/'scope.json'
    scope=json.loads(path.read_text(encoding='utf-8'))
    for item in ['Solutions/SnakyMilestones/Strategy35.lean','Solutions/SnakyMilestones/Certificate35.lean']:
        if item not in scope['build']:
            scope['build'].append(item)
    path.write_text(json.dumps(scope,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    pipeline.run_checked([sys.executable,'-B','scripts/workspace.py','build','snaky-21'],'milestone-workspace-build')
    check=subprocess.run([sys.executable,'-B','scripts/workspace.py','check'],cwd=ROOT,
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
    (HERE/'verification'/'milestone-workspace-check.log').write_text(check.stdout,encoding='utf-8')
    errors={s for s in check.stdout.splitlines() if s.startswith('ERROR:')}
    if errors-BASELINE:
        raise RuntimeError('New workspace errors: '+str(errors-BASELINE))
    stage('verify-final-milestones')
    token=publish.api.get_token()
    milestones=publish.request('GET','/missions/8aa93f9c-de49-4185-9e83-413d0f9f8155/milestones?limit=20',token)
    if len(milestones['milestones'])!=2 or not all(m['completed'] and m['theorem']['status']=='Proved' for m in milestones['milestones']):
        raise RuntimeError('The two original milestones are not both completed')
    (HERE/'verification'/'milestones-after.json').write_text(json.dumps(milestones,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    journal=publish.read_journal()
    accepted=[]
    for milestone in milestones['milestones']:
        target=milestone['theorem']
        record=journal['proof:'+target['theorem_name']]
        if record['status']!='ACCEPTED':
            raise RuntimeError('Our milestone submission is not ACCEPTED')
        rows=publish.request('GET','/theorems/'+target['id']+'/submissions?status=ACCEPTED&limit=200',token)
        own=next(r for r in rows['submissions'] if r['id']==record['submission_id'])
        if own['user_id']!='418b0711-62a5-416a-ba5d-876ae8758fe3':
            raise RuntimeError('Milestone contribution has an unexpected owner')
        accepted.append(own)
    paths=[ROOT/'Definitions'/'Def_SnakyCertificate.lean',ROOT/'Definitions'/'Def_SnakyConditional.lean',
           ROOT/'Solutions'/'SnakyMilestones'/'Strategy35.lean',
           ROOT/'Solutions'/'SnakyMilestones'/'Certificate35.lean']
    report={'status':'COMPLETE','milestones':milestones['milestones'],'accepted_submissions':accepted,
            'source_sha256':{p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
            'local_axiom_audits':{name:re.findall(r'depends on axioms: \[([^\]]*)\]',
                (HERE/'verification'/('milestone-'+name+'.log')).read_text(encoding='utf-8'))
                for name in ['Strategy35','Certificate35']},
            'certificate_rows':616,'certificate_placement_terms':1837,
            'workspace_build_log':'verification/milestone-workspace-build.log',
            'new_workspace_errors':[],'preexisting_workspace_errors':sorted(errors)}
    (HERE/'verification'/'milestones-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    stage('COMPLETE')

if __name__=='__main__':
    main()
