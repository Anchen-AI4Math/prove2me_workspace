"""Platform-only verification after the user reported local resource exhaustion."""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from datetime import datetime,timezone
import publish
from finalize import BASELINE
from submit_milestone import SPECS

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE='https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyCertificate.lean'

def stage(name):
    data={'stage':name,'local_lean_enabled':False,'updated_at':datetime.now(timezone.utc).isoformat()}
    (HERE/'verification'/'milestones-progress.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    print('STAGE',name,flush=True)

def definition(item,wait=True):
    path=ROOT/item['file'];name=path.stem.removeprefix('Def_')
    code=path.read_text(encoding='utf-8');digest=hashlib.sha256(code.encode()).hexdigest()
    journal=publish.read_journal();key='definition:'+name
    previous=journal.get(key)
    retry=previous and previous.get('status') in ('FAILED','ERROR') and previous.get('source_sha256')!=digest
    if previous is None or retry:
        for required in item.get('requires',[]):
            publish.wait_job(publish.read_journal(),'definition:'+required,publish.api.get_token())
        journal=publish.read_journal()
        token=publish.api.get_token();publish.ensure_available(name,token)
        result=publish.request('POST','/submit-definition',token,
            {'definition_name':name,'definition_title':name,'definition':code,
             'natural_language_statement':item['description'],'source':SOURCE+'; Proposition 10, original 35-move finite certificate.','env':publish.ENV})
        history=[] if previous is None else previous.get('job_history',[])+[{k:v for k,v in previous.items() if k!='job_history'}]
        journal[key]={'job_id':result['job_id'],'source_sha256':digest,'file':item['file'],'job_history':history}
        publish.save_journal(journal)
    elif journal[key]['source_sha256']!=digest:
        raise RuntimeError('A recorded definition changed: '+name)
    if wait:
        publish.wait_job(journal,key,publish.api.get_token())
    return key

def lemma(slug):
    result=publish.lemma(HERE/'platform'/(slug+'.json'),publish.api.get_token(),publish.read_journal())
    if result['status']!='ACCEPTED':
        raise RuntimeError('A support result is not fully accepted: '+slug)

def finalize():
    stage('verify-original-milestones')
    token=publish.api.get_token()
    live=publish.request('GET','/missions/8aa93f9c-de49-4185-9e83-413d0f9f8155/milestones?limit=20',token)
    if len(live['milestones'])!=2 or not all(m['completed'] and m['theorem']['status']=='Proved' for m in live['milestones']):
        raise RuntimeError('Original milestones are not both completed')
    (HERE/'verification'/'milestones-after.json').write_text(json.dumps(live,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    journal=publish.read_journal();accepted=[]
    for m in live['milestones']:
        target=m['theorem'];record=journal['proof:'+target['theorem_name']]
        if record['status']!='ACCEPTED':
            raise RuntimeError('Our original milestone proof is not accepted')
        items=publish.request('GET','/theorems/'+target['id']+'/submissions?status=ACCEPTED&limit=200',token)
        own=next(x for x in items['submissions'] if x['id']==record['submission_id'])
        if own['user_id']!='418b0711-62a5-416a-ba5d-876ae8758fe3':
            raise RuntimeError('Unexpected contribution account')
        accepted.append(own)
    graph=publish.request('GET','/theorems/c5e790f7-904e-40dd-a7f5-ba72d31e941b/graph?depth=30',token)
    (HERE/'verification'/'milestone-certificate-graph.json').write_text(json.dumps(graph,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    ids={n['theorem_id'] for n in graph['nodes']}
    missing=[key for key,val in journal.items() if key.startswith('theorem:OAI.SnakyCertificate.MilestoneChecks.') and val.get('theorem_id') not in ids]
    if missing:
        raise RuntimeError('Unconnected milestone supports: '+str(missing))
    check=subprocess.run([sys.executable,'-B','scripts/workspace.py','check'],cwd=ROOT,
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
    (HERE/'verification'/'milestone-workspace-check.log').write_text(check.stdout,encoding='utf-8')
    errors={s for s in check.stdout.splitlines() if s.startswith('ERROR:')}
    if errors-BASELINE:
        raise RuntimeError('New workspace errors: '+str(errors-BASELINE))
    sources=list((ROOT/'Solutions'/'SnakyMilestones').glob('*.lean'))+list((ROOT/'Definitions').glob('Def_Snaky35*.lean'))
    report={'status':'COMPLETE','milestones':live['milestones'],'accepted_submissions':accepted,
            'certificate_rows':616,'certificate_placement_terms':1837,'unconnected_support_theorems':[],
            'verification_route':'platform-side kernel verification of all blocks and final exact target',
            'local_lean_enabled':False,
            'local_full_certificate_build':'not run after user reported that the computer froze',
            'strategy_local_axioms':re.findall(r'depends on axioms: \[([^\]]*)\]',
                (HERE/'verification'/'milestone-Strategy35.log').read_text(encoding='utf-8')),
            'source_sha256':{p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
            'new_workspace_errors':[],'preexisting_workspace_errors':sorted(errors)}
    (HERE/'verification'/'milestones-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    stage('COMPLETE')

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    manifest=json.loads((HERE/'platform'/'milestone35-manifest.json').read_text(encoding='utf-8'))
    first,*caches=manifest['definitions']
    stage('publish-'+Path(first['file']).stem)
    definition(first)
    for offset in range(0,len(caches),4):
        batch=caches[offset:offset+4]
        for item in batch:
            stage('publish-'+Path(item['file']).stem)
            definition(item,wait=False)
        for item in batch:
            stage('wait-'+Path(item['file']).stem)
            definition(item)
    stage('verify-lookup-support')
    lemma(manifest['lookup'])
    for slug in manifest['parts']:
        for group in manifest.get('subparts',{}).get(slug,[]):
            stage('verify-'+group)
            lemma(group)
        stage('verify-'+slug)
        lemma(slug)
    stage('verify-original-certificate-target')
    spec=SPECS['certificate']
    result=publish.submit(spec['theorem_id'],HERE/'platform'/spec['file'],spec['explanation']+
        ' To protect the user\'s 16 GB computer after a resource incident, the full certificate was '
        'verified in small pieces by the platform rather than rebuilt locally. Every imported support '
        'is now Proved; the final submission is the exact original seven-part conjunction.',
        publish.api.get_token(),publish.read_journal(),spec['theorem_name'])
    if result['status']!='ACCEPTED':
        raise RuntimeError('Original finite milestone is not ACCEPTED')
    finalize()

if __name__=='__main__':
    main()
