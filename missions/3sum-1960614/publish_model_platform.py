"""Resumable, validation-gated publication of the independent model branch.

Persist every intent and returned job/submission id. Publish definitions,
theorem stubs, and accepted proofs in dependency order. Uncertain mutations
are reconciled from server records, never blindly resubmitted.
"""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import sys
import time
from urllib.parse import quote
from platform import api,p2m

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
MANIFEST=VER/'model-platform-manifest.json'
STATE=VER/'model-platform-publish.json'
manifest=json.loads(MANIFEST.read_text(encoding='utf-8'))
validation=json.loads((VER/'model-platform-validation.json').read_text(encoding='utf-8'))
digest=lambda data:hashlib.sha256(data).hexdigest()
assert manifest['validation_complete']
assert validation['manifest_sha256']==digest(MANIFEST.read_bytes())
assert validation['exact_type_comparison_passed'] and validation['frozen_root_contract_passed']
for record in manifest['definitions']+manifest['theorems']:
    fields=[('path','sha256')] if 'path' in record else [('solution_path','solution_sha256')]
    if record.get('theorem_path'):fields.append(('theorem_path','theorem_sha256'))
    for pathkey,hashkey in fields:
        assert digest((ROOT/record[pathkey]).read_bytes())==record[hashkey],record[pathkey]
state=json.loads(STATE.read_text(encoding='utf-8')) if STATE.exists() else {'items':{}}
state.setdefault('manifest_sha256',validation['manifest_sha256'])
assert state['manifest_sha256']==validation['manifest_sha256']


def persist():
    state['updated_at_utc']=datetime.now(timezone.utc).isoformat()
    temporary=STATE.with_suffix('.tmp')
    temporary.write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    temporary.replace(STATE)


def stored(name):return state['items'].setdefault(name,{})


def rows(response,key):
    return response if isinstance(response,list) else response.get(key,[])


def ensure_published(payload,kind):
    name=payload['definition_name'] if kind=='definition' else payload['theorem_name']
    item=stored(name)
    if item.get('theorem_id'):return item['theorem_id']
    expected=payload['definition'] if kind=='definition' else payload['preamble']
    if not item.get('job_id'):
        matches=[]
        offset=0
        while True:
            page=rows(api('GET',f'/publish-jobs?kind={kind}&limit=100&offset={offset}'),'jobs')
            for job in page:
                if job.get('theorem_name')!=name:continue
                assert job.get('definitions','')==expected,('Existing name has different code',name)
                if kind=='problem':assert job['formal_statement']==payload['formal_statement']
                if job['status']!='ERROR':matches.append(job)
            if len(page)<100:break
            offset+=100
        if matches:
            live=[j for j in matches if j['status'] in ('PUBLISHED','PENDING','COMPILING')]
            assert len(live)<=1,('Multiple active publication records',name)
            chosen=live[0] if live else matches[0]
            item['job_id']=chosen['id']
            persist()
        elif item.get('publish_intent'):
            raise RuntimeError('Uncertain previous publication has no matching server job yet: '+name)
        else:
            item['publish_intent']={'kind':kind,'requested_at_utc':datetime.now(timezone.utc).isoformat(),
                                    'payload_sha256':digest(json.dumps(payload,sort_keys=True).encode())}
            persist()
            response=api('POST','/submit-definition' if kind=='definition' else '/submit-problem',payload)
            assert not response.get('errors'),response
            item['job_id']=(response['job_id'] if kind=='definition' else response['jobs'][0]['job_id'])
            persist()
    job=api('GET','/publish-jobs/'+item['job_id'])
    (VER/(name.replace('.','_')+'-model-publish-job.json')).write_text(json.dumps(job,indent=2)+'\n',encoding='utf-8')
    item['publish_status']=job['status']
    if job['status']=='PUBLISHED':
        item['theorem_id']=job['theorem_id']
        persist()
        return item['theorem_id']
    persist()
    if job['status'] in ('FAILED','ERROR'):raise RuntimeError(job)
    return None


reuse=json.loads((VER/'model-upload-plan.json').read_text(encoding='utf-8'))['reusable_accepted_nodes']


def step():
    for definition in manifest['definitions']:
        if not ensure_published(definition['payload'],'definition'):
            return 'waiting for definition '+definition['payload']['definition_name']
    for theorem in manifest['theorems']:
        item=stored(theorem['name'])
        if theorem.get('existing_theorem_id'):
            current=api('GET','/theorems/'+theorem['existing_theorem_id'])
            assert current['theorem_name']==theorem['platform_name']
            item['theorem_id']=theorem['existing_theorem_id']
            persist()
        elif not ensure_published(theorem['payload'],'problem'):
            return 'waiting for theorem '+theorem['name']
    for theorem in manifest['theorems']:
        item=stored(theorem['name'])
        if item.get('proof_status')=='ACCEPTED':continue
        for child in theorem['children']:
            child_id=(reuse[child]['theorem_id'] if child in reuse else stored(child)['theorem_id'])
            current=api('GET','/theorems/'+child_id)
            assert current['status']=='Proved',('Child must be Proved before verification',child,current['status'])
        if not item.get('submission_id'):
            if item.get('verify_intent'):
                raise RuntimeError('Reconcile uncertain prior proof submission before retrying: '+theorem['name'])
            code=(ROOT/theorem['solution_path']).read_text(encoding='utf-8')
            item['verify_intent']={'requested_at_utc':datetime.now(timezone.utc).isoformat(),
                                   'solution_sha256':theorem['solution_sha256']}
            persist()
            fields={'theorem_id':item['theorem_id'],'proof_type':'prove','explanation':theorem['explanation']}
            body,ctype=p2m._multipart(fields,{'file':(Path(theorem['solution_path']).name,code)})
            status,raw=p2m._request('POST','/verify',token=p2m.get_token(),raw_body=body,ctype=ctype)
            assert 200<=status<300,(status,raw[:1600])
            result=json.loads(raw)
            item['submission_id']=result['submission_id']
            persist()
        verdict=api('GET','/verify?submission_id='+item['submission_id'])
        item['proof_status']=verdict['status']
        (VER/(theorem['name'].replace('.','_')+'-model-verdict.json')).write_text(json.dumps(verdict,indent=2)+'\n',encoding='utf-8')
        persist()
        if verdict['status']=='ACCEPTED':continue
        if verdict['status'] not in ('PENDING','RUNNING','VERIFYING','COMPILING','SKETCH_ACCEPTED'):
            raise RuntimeError(verdict)
        return 'waiting for proof '+theorem['name']+' '+verdict['status']
    graph_checks=[]
    for theorem in manifest['theorems']:
        item=stored(theorem['name'])
        current=api('GET','/theorems/'+item['theorem_id'])
        assert current['status']=='Proved',(theorem['name'],current['status'])
        graph=api('GET','/theorems/'+item['theorem_id']+'/graph')
        path=VER/(theorem['name'].replace('.','_')+'-model-graph.json')
        path.write_text(json.dumps(graph,indent=2)+'\n',encoding='utf-8')
        graph_checks.append({'name':theorem['name'],'theorem_id':item['theorem_id'],'graph_file':path.name})
    state.update(all_proofs_accepted=True,graph_snapshots=graph_checks,
                 actual_edge_audit_complete=False)
    persist()
    return 'all model proofs accepted; actual graph edge audit still required'


last=None
while True:
    message=step()
    if message!=last:print(message,flush=True)
    last=message
    if not '--watch' in sys.argv or state.get('all_proofs_accepted'):break
    time.sleep(15)
