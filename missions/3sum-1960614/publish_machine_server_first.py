"""Human-authorized server compilation, with honest per-item state and retries.

No local staged-build/type gate is claimed. Declarations obey the server's
Proved-import rule. Native-type-pruned declarations also support unchanged
proofs verified as genuine sketches while children are Open. Completion still
requires every proof ACCEPTED and the live original-root graph audit.
"""
from datetime import datetime,timezone
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import sys
import time
import re
import subprocess
from platform import api as remote_api,p2m
from machine_queue_reads import owner_status_reads

readback_cache={}

def api(method,path,data=None):
    if method=='GET' and path in readback_cache:
        return readback_cache.pop(path)
    return remote_api(method,path,data)

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
MANIFEST=VER/'machine-platform-manifest.json'
STATE=VER/'machine-platform-publish.json'
BATCHES=HERE/'metadata/machine-batches'
read=lambda path:json.loads(path.read_text(encoding='utf-8'))
digest=lambda data:hashlib.sha256(data).hexdigest()
manifest=read(MANIFEST)
authorization=read(VER/'machine-server-first-authorization.json')
assert authorization['user_authorized_server_compilation']
assert authorization['manifest_sha256']==digest(MANIFEST.read_bytes())
assert not manifest['regression_only']
state=read(STATE) if STATE.exists() else {'items':{}}
state.setdefault('validation_mode','server-first')
assert state['validation_mode']=='server-first'
state.setdefault('manifest_history',[])
if digest(MANIFEST.read_bytes()) not in state['manifest_history']:
    state['manifest_history'].append(digest(MANIFEST.read_bytes()))
state['manifest_sha256']=digest(MANIFEST.read_bytes())
state['local_full_staged_build_passed']=False
state['local_full_staged_type_gate_passed']=False
reuse={r['name']:r for r in manifest['reused_theorems']}
open_sketch_mode=bool(manifest.get('open_sketch_pipeline',{}).get('enabled'))
publication_hashes={r['module'].removeprefix('Definitions.Def_'):r['sha256'] for r in manifest['definitions']}
publication_hashes.update({r['name']:digest((r['preamble']+'\n'+r['formal_statement']).encode()) for r in manifest['theorems']})

def persist():
    state['updated_at_utc']=datetime.now(timezone.utc).isoformat()
    path=STATE.with_suffix('.tmp')
    path.write_text(json.dumps(state,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    path.replace(STATE)

def item_for(name):return state['items'].setdefault(name,{})

def metadata():
    found={}
    for batch in read(BATCHES/'index.json'):
        source=ROOT/batch['input']
        assert digest(source.read_bytes())==batch['sha256']
        output=BATCHES/('output-'+str(batch['batch']).zfill(3)+'.json')
        if not output.exists():continue
        entries=read(output)
        assert isinstance(entries,list) and {e['name'] for e in entries}==set(batch['names'])
        for entry in entries:
            assert entry['name'] not in found
            assert len(entry['natural_language_statement'])>=100
            assert isinstance(entry['tags'],list)
            found[entry['name']]=entry
    return found

def payload(record,kind,meta):
    name=record['module'].removeprefix('Definitions.Def_') if kind=='definition' else record['name']
    if name not in meta:return None
    entry=meta[name]
    tags=list(dict.fromkeys([manifest['project_tag'],*entry['tags']]))
    if kind=='definition':
        code=(ROOT/record['path']).read_bytes()
        assert digest(code)==record['sha256']
        sources=[]
        for module in record.get('original_modules',[record['original_module']]):
            source_path=('Submission/Closed3Sum/'+module.removeprefix('Closed3Sum.').replace('.','/')
                         if module.startswith('Closed3Sum.') else module.replace('.','/'))+'.lean'
            sources.append(manifest['source_repository']+'/blob/'+manifest['source_commit']+'/'+source_path)
        return {'definition_name':name,'definition_title':entry['definition_title'],
                'definition':code.decode('utf-8'),'natural_language_statement':entry['natural_language_statement'],
                'source':'\n'.join(sources),'tags':tags,'env':manifest['environment']}
    assert 0<len(entry['theorem_title'])<=200 and len(entry['explanation'])>=100
    assert (ROOT/record['theorem_path']).read_text(encoding='utf-8')==record['preamble']+'\n'+record['formal_statement']+'\n'
    for key in ('solution','theorem'):
        assert digest((ROOT/record[key+'_path']).read_bytes())==record[key+'_sha256']
    return {'theorem_name':name,'theorem_title':entry['theorem_title'],'preamble':record['preamble'],
            'formal_statement':record['formal_statement'],'natural_language_statement':entry['natural_language_statement'],
            'source':record['source'],'tags':tags,'env':manifest['environment']}

def submit_payload(body,kind):
    name=body['definition_name'] if kind=='definition' else body['theorem_name']
    item=item_for(name)
    code_hash=digest((body['definition'] if kind=='definition' else body['preamble']+'\n'+body['formal_statement']).encode())
    if item.get('blocked_publication_sha256')==code_hash:
        waiting_for_proofs='Imported platform theorems must be Proved at submission time' in (item.get('blocked_publication_error') or '')
        parser_timeout='Import parser timed out after 5s' in (item.get('blocked_publication_error') or '')
        parser_retries=sum(h.get('code_sha256')==code_hash and h.get('retry_reason')=='platform import parser timeout' for h in item.get('publish_history',[]))
        if not waiting_for_proofs and not (parser_timeout and parser_retries<3):return None
        if waiting_for_proofs:
            record=next(r for r in manifest['theorems'] if r['name']==name)
            if not imports_ready(record,'declaration'):return None
        item.pop('blocked_publication_sha256',None)
    if item.get('theorem_id'):
        assert item.get('published_code_sha256')==code_hash,('Published statement is immutable',name)
        return item['theorem_id']
    if item.get('publish_intent') and not item.get('job_id'):
        raise RuntimeError('Reconcile uncertain publication intent before retry: '+name)
    if item.get('job_id'):
        job=api('GET','/publish-jobs/'+item['job_id'])
        item['publish_status']=job['status']
        (VER/(name.replace('.','_')+'-machine-publish-job.json')).write_text(json.dumps(job,indent=2)+'\n',encoding='utf-8')
        if job['status']=='PUBLISHED':
            assert item['publish_code_sha256']==code_hash
            item.update(theorem_id=job['theorem_id'],published_code_sha256=code_hash)
            persist();return item['theorem_id']
        if job['status'] in ('FAILED','ERROR'):
            persist()
            infrastructure_reason=('platform database connection terminated' if
                                   'DB error looking up import' in job.get('error_message','') and
                                   'ConnectionTerminated' in job.get('error_message','') else
                                   ('platform import parser timeout' if 'Import parser timed out after 5s' in job.get('error_message','') else None))
            infrastructure_failure=infrastructure_reason is not None
            waiting_for_proofs='Imported platform theorems must be Proved at submission time' in job.get('error_message','')
            if waiting_for_proofs:
                record=next(r for r in manifest['theorems'] if r['name']==name)
                if not imports_ready(record,'declaration'):
                    item['blocked_publication_sha256']=code_hash
                    item['blocked_publication_error']=job['error_message']
                    persist();return None
            infrastructure_attempts=sum(h.get('code_sha256')==code_hash and h.get('retry_reason')==infrastructure_reason
                                        for h in item.get('publish_history',[]))
            if item['publish_code_sha256']==code_hash and job['status']=='FAILED' and not waiting_for_proofs and (not infrastructure_failure or infrastructure_attempts>=3):
                item['blocked_publication_sha256']=code_hash
                item['blocked_publication_error']=job.get('error_message')
                persist()
                print('Source correction required for publication:',name,json.dumps((job.get('error_message') or '')[:1200],ensure_ascii=True),flush=True)
                return None
            item.setdefault('publish_history',[]).append({'job_id':item['job_id'],'status':job['status'],
                                                          'code_sha256':item['publish_code_sha256'],
                                                          'error_message':job.get('error_message'),
                                                          'retry_reason':infrastructure_reason if infrastructure_failure else ('imported theorems now Proved' if waiting_for_proofs else 'source correction or server ERROR')})
            item.pop('job_id');item.pop('publish_intent',None)
        else:
            persist();return None
    item['publish_intent']={'requested_at_utc':datetime.now(timezone.utc).isoformat(),'kind':kind}
    item['publish_code_sha256']=code_hash
    persist()
    result=api('POST','/submit-definition' if kind=='definition' else '/submit-problem',body)
    assert not result.get('errors'),result
    item['job_id']=result['job_id'] if kind=='definition' else result['jobs'][0]['job_id']
    item['publish_status']='QUEUED'
    persist();return None

def verify(record,explanation):
    item=item_for(record['name'])
    code=(ROOT/record['solution_path']).read_bytes()
    assert digest(code)==record['solution_sha256']
    if item.get('blocked_solution_sha256')==record['solution_sha256']:return False
    if item.get('proof_status')=='ACCEPTED':
        assert item['verified_solution_sha256']==record['solution_sha256']
        return True
    if item.get('verify_intent') and not item.get('submission_id'):
        raise RuntimeError('Reconcile uncertain proof intent before retry: '+record['name'])
    if item.get('submission_id'):
        verdict=api('GET','/verify?submission_id='+item['submission_id'])
        item['proof_status']=verdict['status']
        (VER/(record['name'].replace('.','_')+'-machine-verdict.json')).write_text(json.dumps(verdict,indent=2)+'\n',encoding='utf-8')
        if verdict['status']=='ACCEPTED':
            assert item['submitted_solution_sha256']==record['solution_sha256']
            item['verified_solution_sha256']=record['solution_sha256']
            persist();return True
        if verdict['status'] in ('PENDING','RUNNING','VERIFYING','COMPILING','SKETCH_ACCEPTED'):
            if verdict['status']=='SKETCH_ACCEPTED':
                assert item['submitted_solution_sha256']==record['solution_sha256']
                item['verified_sketch_solution_sha256']=record['solution_sha256']
            persist();return False
        timed_out = 'Verification timed out after 300s' in (verdict.get('error_message') or '')
        if (verdict['status']!='ERROR' or timed_out) and item['submitted_solution_sha256']==record['solution_sha256']:
            item['blocked_solution_sha256']=record['solution_sha256']
            item['blocked_solution_error']=verdict.get('error_message')
            persist()
            print('Source correction required for proof:',record['name'],json.dumps((verdict.get('error_message') or '')[:1200],ensure_ascii=True),flush=True)
            return False
        item.setdefault('proof_history',[]).append({'submission_id':item['submission_id'],'status':verdict['status'],
                                                   'solution_sha256':item['submitted_solution_sha256'],
                                                   'error_message':verdict.get('error_message')})
        item.pop('submission_id');item.pop('verify_intent',None)
    item['verify_intent']={'requested_at_utc':datetime.now(timezone.utc).isoformat()}
    item['submitted_solution_sha256']=record['solution_sha256']
    persist()
    fields={'theorem_id':item['theorem_id'],'proof_type':'prove','explanation':explanation}
    body,ctype=p2m._multipart(fields,{'file':(Path(record['solution_path']).name,code.decode('utf-8'))})
    status,raw=p2m._request('POST','/verify',token=p2m.get_token(),raw_body=body,ctype=ctype)
    assert 200<=status<300,(status,raw[:1600])
    item['submission_id']=json.loads(raw)['submission_id']
    item['proof_status']='PENDING'
    persist();return False

def step():
    meta=metadata()
    for record in manifest['definitions']:
        body=payload(record,'definition',meta)
        if body is None:return 'waiting for metadata '+record['module']
        if not submit_payload(body,'definition'):return 'platform compiling definition '+body['definition_name']
    for record in manifest['theorems']:
        body=payload(record,'problem',meta)
        if body is None:return 'waiting for metadata '+record['name']
        item=item_for(record['name'])
        if item.get('proof_status')=='ACCEPTED':
            assert item['verified_solution_sha256']==record['solution_sha256']
            continue
        for child in record['children']:
            child_id=reuse[child]['theorem_id'] if child in reuse else item_for(child)['theorem_id']
            child_state=api('GET','/theorems/'+child_id)
            assert child_state['status']=='Proved',('Child must be Proved first',child,child_state['status'])
        if record.get('existing_theorem_id'):
            assert record['name']=='ThreeSum1960614.costs_solve_3sum'
            assert record['existing_theorem_id']=='7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'
            target=api('GET','/theorems/'+record['existing_theorem_id'])
            assert target['theorem_name']==record['name']
            item['theorem_id']=record['existing_theorem_id'];persist()
        elif not submit_payload(body,'problem'):return 'platform compiling theorem '+record['name']
        if not verify(record,meta[record['name']]['explanation']):return 'platform verifying proof '+record['name']
    state['all_proofs_accepted']=True
    state['actual_edge_audit_complete']=False
    persist()
    return 'all proofs accepted; actual live graph audit required'


# A small bounded server queue allows independent leaves to progress while a
# later definition compiles. Every mutation is still recorded sequentially.
definition_modules={r['module']:r['module'].removeprefix('Definitions.Def_') for r in manifest['definitions']}
theorem_modules={str(Path(r['theorem_path']).with_suffix('')).replace('\\','/').replace('/','.'):
                 r['name'] for r in manifest['theorems']}
file_imports={}
reuse_confirmed=set()
downstream={r['name']:set() for r in manifest['theorems']}
for record in manifest['theorems']:
    for child in record['children']:
        if child in downstream:downstream[child].add(record['name'])
critical_depth={}

def downstream_depth(name,visiting=None):
    if name in critical_depth:return critical_depth[name]
    visiting=set() if visiting is None else visiting
    assert name not in visiting,('Cyclic theorem dependency',name)
    visiting.add(name)
    depth=1+max((downstream_depth(parent,visiting) for parent in downstream[name]),default=0)
    visiting.remove(name)
    critical_depth[name]=depth
    return depth

for name in downstream:downstream_depth(name)

def imports_ready(record,kind):
    if kind=='definition':
        imports=record['dependencies']
    else:
        key=(record['name'],kind)
        if key not in file_imports:
            file_imports[key]=set(re.findall(r'(?m)^import ([\w.]+)$',record['preamble']))
            if kind!='declaration':
                file_imports[key].update(re.findall(r'(?m)^import ([\w.]+)$',
                                         (ROOT/record['solution_path']).read_text(encoding='utf-8')))
        imports=file_imports[key]
    for module in imports:
        if module in definition_modules and not item_for(definition_modules[module]).get('theorem_id'):
            return False
        if module in theorem_modules:
            dependency=item_for(theorem_modules[module])
            if kind=='problem' and open_sketch_mode:
                if not dependency.get('theorem_id'):return False
            elif dependency.get('proof_status')!='ACCEPTED':return False
    if kind not in ('definition','declaration'):
        for child in record['children']:
            if child in reuse:
                if child not in reuse_confirmed:
                    current=api('GET','/theorems/'+reuse[child]['theorem_id'])
                    assert current['status']=='Proved' and current['theorem_name']==child
                    reuse_confirmed.add(child)
            elif open_sketch_mode:
                if not item_for(child).get('theorem_id'):return False
            elif item_for(child).get('proof_status')!='ACCEPTED':return False
    return True

def step_queued(limit):
    meta=metadata()
    # Older uploaders persisted the returned submission ID before recording
    # its initial status. An unknown status with an ID must always be polled.
    running_proofs=(None,'PENDING','RUNNING','VERIFYING','COMPILING','SKETCH_ACCEPTED')
    compiling_proofs=(None,'PENDING','RUNNING','VERIFYING','COMPILING')
    # Independent status reads overlap; publication and proof mutations below
    # stay sequential and preserve their intent/receipt ordering.
    poll_paths=[]
    for item in state['items'].values():
        if item.get('job_id') and not item.get('theorem_id') and item.get('publish_status') not in ('FAILED','ERROR'):
            poll_paths.append('/publish-jobs/'+item['job_id'])
        if item.get('submission_id') and item.get('proof_status') in running_proofs:
            poll_paths.append('/verify?submission_id='+item['submission_id'])
    if poll_paths:
        readback_cache.update(owner_status_reads(state['items']))
    def active_count():
        return sum(bool(x.get('job_id') and not x.get('theorem_id') and
                        x.get('publish_status') not in ('FAILED','ERROR','PUBLISHED'))+
                   bool(x.get('submission_id') and x.get('proof_status') in compiling_proofs)
                   for x in state['items'].values())
    # Collect completions before filling free slots. Otherwise a later job can
    # finish and refill a slot after an earlier ready retry was skipped forever.
    for record in manifest['definitions']:
        item=item_for(record['module'].removeprefix('Definitions.Def_'))
        if item.get('job_id') and not item.get('theorem_id') and item.get('publish_status') not in ('FAILED','ERROR'):
            submit_payload(payload(record,'definition',meta),'definition')
    for record in manifest['theorems']:
        item=item_for(record['name'])
        if item.get('job_id') and not item.get('theorem_id') and item.get('publish_status') not in ('FAILED','ERROR'):
            submit_payload(payload(record,'problem',meta),'problem')
        if item.get('submission_id') and item.get('proof_status') in running_proofs:
            verify(record,meta[record['name']]['explanation'])
    for record in manifest['definitions']:
        name=record['module'].removeprefix('Definitions.Def_')
        item=item_for(name)
        if item.get('theorem_id'):continue
        if item.get('job_id') and item.get('publish_status') not in ('FAILED','ERROR'):continue
        if not imports_ready(record,'definition'):continue
        if (not item.get('job_id') or item.get('publish_status') in ('FAILED','ERROR')) and active_count()>=limit:continue
        body=payload(record,'definition',meta)
        if body is None:continue
        submit_payload(body,'definition')
    prioritized=sorted(manifest['theorems'],key=lambda r:(
        not bool(item_for(r['name']).get('theorem_id')),
        item_for(r['name']).get('proof_status') not in ('CE','WA','FAILED','ERROR'),
        -critical_depth[r['name']],-len(downstream[r['name']])))
    for record in prioritized:
        item=item_for(record['name'])
        if item.get('proof_status')=='ACCEPTED':
            assert item['verified_solution_sha256']==record['solution_sha256']
            continue
        if item.get('submission_id'):
            if not imports_ready(record,'problem'):continue
            if item.get('proof_status') in running_proofs:continue
            if item.get('proof_status') not in running_proofs and active_count()>=limit:continue
            verify(record,meta[record['name']]['explanation'])
            continue
        if not item.get('theorem_id'):
            # The publication endpoint requires Proved theorem imports even
            # for a sorry-stub. Proof-only imports need not delay publication.
            if not imports_ready(record,'declaration'):continue
            if record.get('existing_theorem_id'):
                if active_count()>=limit:continue
                assert record['name']=='ThreeSum1960614.costs_solve_3sum'
                assert record['existing_theorem_id']=='7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6'
                current=api('GET','/theorems/'+record['existing_theorem_id'])
                assert current['theorem_name']==record['name']
                item['theorem_id']=record['existing_theorem_id'];persist()
            else:
                if item.get('job_id') and item.get('publish_status') not in ('FAILED','ERROR'):continue
                if (not item.get('job_id') or item.get('publish_status') in ('FAILED','ERROR')) and active_count()>=limit:continue
                body=payload(record,'problem',meta)
                if body is None:continue
                if not submit_payload(body,'problem'):
                    continue
        if not imports_ready(record,'problem'):continue
        if active_count()>=limit:continue
        verify(record,meta[record['name']]['explanation'])
    definitions_done=sum(bool(item_for(n).get('theorem_id')) for n in definition_modules.values())
    proofs_done=sum(item_for(r['name']).get('proof_status')=='ACCEPTED' for r in manifest['theorems'])
    if proofs_done==len(manifest['theorems']) and definitions_done==len(manifest['definitions']):
        state['all_proofs_accepted']=True
        state['actual_edge_audit_complete']=False
        persist()
        return 'all proofs accepted; actual live graph audit required'
    state['server_queue_limit']=limit
    persist()
    blocked=sum(item_for(r['name']).get('blocked_solution_sha256')==r['solution_sha256'] for r in manifest['theorems'])
    sketches=sum(item_for(r['name']).get('proof_status')=='SKETCH_ACCEPTED' for r in manifest['theorems'])
    blocked_publications=sum(item_for(name).get('blocked_publication_sha256')==code_hash for name,code_hash in publication_hashes.items())
    return f'Platform: {definitions_done}/{len(manifest["definitions"])} definitions published; {proofs_done}/{len(manifest["theorems"])} proofs accepted; {sketches} verified sketches awaiting children; {active_count()} jobs in flight; {blocked} proofs and {blocked_publications} publications need attention'

persist()
last=None
while True:
    if (VER/'machine-server-first.pause').exists():
        print('Uploader paused at a safe boundary; stored jobs remain resumable.',flush=True)
        break
    limit=int(sys.argv[sys.argv.index('--concurrency')+1]) if '--concurrency' in sys.argv else 1
    # Both publication and verification document a 100-job pending cap.
    # Keep one bounded queue well below it while overlapping independent work.
    assert 1<=limit<=32
    message=step_queued(limit) if limit>1 or open_sketch_mode else step()
    if message!=last:print(message,flush=True)
    last=message
    if '--watch' not in sys.argv or state.get('all_proofs_accepted'):break
    time.sleep(15)

if '--watch' in sys.argv and state.get('all_proofs_accepted'):
    print('All proofs accepted; checking the complete actual graph and original main reduction.',flush=True)
    subprocess.run([sys.executable,str(HERE/'audit_machine_graph.py')],check=True)
