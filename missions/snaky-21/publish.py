"""Journaled task-scoped Prove2me publication; never prints credentials."""
import argparse
import hashlib
import http.client
import json
import os
import sys
import time
from pathlib import Path
from urllib.parse import urlencode
from urllib.error import URLError
import urllib.request

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT/'scripts'))
import p2m_api as api

if os.environ.get('SNAKY21_DIRECT_API')=='1':
    # Task-local transport choice; never edits the system proxy or shared client.
    api._OPENER=urllib.request.build_opener(urllib.request.ProxyHandler({}))

ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
PAPER = 'https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf'
JOURNAL = HERE/'platform'/'journal.json'

class RetryPublication(RuntimeError):
    pass

def read_journal():
    return json.loads(JOURNAL.read_text(encoding='utf-8')) if JOURNAL.exists() else {}

def save_journal(journal):
    JOURNAL.parent.mkdir(exist_ok=True)
    temporary=JOURNAL.with_suffix('.tmp')
    temporary.write_text(json.dumps(journal,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    temporary.replace(JOURNAL)

def request(method,path,token,data=None):
    for attempt in range(6):
        try:
            status,body=api._request(method,path,token=token,data=data)
            if status==401:
                refreshed=api.get_token()
                if refreshed==token:
                    refreshed=api.get_token(force=True)
                token=refreshed
                status,body=api._request(method,path,token=token,data=data)
            if method=='GET' and status in (429,502,503,504) and attempt<5:
                print('RETRY read-only HTTP',status,path,flush=True)
                time.sleep(min(5*(attempt+1),25))
                continue
            if status not in (200,201,202):
                raise RuntimeError(f'HTTP {status} {path}: {body[:1200]}')
            return json.loads(body)
        except (URLError,TimeoutError,ConnectionError,http.client.RemoteDisconnected):
            # Retrying an ambiguous POST could duplicate a public submission.
            if method!='GET' or attempt==5:
                raise
            print('RETRY read-only transport',path,attempt+1,flush=True)
            time.sleep(min(5*(attempt+1),25))

def ensure_available(name,token):
    query=urlencode({'theorem_name':name,'env':ENV,'limit':1})
    found=request('GET','/theorems?'+query,token)
    if found.get('total',0) or found.get('theorems'):
        raise RuntimeError('Existing exact platform name requires reuse rather than duplicate publication: '+name)
    print('EXACT NAME AVAILABLE',name,flush=True)

def recover_problem_job(spec,token):
    """Reconcile an ambiguous POST against this account's exact job history."""
    jobs=request('GET','/publish-jobs?kind=problem&limit=100',token)
    matches=[item for item in jobs['publish_jobs']
             if item.get('theorem_name')==spec['theorem_name']
             and item.get('formal_statement')==spec['formal_statement']
             and item.get('definitions')==spec['preamble']]
    if not matches:
        raise RuntimeError('Ambiguous statement POST has no matching account job; do not resubmit: '+spec['theorem_name'])
    job=matches[0]
    print('RECOVERED EXISTING STATEMENT JOB',spec['theorem_name'],job['id'],job['status'],flush=True)
    return job

def wait_job(journal,key,token):
    record=journal[key]
    last=None
    while True:
        job=request('GET','/publish-jobs/'+record['job_id'],token)
        record.update({'status':job['status'],'theorem_id':job.get('theorem_id'),'error_message':job.get('error_message')})
        save_journal(journal)
        if job['status']!=last:
            print(key,job['status'],flush=True)
            last=job['status']
        if job['status'] in ('PUBLISHED','FAILED','ERROR'):
            if job['status']!='PUBLISHED':
                same_source=sum(item.get('source_sha256')==record.get('source_sha256') for item in record.get('job_history',[]))
                if job['status']=='ERROR' and same_source<2:
                    raise RetryPublication(job.get('error_message'))
                raise RuntimeError(job.get('error_message'))
            return job['theorem_id']
        time.sleep(10)

def definition(path,token,journal):
    name=path.stem.removeprefix('Def_')
    key='definition:'+name
    code=path.read_text(encoding='utf-8')
    digest=hashlib.sha256(code.encode()).hexdigest()
    previous=journal.get(key)
    same_source=0 if not previous else sum(item.get('source_sha256')==digest for item in previous.get('job_history',[]))
    retry=previous and ((previous.get('status')=='ERROR' and same_source<2) or (previous.get('status') in ('FAILED','ERROR') and previous.get('source_sha256')!=digest and not previous.get('theorem_id')))
    if key not in journal or retry:
        ensure_available(name,token)
        # A duplicate name is rejected by the platform; never overwrite one.
        data={'definition_name':name,'definition_title':name,'definition':code,'natural_language_statement':
              'Definitions for the finite conditional-claim proof of Snaky in 21 Maker moves. '
              'They use the existing integer-grid game and target, and encode the required Maker cells, '
              'the Breaker-free envelope, and the bound on actual further Maker claims. '
              'The numbered certificate data use the fixed 2026-09-25 source. No game-winning theorem is assumed.',
              'source':PAPER+'; Definition 2, Lemma 3 and Proposition 5; pinned certificate supplement.', 'env':ENV}
        result=request('POST','/submit-definition',token,data)
        history=[] if previous is None else previous.get('job_history',[])+[{k:v for k,v in previous.items() if k!='job_history'}]
        journal[key]={'job_id':result['job_id'],'source_sha256':digest,'file':str(path.relative_to(ROOT)),'job_history':history}
        save_journal(journal)
    else:
        if journal[key]['source_sha256']!=digest:
            raise RuntimeError('Published definition source changed: '+name)
    try:
        return wait_job(journal,key,token)
    except RetryPublication:
        print('RETRY unchanged definition after infrastructure error',name,flush=True)
        return definition(path,api.get_token(),journal)

def statement(spec_path,token,journal):
    spec=json.loads(spec_path.read_text(encoding='utf-8'))
    name=spec['theorem_name']
    key='theorem:'+name
    previous=journal.get(key)
    infrastructure_failure=previous and previous.get('status')=='FAILED' and any(
        marker in (previous.get('error_message') or '') for marker in
        ['DB error looking up import','ConnectionTerminated','connection reset'])
    retry=previous and (previous.get('status')=='ERROR' or infrastructure_failure) and len(previous.get('job_history',[]))<2
    if key not in journal or retry:
        ensure_available(name,token)
        body={k:spec[k] for k in ['theorem_name','theorem_title','formal_statement','natural_language_statement','preamble','source']}
        body['env']=ENV
        result=request('POST','/submit-problem',token,body)
        jobs=result.get('jobs',[])
        if not jobs:
            raise RuntimeError(str(result))
        history=[] if previous is None else previous.get('job_history',[])+[{k:v for k,v in previous.items() if k!='job_history'}]
        journal[key]={'job_id':jobs[0]['job_id'],'spec':str(spec_path.relative_to(ROOT)),'job_history':history}
        save_journal(journal)
    try:
        target=wait_job(journal,key,token)
    except RetryPublication:
        print('RETRY unchanged statement after infrastructure error',name,flush=True)
        return statement(spec_path,api.get_token(),journal)
    return target

def lemma(spec_path,token,journal):
    spec=json.loads(spec_path.read_text(encoding='utf-8'))
    target=statement(spec_path,token,journal)
    return submit(target,ROOT/spec['proof_file'],spec['explanation'],token,journal,spec['theorem_name'])

def submit(target,path,explanation,token,journal,label,resubmit_sketch=False):
    key='proof:'+label
    record=journal.get(key)
    code=path.read_text(encoding='utf-8')
    digest=hashlib.sha256(code.encode()).hexdigest()
    def retryable(item):
        if not item or item.get('status')!='ERROR':
            return False
        message=item.get('result',{}).get('error_message','')
        dependency_timeout=any(fragment in message for fragment in (
            'materialize','Failed to compile theorem module','Failed to resolve platform imports'))
        return dependency_timeout and 'timed out' in message and len(item.get('attempt_history',[]))<2
    if record and record.get('status')=='PENDING' and record.get('source_sha256')!=digest:
        raise RuntimeError('Wait for the pending proof before changing its submitted source: '+label)
    if record is None or record.get('source_sha256')!=digest or retryable(record) or (resubmit_sketch and record.get('status')=='SKETCH_ACCEPTED'):
        fields={'theorem_id':target,'proof_type':'prove','explanation':explanation}
        body,ctype=api._multipart(fields,{'file':(path.name,code)})
        status,response=api._request('POST','/verify',token=token,raw_body=body,ctype=ctype)
        if status==401:
            refreshed=api.get_token()
            if refreshed==token:
                refreshed=api.get_token(force=True)
            status,response=api._request('POST','/verify',token=refreshed,raw_body=body,ctype=ctype)
        if status not in (200,201,202):
            raise RuntimeError(f'HTTP {status}: {response[:1200]}')
        result=json.loads(response)
        history=[] if record is None else record.get('attempt_history',[])+[{k:v for k,v in record.items() if k!='attempt_history'}]
        record={'submission_id':result['submission_id'],'status':'PENDING','theorem_id':target,'source_sha256':digest,'file':str(path.relative_to(ROOT)),'attempt_history':history}
        journal[key]=record
        save_journal(journal)
    last=None
    while True:
        result=request('GET','/verify?submission_id='+record['submission_id'],token)
        record['status']=result['status']
        record['result']=result
        save_journal(journal)
        if result['status']!=last:
            print(label,result['status'],record['submission_id'],flush=True)
            last=result['status']
        if result['status']!='PENDING':
            if retryable(record):
                print('RETRY dependency compilation after saved timeout',label,flush=True)
                return submit(target,path,explanation,api.get_token(),journal,label)
            if result['status'] not in ('ACCEPTED','SKETCH_ACCEPTED'):
                raise RuntimeError(json.dumps(result,ensure_ascii=False))
            return result
        time.sleep(10)

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser()
    parser.add_argument('action',choices=['definition','lemma'])
    parser.add_argument('file')
    args=parser.parse_args()
    token=api.get_token()
    journal=read_journal()
    path=(ROOT/args.file).resolve()
    if not path.is_relative_to(ROOT):
        raise ValueError('File outside task workspace')
    if args.action=='definition':
        definition(path,token,journal)
    else:
        lemma(path,token,journal)

if __name__=='__main__':
    main()
