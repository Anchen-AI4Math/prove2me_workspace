"""One journal writer, one local Lean checker, bounded asynchronous API jobs."""
import copy
import hashlib
import json
import re
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import pipeline
import publish
import local_completion

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=HERE/'platform'
LOCK=threading.RLock()
STOP=threading.Event()
THREAD=threading.local()
ORIGINAL_SAVE=publish.save_journal
ORIGINAL_TOKEN=publish.api.get_token
JOURNAL=publish.read_journal()

def read():
    with LOCK:
        return copy.deepcopy(JOURNAL)

def save(local):
    allowed=getattr(THREAD,'allowed',None)
    if allowed is None:
        raise RuntimeError('Missing task-scoped journal ownership')
    with LOCK:
        for key in allowed:
            if key in local:
                JOURNAL[key]=copy.deepcopy(local[key])
        ORIGINAL_SAVE(JOURNAL)

publish.read_journal=read
publish.save_journal=save

def locked_token(*args,**kwargs):
    with LOCK:
        return ORIGINAL_TOKEN(*args,**kwargs)

publish.api.get_token=locked_token

def token():
    with LOCK:
        return publish.api.get_token()

def definitions():
    names=['Snaky21Data10','Snaky21Data11']
    THREAD.allowed={'definition:'+name for name in names}
    for name in names:
        if STOP.is_set():
            raise RuntimeError('Stopped after a dependency failure')
        publish.definition(ROOT/'Definitions'/('Def_'+name+'.lean'),token(),read())
    from publish_cache_parts import part
    for i in range(12):
        part(i,sys.modules[__name__])
    THREAD.allowed={'definition:Snaky21Calc11','definition:Snaky21Catalog'}
    # The umbrella cache imports every literal. Adapters now import just their
    # own published parts, so a saved umbrella timeout cannot block proofs.
    umbrella=read().get('definition:Snaky21Calc11',{})
    if umbrella.get('status') in ('PENDING','COMPILING'):
        job=publish.request('GET','/publish-jobs/'+umbrella['job_id'],token())
        local=read()
        local['definition:Snaky21Calc11'].update({'status':job['status'],'theorem_id':job.get('theorem_id'),'error_message':job.get('error_message')})
        save(local)
    print('OPTIONAL CACHE UMBRELLA',read().get('definition:Snaky21Calc11',{}).get('status'),flush=True)
    for name in ('Snaky21Catalog',):
        previous=read().get('definition:'+name,{})
        if previous.get('status')=='PUBLISHED':
            print('REUSE PUBLISHED',name,flush=True)
        else:
            path=ROOT/'Definitions'/('Def_'+name+'.lean')
            publish.definition(path,token(),read())
    print('ALL CERTIFICATE DEFINITIONS PUBLISHED',flush=True)

def imports(code):
    return re.findall(r'^import\s+(\S+)',code,re.M)

def missing_modules(modules):
    state=read()
    missing=[]
    for module in modules:
        if module.startswith('Definitions.Def_'):
            name=module.removeprefix('Definitions.Def_')
            if name=='SnakyTwentyOne':
                continue
            if state.get('definition:'+name,{}).get('status')!='PUBLISHED':
                missing.append(module)
        elif module.startswith('Theorems.Thm_'):
            # Names are taken from exact task specs; underscores are retained.
            matches=[v for k,v in state.items() if k.startswith('theorem:') and 'Theorems.Thm_'+k.removeprefix('theorem:').replace('.','_')==module]
            if not matches or matches[0].get('status')!='PUBLISHED':
                missing.append(module)
    return missing

def statement_worker(spec_path):
    spec=json.loads(spec_path.read_text(encoding='utf-8'))
    name=spec['theorem_name']
    THREAD.allowed={'theorem:'+name}
    while missing_modules(imports(spec['preamble'])):
        if STOP.is_set():
            raise RuntimeError('Stopped after a dependency failure')
        time.sleep(5)
    local=read()
    key='theorem:'+name
    previous=local.get(key)
    if previous is None or (previous.get('status')=='ERROR' and len(previous.get('job_history',[]))<2):
        publish.ensure_available(name,token())
        data={k:spec[k] for k in ['theorem_name','theorem_title','formal_statement','natural_language_statement','preamble','source']}
        data['env']=publish.ENV
        try:
            result=publish.request('POST','/submit-problem',token(),data)
            job_id=result['jobs'][0]['job_id']
        except (TimeoutError,ConnectionError,publish.URLError,publish.http.client.RemoteDisconnected):
            job_id=publish.recover_problem_job(spec,token())['id']
        history=[] if previous is None else previous.get('job_history',[])+[{k:v for k,v in previous.items() if k!='job_history'}]
        local[key]={'job_id':job_id,'spec':str(spec_path.relative_to(ROOT)),'job_history':history}
        save(local)
    try:
        target=publish.wait_job(local,key,token())
    except publish.RetryPublication:
        return statement_worker(spec_path)
    return target

def proof_worker(spec_path,target):
    spec=json.loads(spec_path.read_text(encoding='utf-8'))
    name=spec['theorem_name']
    THREAD.allowed={'proof:'+name}
    candidate=ROOT/spec['proof_file']
    while missing_modules(imports(candidate.read_text(encoding='utf-8'))):
        if STOP.is_set():
            raise RuntimeError('Stopped after a dependency failure')
        time.sleep(5)
    result=publish.submit(target,candidate,spec['explanation'],token(),read(),name)
    print('VERIFIED',name,result['status'],flush=True)
    return result

def ensure_interfaces(candidate):
    visited=set()
    def visit(module):
        if module in visited:
            return
        visited.add(module)
        source=ROOT/Path(*module.split('.')).with_suffix('.lean')
        output=ROOT/'.lake'/'build'/'lib'/'lean'/Path(*module.split('.')).with_suffix('.olean')
        if not source.is_file():
            return
        # A changed minimal interface must be compiled before its clients.
        if output.exists() and module.startswith('Definitions.'):
            audited=json.loads(local_completion.STAMP.read_text(encoding='utf-8'))['source_sha256']
            if audited.get(source.relative_to(ROOT).as_posix())==hashlib.sha256(source.read_bytes()).hexdigest():
                return
        if output.exists() and output.stat().st_mtime>=source.stat().st_mtime:
            return
        for child in imports(source.read_text(encoding='utf-8')):
            visit(child)
        pipeline.build_interface(module,'queue-'+module.split('.')[-1])
    for module in imports(candidate.read_text(encoding='utf-8')):
        visit(module)

def order(path):
    # Data identities have no game-theorem dependency and can fill idle slots.
    if path.stem.startswith('final-calculations'):
        return (1,path.stem)
    if path.stem.startswith('block'):
        return (0,path.stem)
    return (2,{'catalog':0,'certificate':1,'empty-force':2}.get(path.stem,3))

def dependency_order(paths):
    """Put each proof's unpublished theorem interfaces before its clients."""
    modules={}
    dependencies={}
    for path in paths:
        spec=json.loads(path.read_text(encoding='utf-8'))
        modules['Theorems.Thm_'+spec['theorem_name'].replace('.','_')]=path
        dependencies[path]=imports((ROOT/spec['proof_file']).read_text(encoding='utf-8'))
    visiting=set()
    visited=set()
    result=[]
    def visit(path):
        if path in visited:
            return
        if path in visiting:
            raise RuntimeError('Cyclic publication dependency: '+path.stem)
        visiting.add(path)
        for module in dependencies[path]:
            if module in modules:
                visit(modules[module])
        visiting.remove(path)
        visited.add(path)
        result.append(path)
    for path in sorted(paths,key=order):
        visit(path)
    return result

def check_adapter(path):
    obj=json.loads(path.read_text(encoding='utf-8'))
    candidate=ROOT/obj['proof_file']
    previous=read().get('proof:'+obj['theorem_name'],{})
    digest=hashlib.sha256(candidate.read_text(encoding='utf-8').encode()).hexdigest()
    if previous.get('status')=='PENDING' and previous.get('source_sha256')==digest:
        print('RESUME CHECKED PENDING',path.stem,flush=True)
    else:
        ensure_interfaces(candidate)
        pipeline.run_checked([str(pipeline.LEAN),'-DautoImplicit=false',str(candidate)],path.stem+'-submission')
    return path

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    if not local_completion.unchanged():
        raise RuntimeError('Actual closed proof differs from its completed audit')
    specs=[]
    for path in OUT.glob('*.json'):
        obj=json.loads(path.read_text(encoding='utf-8'))
        name=obj.get('theorem_name','')
        if not name.startswith('OAI.Snaky21.') or 'proof_file' not in obj:
            continue
        previous=read().get('proof:'+name,{})
        digest=hashlib.sha256((ROOT/obj['proof_file']).read_text(encoding='utf-8').encode()).hexdigest()
        if previous.get('status') in ('ACCEPTED','SKETCH_ACCEPTED') and previous.get('source_sha256')==digest:
            continue
        specs.append(path)
    specs=dependency_order(specs)
    print('RESUME',len(specs),'proof adapters; four API jobs, one local checker',flush=True)
    checked=[]
    ready=[]
    active={}
    failures=[]
    checking=None
    with ThreadPoolExecutor(max_workers=4) as executor, ThreadPoolExecutor(max_workers=1) as checker:
        active[executor.submit(definitions)]=('definitions',None)
        while specs or checked or ready or active or checking:
            if checking is not None and checking.done():
                try:
                    checked.append(checking.result())
                except Exception as error:
                    failures.append({'item':'local-check','type':type(error).__name__,'message':str(error)})
                    print('ERROR local-check',str(error),flush=True)
                checking=None
            for future in list(active):
                if future.done():
                    kind,path=active.pop(future)
                    label='definitions' if path is None else kind+':'+path.stem
                    try:
                        result=future.result()
                        if kind=='statement':
                            ready.append((path,result))
                    except Exception as error:
                        failures.append({'item':label,'type':type(error).__name__,'message':str(error)})
                        print('ERROR',label,str(error),flush=True)
            if failures:
                STOP.set()
                (HERE/'verification'/'queue-errors.json').write_text(json.dumps(failures,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
                # Do not launch descendants of a failed dependency.
                raise RuntimeError('Publication queue has a saved failed item')
            for path,target in list(ready):
                if len(active)>=4:
                    break
                obj=json.loads(path.read_text(encoding='utf-8'))
                candidate=ROOT/obj['proof_file']
                if missing_modules(imports(candidate.read_text(encoding='utf-8'))):
                    continue
                ready.remove((path,target))
                active[executor.submit(proof_worker,path,target)]=('proof',path)
            for path in list(checked):
                if len(active)>=4:
                    break
                obj=json.loads(path.read_text(encoding='utf-8'))
                # Publishing the statement returns its worker immediately;
                # waiting for proof imports only occupies the ready list.
                if missing_modules(imports(obj['preamble'])):
                    continue
                checked.remove(path)
                active[executor.submit(statement_worker,path)]=('statement',path)
            if checking is None and specs and len(checked)+len(ready)<8:
                path=specs.pop(0)
                checking=checker.submit(check_adapter,path)
            time.sleep(1)
    # SKETCH_ACCEPTED is an honest intermediate state. Every target must now
    # auto-resolve to Proved before the original root is submitted again.
    for attempt in range(30):
        states={}
        for key,value in read().items():
            if key.startswith('theorem:') and value.get('theorem_id'):
                item=publish.request('GET','/theorems/'+value['theorem_id'],token())
                states[key]={'theorem_id':value['theorem_id'],'status':item['status']}
        (HERE/'verification'/'queue-targets.json').write_text(json.dumps(states,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
        open_names=[key for key,value in states.items() if value['status']!='Proved']
        if not open_names:
            break
        print('WAIT FOR AUTO-RESOLVE',open_names,flush=True)
        time.sleep(10)
    else:
        raise RuntimeError('Unresolved theorem targets remain')
    spec=json.loads((OUT/'main.json').read_text(encoding='utf-8'))
    candidate=ROOT/spec['proof_file']
    ensure_interfaces(candidate)
    pipeline.run_checked([str(pipeline.LEAN),'-DautoImplicit=false',str(candidate)],'main-submission')
    THREAD.allowed={'proof:'+spec['theorem_name']}
    publish.submit(spec['theorem_id'],candidate,spec['explanation'],token(),read(),spec['theorem_name'],resubmit_sketch=True)
    result=subprocess.run([sys.executable,'-B',str(HERE/'finalize.py')],cwd=ROOT,env=pipeline.environment())
    if result.returncode:
        raise RuntimeError('Final independent audit failed')
    print('COMPLETE: original mission Proved; account attribution and actual proof audited',flush=True)

if __name__=='__main__':
    main()
