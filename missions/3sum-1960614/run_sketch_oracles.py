"""Supervised, resumable Stage 2 extraction with the official Lean sketch oracle.

All declaration spans and references come from Lean. This runner only selects
files, caches exact source/tool fingerprints, and checks JSON/exit status.
"""
from concurrent.futures import ThreadPoolExecutor,as_completed
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import shutil
import threading
import time
from contextlib import contextmanager
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
VER=HERE/'verification'
model_only='--model' in sys.argv
OUT=VER/('model-sketch-oracles' if model_only else 'sketch-oracles')
OUT.mkdir(exist_ok=True)
plan=json.loads((VER/('model-upload-plan.json' if model_only else 'machine-upload-plan.json')).read_text(encoding='utf-8'))
tool=ROOT/'scripts/extract_sketch_info.lean'
toolhash=hashlib.sha256(tool.read_bytes()).hexdigest()
lake=Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake.exe'
env=os.environ.copy()
env['LEAN_NUM_THREADS']='2'
workers=int(sys.argv[1]) if len(sys.argv)>1 else 1
assert 1<=workers<=2
mods=plan['participating_modules']
resource_file=VER/('model-oracle-resources.json' if model_only else 'sketch-oracle-resources.json')
resource_lock=threading.Lock()
active_processes=0

@contextmanager
def process_slot():
    global active_processes
    while True:
        try:
            limit=(json.loads(resource_file.read_text(encoding='utf-8-sig'))['max_live_lean_processes']
                   if resource_file.exists() else workers)
            assert isinstance(limit,int) and 0<=limit<=workers
        except json.JSONDecodeError:
            time.sleep(1)
            continue
        with resource_lock:
            if active_processes<limit:
                active_processes+=1
                break
        time.sleep(1)
    try:
        yield
    finally:
        with resource_lock:active_processes-=1
def extract(module):
    source=HERE/'machine/lean'/Path(*module.split('.')).with_suffix('.lean')
    assert source.is_file(),source
    sourcehash=hashlib.sha256(source.read_bytes()).hexdigest()
    name=module.replace('.','_')
    facts=OUT/(name+'.jsonl'); err=OUT/(name+'.stderr.txt'); stamp=OUT/(name+'.receipt.json')
    if model_only and not stamp.exists():
        shared=VER/'sketch-oracles'
        shared_stamp=shared/stamp.name
        shared_facts=shared/facts.name
        if shared_stamp.exists() and shared_facts.exists():
            old=json.loads(shared_stamp.read_text(encoding='utf-8'))
            if old.get('source_sha256')==sourcehash and old.get('oracle_sha256')==toolhash and old.get('exit_code')==0:
                shutil.copyfile(shared_facts,facts)
                old['facts_path']=facts.relative_to(ROOT).as_posix()
                stamp.write_text(json.dumps(old,indent=2)+'\n',encoding='utf-8')
    if stamp.exists():
        old=json.loads(stamp.read_text(encoding='utf-8'))
        if old.get('source_sha256')==sourcehash and old.get('oracle_sha256')==toolhash and old.get('exit_code')==0 and facts.exists():
            return module,'cached',old['declaration_count']
    with process_slot(),facts.open('w',encoding='utf-8') as stdout,err.open('w',encoding='utf-8') as stderr:
        result=subprocess.run([str(lake),'env','lean','--run',str(tool),str(source)],
            cwd=ROOT,env=env,stdout=stdout,stderr=stderr)
    declarations=0
    if result.returncode==0:
        for line in facts.read_text(encoding='utf-8').splitlines():
            if not line.strip():continue
            row=json.loads(line)
            assert row['kind'] in ('decl','ref'),row
            declarations+=row['kind']=='decl'
    receipt=dict(module=module,source_sha256=sourcehash,oracle_sha256=toolhash,
        exit_code=result.returncode,declaration_count=declarations,
        facts_path=facts.relative_to(ROOT).as_posix())
    stamp.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    if result.returncode: raise RuntimeError(module+' failed; inspect '+str(err))
    return module,'extracted',declarations
print('Stage 2 modules:',len(mods),'workers:',workers,flush=True)
failed=[]
with ThreadPoolExecutor(max_workers=workers) as pool:
    futures={pool.submit(extract,m):m for m in mods}
    for n,f in enumerate(as_completed(futures),1):
        try:
            module,status,count=f.result()
            print(n,'/',len(mods),status,module,'declarations',count,flush=True)
        except Exception as exc:
            failed.append(str(exc))
            print('FAILED',futures[f],str(exc),flush=True)
summary=dict(module_count=len(mods),failed=failed,all_succeeded=not failed,oracle_sha256=toolhash)
(VER/('model-sketch-oracle-summary.json' if model_only else 'sketch-oracle-summary.json')).write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print('Stage 2 completed; failed:',len(failed),flush=True)
sys.exit(bool(failed))
