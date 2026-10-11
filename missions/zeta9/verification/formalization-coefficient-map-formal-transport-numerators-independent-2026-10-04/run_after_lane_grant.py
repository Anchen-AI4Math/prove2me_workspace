"""Prepared runner. DO NOT EXECUTE until Root explicitly grants a free Lean lane.
This file was written offline; merely preparing it performs zero compiler calls.
Each later invocation executes one genuine call and retains failures separately.
"""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys, time

OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/ni1'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,d):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(d if isinstance(d,bytes) else d.encode('utf8'))
def bind(p):return {'root_relative':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
def dump(p,d):write(p,json.dumps(d,indent=2)+'\n')
def verify(rows):
    for r in rows:
        p=ROOT/r['root_relative']
        assert p.is_file() and p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)

def gate():
    prep=load(OUT/'preparation-verification.json')
    verify(prep['author_control_bindings']+prep['verified_author_bindings']+prep['runtime_bindings'])
    for row in prep['source_copies']:verify([row['original'],row['own_copy']])
    manifest=load(OUT/'preparation-manifest.json')
    verify(manifest['immutable_prepared_files'])
    assert (PROJECT/'.lake/packages').is_junction()
    assert (PROJECT/'.lake/packages').resolve()==(ROOT/'.lake/packages').resolve()
    return prep

def run(mode,module,file,grant):
    assert grant=='ROOT_EXPLICIT_LANE_GRANT', 'A free compiler lane must first be granted by Root'
    prep=gate()
    receipt=OUT/'actual-execution-receipt.json'
    records=load(receipt) if receipt.exists() else {'rows':[], 'fresh_source_modules_required':17,
        'foreign_author_Root_independent_or_previous_PF_objects_reused':0}
    attempt=OUT/'actual'/('r'+str(len(records['rows'])+1).zfill(2))
    attempt.mkdir(parents=True)
    modules=[r['module'] for r in prep['source_copies']]
    obj=None
    if mode=='source':
        assert module in modules
        source=PROJECT/Path(module.replace('.','/')).with_suffix('.lean')
        obj=PROJECT/'b/lib/lean'/Path(module.replace('.','/')).with_suffix('.olean')
    elif mode=='alias':
        assert module in ['IndependentDataValues','IndependentWholeTypes']
        source=PROJECT/(module+'.lean')
        obj=PROJECT/'b/lib/lean'/(module+'.olean')
    elif mode=='runtime':source=PROJECT/'lean-toolchain'
    else:
        source=PROJECT/file
        assert source.is_file() and source.resolve().is_relative_to(PROJECT.resolve())
    write(attempt/source.name,source.read_bytes())
    if obj is not None:
        assert not obj.exists(), 'Never overwrite a successful proof object in this independent review'
        obj.parent.mkdir(parents=True,exist_ok=True)
        assert len(str(obj))+64<=259
        command=['lake','env','lean','-o',str(obj),str(source)]
    elif mode=='runtime':command=['lake','env','lean','--version']
    else:command=['lake','env','lean']+(['--run'] if mode=='resolver' else [])+[str(source)]
    env=dict(os.environ)
    for key in ['LEAN_PATH','LEAN_SRC_PATH']:env.pop(key,None)
    package_names=[p['name'] for p in load(PROJECT/'lake-manifest.json')['packages']]
    paths=[str(PROJECT/'b/lib/lean')]+[str(PROJECT/'.lake/packages'/p/'.lake/build/lib/lean') for p in package_names]
    # Only own proof objects plus fixed Mathlib/dependency package caches.
    env['LEAN_PATH']=os.pathsep.join(paths)
    env['LEAN_NUM_THREADS']='1';env['LAKE_JOBS']='1'
    start=time.monotonic();log=attempt/'run.log';exitfile=attempt/'exit.txt'
    with log.open('wb') as f:
        result=subprocess.run(command,cwd=PROJECT,env=env,stdout=f,stderr=subprocess.STDOUT)
    write(exitfile,str(result.returncode)+'\n')
    row={'mode':mode,'module':module,'file':file,'actual_exit':result.returncode,
        'elapsed_seconds':round(time.monotonic()-start,3),'command':command,'cwd':str(PROJECT),
        'input':bind(attempt/source.name),'log':bind(log),'exit_file':bind(exitfile),
        'explicit_filtered_LEAN_PATH':paths,'foreign_proof_objects_reused':0}
    if obj is not None and result.returncode==0:
        write(attempt/'compiled.olean',obj.read_bytes())
        row['object']=bind(obj);row['retained_object']=bind(attempt/'compiled.olean')
    records['rows'].append(row);dump(receipt,records)
    gate()
    print(mode,module or file,'actual exit',result.returncode,'elapsed',row['elapsed_seconds'],flush=True)
    return result.returncode

if __name__=='__main__':
    sys.stdout.reconfigure(encoding='utf8')
    p=argparse.ArgumentParser()
    p.add_argument('mode',choices=['runtime','source','alias','audit','resolver'])
    p.add_argument('--module',default='');p.add_argument('--file',default='')
    p.add_argument('--lane-grant',required=True)
    a=p.parse_args()
    raise SystemExit(run(a.mode,a.module,a.file,a.lane_grant))
