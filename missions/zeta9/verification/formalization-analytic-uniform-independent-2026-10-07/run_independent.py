"""Granted independent serial SOURCE/control compilation; retain each actual call."""
from __future__ import annotations
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
TASK=OUT.parents[1]
ROOT=TASK.parents[1]
PROJECT=TASK/'.rt/aui1'
PYTHON='C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe'

def load(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def dump(p,j): p.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def bind(p):
    data=p.read_bytes()
    base=TASK if p.is_relative_to(TASK) else ROOT
    return {'task_relative' if base==TASK else 'root_relative':p.relative_to(base).as_posix(),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
def gate():
    grant=load(OUT/'Root-native-independent-lane1-grant.json')
    assert grant['Root_explicit_grant'] and grant['lane']==1 and grant['owner']=='analytic_uniform_independent_1007'
    assert grant['fresh_private_project']=='.rt/aui1'
    prep=load(OUT/'source-preparation.json')
    for r in prep['source_bindings']:
        assert bind(TASK/r['task_relative'])==r
    personal=load(OUT/'personal-author-and-import-rehash.json')
    assert personal['mismatches']==0 and personal['Lean_calls']==0
    assert personal['author_report']['sha256']==grant['author_report_sha256']
    assert personal['root_author_pin']['sha256']==grant['Root_author_full_binding_rehash_sha256']
    return prep
def config():
    junction=PROJECT/'.lake/packages'
    if junction.exists():
        assert junction.is_junction() and junction.resolve()==(ROOT/'.lake/packages').resolve()
        return
    assert not list((PROJECT/'b/lib/lean').rglob('*.olean'))
    junction.parent.mkdir(exist_ok=True)
    command=['powershell','-NoProfile','-Command',"New-Item -ItemType Junction -Path '"+str(junction)+"' -Target '"+str(ROOT/'.lake/packages')+"' | Out-Null"]
    r=subprocess.run(command,capture_output=True)
    (OUT/'junction-stdout.log').write_bytes(r.stdout)
    (OUT/'junction-stderr.log').write_bytes(r.stderr)
    assert r.returncode==0,r.stderr
    assert junction.is_junction() and junction.resolve()==(ROOT/'.lake/packages').resolve()
    dump(OUT/'junction-config.json',{'status':'CONFIG_ONLY','junction':str(junction),'actual_target':str(junction.resolve()),'Lean_calls':0})
def run(label,module=None,controls=False):
    gate()
    receipt=OUT/'actual-independent-calls.json'
    data=load(receipt) if receipt.exists() else {'role':'independent','lane':1,'project':'.rt/aui1','foreign_math_objects':0,'Root_math_objects':0,'rows':[]}
    assert all(isinstance(r['exit_code'],int) for r in data['rows'])
    idx=len(data['rows'])+1
    folder=OUT/'actual-runs'/f'{idx:03}-{label}'
    folder.mkdir(parents=True,exist_ok=False)
    root=PROJECT/('controls' if controls else 'src')
    args=['--version']; output=None
    inputs=[bind(Path(__file__)),bind(OUT/'source-preparation.json'),bind(OUT/'personal-author-and-import-rehash.json'),bind(OUT/'Root-native-independent-lane1-grant.json')]
    inputs.extend(bind(PROJECT/n) for n in ('lakefile.lean','lake-manifest.json','lean-toolchain','leaf.py'))
    if module:
        source=root/(module.replace('.','/')+'.lean')
        inputs.append(bind(source))
        inputs.extend(bind(p) for p in sorted((PROJECT/'b/lib/lean').rglob('*.olean')))
        output=PROJECT/'b/lib/lean'/(module.replace('.','/')+'.olean')
        output.parent.mkdir(parents=True,exist_ok=True)
        args=['-o',str(output),str(source)]
    env=dict(os.environ)
    env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
    env['LEAN_NUM_THREADS']='1';env['LAKE_JOBS']='1'
    env['ACTUAL_ANALYTIC_PATH_RECEIPT']=str(folder/'selected-paths.json')
    command=['lake','env',PYTHON,str(PROJECT/'leaf.py'),'lean','-j1','--root='+str(root)]+args
    dump(folder/'running-intent.json',{'actual_command':command,'source_inputs':inputs,'started_epoch':time.time(),'not_terminal_receipt':True})
    print(label+': starting actual fresh independent SOURCE',flush=True)
    started=time.monotonic()
    with (folder/'stdout.log').open('wb') as out,(folder/'stderr.log').open('wb') as err:
        result=subprocess.run(command,cwd=PROJECT,env=env,stdout=out,stderr=err)
    (folder/'exit.txt').write_text(str(result.returncode)+'\n',encoding='utf-8')
    outputs=[]
    if output and output.exists():
        outputs=[bind(p) for p in sorted(output.parent.glob(output.name+'*'))]
    selected=folder/'selected-paths.json'
    paths=load(selected) if selected.exists() else None
    if paths:
        for k in ('LEAN_PATH','LEAN_SRC_PATH'):
            for raw in paths[k]['filtered']:
                p=Path(raw).resolve()
                assert p.is_relative_to(PROJECT.resolve()) or p.is_relative_to((ROOT/'.lake/packages').resolve()),p
    row={'index':idx,'label':label,'module':module,'command':command,'cwd':str(PROJECT),'exit_code':result.returncode,
         'elapsed_seconds':time.monotonic()-started,'actual_environment':{'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'},
         'input_bindings':inputs,'output_bindings':outputs,'stdout':bind(folder/'stdout.log'),'stderr':bind(folder/'stderr.log'),
         'exit_file':bind(folder/'exit.txt'),'selected_paths':bind(selected) if selected.exists() else None,'historical_failure_retained':result.returncode!=0}
    data['rows'].append(row);dump(receipt,data)
    dump(folder/'terminal-receipt.json',row)
    print(label+': actual exit '+str(result.returncode),flush=True)
    if result.returncode:
        print((folder/'stdout.log').read_text(encoding='utf-8',errors='replace')[-16000:],flush=True)
        print((folder/'stderr.log').read_text(encoding='utf-8',errors='replace')[-16000:],flush=True)
    gate()
    return result.returncode
def main():
    sys.stdout.reconfigure(encoding='utf-8')
    p=argparse.ArgumentParser();p.add_argument('mode',choices=['sources','controls','one']);p.add_argument('--module');p.add_argument('--control',action='store_true');q=p.parse_args()
    prep=gate();config()
    if q.mode=='sources':
        assert not (OUT/'actual-independent-calls.json').exists(),'Do not restart a completed or existing sources pipeline.'
        if run('runtime'):sys.exit(1)
        for r in prep['original_source_gates']:
            if run(r['module'].replace('.','_'),r['module']):sys.exit(1)
    elif q.mode=='controls':
        for m in ['AUExprDag','AUExprDagValidation','AURecords','AUKernel','AUBoundary','AUResolver']:
            if run(m,m,True):sys.exit(1)
    else:
        assert q.module
        sys.exit(run(q.module,q.module,q.control))
if __name__=='__main__':main()
