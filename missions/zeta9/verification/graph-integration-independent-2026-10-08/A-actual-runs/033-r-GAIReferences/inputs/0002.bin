from __future__ import annotations
from pathlib import Path
import argparse,json,os,subprocess,sys,time
from prepare_A_independent import OUT,TASK,ROOT,PROJECT,GRANT,load,bind,pathof,verify

sys.dont_write_bytecode=True
PYTHON='C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe'
PREP=OUT/'A-source-preparation-v2.json'
RECEIPT=OUT/'A-actual-independent-calls.json'
def dump(p,j):p.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def gate():
    g=load(GRANT);assert g['Root_explicit_grant'] and g['lane']==2 and g['owner']=='graph_integration_audit_1008'
    p=load(PREP);verify(p['Root_grant']);verify(p['author_report']);verify(p['Root_pin']);verify(p['pure_design']);verify(p['personal_author_stock_preflight'])
    assert p['private_project']=='.rt/gaui1008' and p['project_initially_absent'] and p['foreign_mathematical_objects_copied']==0
    for b in p['source_bindings']:verify(b)
    for c in p['contexts'].values():
        junction=TASK/c['context']/'.lake/packages';assert junction.is_junction() and junction.resolve()==(ROOT/'.lake/packages').resolve()
    return p
def run(tag,module=None):
    p=gate();context=PROJECT/tag
    calls=load(RECEIPT) if RECEIPT.exists() else dict(role='independent',owner='graph_integration_audit_1008',lane=2,project='.rt/gaui1008',foreign_math_objects=0,rows=[])
    idx=len(calls['rows'])+1;label=module.replace('.','-') if module else 'runtime'
    folder=OUT/'A-actual-runs'/f'{idx:03}-{tag}-{label}';folder.mkdir(parents=True,exist_ok=False)
    inputs=[bind(PREP),bind(GRANT),bind(Path(__file__))]+[bind(context/f) for f in ['lakefile.lean','lake-manifest.json','lean-toolchain','leaf.py']]
    args=['--version'];output=None
    if module:
        source=context/'src'/(module.replace('.','/')+'.lean');assert source.exists();inputs.append(bind(source))
        inputs += [bind(f) for f in sorted((context/'b/lib/lean').rglob('*')) if f.is_file()]
        output=context/'b/lib/lean'/(module.replace('.','/')+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
        args=['-o',str(output),str(source)]
    snapshots=[]
    for i,b in enumerate(inputs):
        f=folder/'inputs'/f'{i:04}.bin';f.parent.mkdir(exist_ok=True);f.write_bytes(pathof(b).read_bytes());snapshots.append(dict(original=b,snapshot=bind(f)))
    env=dict(os.environ)
    for k in ['LEAN_PATH','LEAN_SRC_PATH']:env.pop(k,None)
    env.update(LEAN_NUM_THREADS='1',LAKE_JOBS='1',GAI_PATH_RECEIPT=str(folder/'selected-paths.json'))
    command=['lake','env',PYTHON,str(context/'leaf.py'),'lean','-j1','--root='+str(context/'src')]+args
    dump(folder/'intent.json',dict(index=idx,tag=tag,module=module,command=command,cwd=str(context),started_epoch=time.time(),SOURCE_inputs=inputs,not_terminal=True))
    print(f'{idx} {tag} {label}: starting actual fresh independent -j1',flush=True);started=time.monotonic()
    with (folder/'stdout.log').open('wb') as out,(folder/'stderr.log').open('wb') as err:
        result=subprocess.run(command,cwd=context,env=env,stdout=out,stderr=err)
    (folder/'exit.txt').write_text(str(result.returncode)+'\n',encoding='utf-8')
    outs=[];outsnap=[]
    if output and output.exists():
        for i,f in enumerate(sorted(output.parent.glob(output.name+'*'))):
            b=bind(f);s=folder/'outputs'/f'{i:04}.bin';s.parent.mkdir(exist_ok=True);s.write_bytes(f.read_bytes());outs.append(b);outsnap.append(dict(original=b,snapshot=bind(s)))
    selected=folder/'selected-paths.json';paths=load(selected) if selected.exists() else None
    if paths:
        for k in ['LEAN_PATH','LEAN_SRC_PATH']:
            for raw in paths[k]['filtered']:
                d=Path(raw).resolve();assert d.is_relative_to(context.resolve()) or d.is_relative_to((ROOT/'.lake/packages').resolve()),raw
        assert paths['actual_environment']=={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'}
    row=dict(index=idx,tag=tag,module=module,command=command,cwd=str(context),exit_code=result.returncode,elapsed_seconds=time.monotonic()-started,
        actual_environment={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'},input_bindings=inputs,input_snapshots=snapshots,output_bindings=outs,output_snapshots=outsnap,
        stdout=bind(folder/'stdout.log'),stderr=bind(folder/'stderr.log'),exit_file=bind(folder/'exit.txt'),selected_paths=bind(selected) if selected.exists() else None,failed_attempt_retained=result.returncode!=0)
    calls['rows'].append(row);dump(RECEIPT,calls);dump(folder/'terminal-receipt.json',row)
    print(f'{idx} {tag} {label}: actual exit {result.returncode}',flush=True)
    if result.returncode:
        print((folder/'stdout.log').read_text(encoding='utf-8',errors='replace')[-16000:],flush=True)
        print((folder/'stderr.log').read_text(encoding='utf-8',errors='replace')[-16000:],flush=True)
    gate();return result.returncode
def main():
    sys.stdout.reconfigure(encoding='utf-8');ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['all','one','resume']);ap.add_argument('--tag');ap.add_argument('--module');args=ap.parse_args();p=gate()
    if args.mode=='one':assert args.tag and args.module;sys.exit(run(args.tag,args.module))
    if args.mode=='all':assert not RECEIPT.exists(),'Do not restart successful actual calls';sys.exit(1) if run('n') else None
    done={(r['tag'],r['module']) for r in load(RECEIPT)['rows'] if r['exit_code']==0}
    for tag,order in p['compile_orders'].items():
        for module in order:
            if (tag,module) not in done:
                if run(tag,module):sys.exit(1)
    print('All initial independent SOURCE and controls terminal0; freeze still required.',flush=True)
if __name__=='__main__':main()
