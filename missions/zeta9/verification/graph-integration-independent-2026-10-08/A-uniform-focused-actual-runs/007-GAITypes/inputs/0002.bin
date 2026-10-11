from __future__ import annotations
from pathlib import Path
import json,os,subprocess,sys,time
from prepare_A_independent import OUT,TASK,ROOT,load,bind,pathof,verify

sys.dont_write_bytecode=True
CONTEXT=TASK/'.rt/gaui1008/u2'
GRANT=TASK/'verification/graph-integration-root-2026-10-08/A-uniform-focused-independent-lane2-grant.json'
PYTHON='C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe'
PREP=OUT/'A-uniform-focused-source-preparation.json'
RECEIPT=OUT/'A-uniform-focused-actual-calls.json'

def dump(p,j):p.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

def gate():
    grant=load(GRANT);assert grant['Root_explicit_grant'] and grant['lane']==2 and grant['owner']=='graph_integration_audit_1008'
    prep=load(PREP)
    assert prep['private_project']=='.rt/gaui1008/u2' and prep['project_initially_absent'] and prep['all_foreign_math_objects_copied']==0
    for key in ['Root_grant','author_report','Root_pin','pure_design','original_source_preparation','complete_actual_stock_prefreeze']:verify(prep[key])
    for row in prep['source_bindings']:verify(row)
    junction=CONTEXT/'.lake/packages';assert junction.is_junction() and junction.resolve()==(ROOT/'.lake/packages').resolve()
    return prep

def run(module):
    prep=gate()
    calls=load(RECEIPT) if RECEIPT.exists() else dict(role='independent',owner='graph_integration_audit_1008',lane=2,project='.rt/gaui1008/u2',scope=prep['scope'],foreign_math_objects=0,rows=[])
    index=len(calls['rows'])+1
    folder=OUT/'A-uniform-focused-actual-runs'/f'{index:03}-{module.replace(".","-")}'
    folder.mkdir(parents=True,exist_ok=False)
    source=CONTEXT/'src'/(module.replace('.','/')+'.lean');assert source.exists()
    inputs=[bind(PREP),bind(GRANT),bind(Path(__file__))]+[bind(CONTEXT/f) for f in ['lakefile.lean','lake-manifest.json','lean-toolchain','leaf.py']]+[bind(source)]
    inputs += [bind(f) for f in sorted((CONTEXT/'b/lib/lean').rglob('*')) if f.is_file()]
    snapshots=[]
    for i,binding in enumerate(inputs):
        target=folder/'inputs'/f'{i:04}.bin';target.parent.mkdir(exist_ok=True);target.write_bytes(pathof(binding).read_bytes())
        snapshots.append(dict(original=binding,snapshot=bind(target)))
    output=CONTEXT/'b/lib/lean'/(module.replace('.','/')+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ)
    for k in ['LEAN_PATH','LEAN_SRC_PATH']:env.pop(k,None)
    env.update(LEAN_NUM_THREADS='1',LAKE_JOBS='1',GAI_PATH_RECEIPT=str(folder/'selected-paths.json'))
    command=['lake','env',PYTHON,str(CONTEXT/'leaf.py'),'lean','-j1','--root='+str(CONTEXT/'src'),'-o',str(output),str(source)]
    dump(folder/'intent.json',dict(index=index,module=module,command=command,cwd=str(CONTEXT),started_epoch=time.time(),SOURCE_inputs=inputs,not_terminal=True))
    print(f'{index} U2 {module}: actual independent -j1 starting',flush=True);started=time.monotonic()
    with (folder/'stdout.log').open('wb') as out,(folder/'stderr.log').open('wb') as err:
        result=subprocess.run(command,cwd=CONTEXT,env=env,stdout=out,stderr=err)
    (folder/'exit.txt').write_text(str(result.returncode)+'\n',encoding='utf-8')
    outputs=[];output_snapshots=[]
    if output.exists():
        for i,f in enumerate(sorted(output.parent.glob(output.name+'*'))):
            binding=bind(f);target=folder/'outputs'/f'{i:04}.bin';target.parent.mkdir(exist_ok=True);target.write_bytes(f.read_bytes())
            outputs.append(binding);output_snapshots.append(dict(original=binding,snapshot=bind(target)))
    selected=folder/'selected-paths.json';paths=load(selected) if selected.exists() else None
    if paths:
        for k in ['LEAN_PATH','LEAN_SRC_PATH']:
            for raw in paths[k]['filtered']:
                p=Path(raw).resolve();assert p.is_relative_to(CONTEXT.resolve()) or p.is_relative_to((ROOT/'.lake/packages').resolve())
        assert paths['actual_environment']=={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'}
    row=dict(index=index,module=module,command=command,cwd=str(CONTEXT),exit_code=result.returncode,elapsed_seconds=time.monotonic()-started,
        actual_environment={'LEAN_NUM_THREADS':'1','LAKE_JOBS':'1'},input_bindings=inputs,input_snapshots=snapshots,output_bindings=outputs,output_snapshots=output_snapshots,
        stdout=bind(folder/'stdout.log'),stderr=bind(folder/'stderr.log'),exit_file=bind(folder/'exit.txt'),selected_paths=bind(selected) if selected.exists() else None,failed_attempt_retained=result.returncode!=0)
    calls['rows'].append(row);dump(RECEIPT,calls);dump(folder/'terminal-receipt.json',row)
    print(f'{index} U2 {module}: actual terminal {result.returncode}',flush=True)
    if result.returncode:
        print((folder/'stdout.log').read_text(encoding='utf-8',errors='replace')[-16000:],flush=True)
        print((folder/'stderr.log').read_text(encoding='utf-8',errors='replace')[-16000:],flush=True)
    gate();return result.returncode

def main():
    sys.stdout.reconfigure(encoding='utf-8');prep=gate()
    assert not RECEIPT.exists(),'Fresh U2 driver cannot overwrite or silently retry historical calls'
    for module in prep['compile_order']:
        if run(module):sys.exit(1)
    print('U2 all11 fresh independent SOURCE and controls terminal0; pure final freeze pending.',flush=True)

if __name__=='__main__':main()
