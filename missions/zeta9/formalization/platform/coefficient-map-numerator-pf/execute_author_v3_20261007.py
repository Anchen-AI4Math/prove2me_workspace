"""Versioned explicit-Python/absolute-input author executor; no import-time Lean."""
from pathlib import Path
import os, subprocess, time, sys
sys.dont_write_bytecode=True
import prepare as p
import execute_oracles as original
import retain_actual_inputs
PYTHON='C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe'

def run(label,arguments):
    original.gate()
    assert os.environ.get('LEAN_NUM_THREADS')=='1' and os.environ.get('LAKE_JOBS')=='1'
    receipt_path=p.OUT/'compile-receipt.json'
    receipt=p.load(receipt_path)
    helper=p.PROJECT/'lean_call_v3_20261007.py'
    if not helper.exists():
        p.write(helper,(p.PROJECT/'lean_call.py').read_text().replace('allowed.append(raw)','allowed.append(str(path))'))
    assert helper.read_text()==(p.PROJECT/'lean_call.py').read_text().replace('allowed.append(raw)','allowed.append(str(path))')
    inputs=[p.binding(p.PROJECT/name) for name in ['lakefile.lean','lean-toolchain','lake-manifest.json','lean_call.py','lean_call_v3_20261007.py']]
    inputs.append(p.binding(Path(__file__)))
    absolute=[]
    for argument in arguments:
        if str(argument).endswith(('.lean','.olean')):
            candidate=p.PROJECT/argument
            absolute.append(str(candidate))
            if str(argument).endswith('.lean'):
                inputs.append(p.binding(candidate))
        else: absolute.append(argument)
    previous=next((r for r in reversed(receipt['rows']) if r['label']==label and r['exit_code']==0 and r['input_bindings']==inputs),None)
    if previous is not None:
        for row in previous['input_bindings']+previous['output_bindings']+[previous[k] for k in ['stdout','stderr','log','exit_file','selected_paths']]:
            path=p.TASK/row['task_relative']
            assert path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256']
        print(label+': retained actual success',flush=True)
        return
    attempt=1+sum(r['label']==label for r in receipt['rows'])
    folder=p.OUT/'actual-runs'/(label+'-'+str(attempt).zfill(2))
    folder.mkdir(parents=True,exist_ok=False)
    environment=dict(os.environ)
    environment.pop('LEAN_PATH',None);environment.pop('LEAN_SRC_PATH',None)
    environment['NUMERATOR_PF_RUN_LABEL']=label
    environment['NUMERATOR_PF_RUN_PATHS_RECEIPT']=str(folder/'selected-paths.json')
    command=['lake','env',PYTHON,str(helper),'lean','-j1','--root='+str(p.PROJECT)]+absolute
    started=time.monotonic()
    result=subprocess.run(command,cwd=p.PROJECT,env=environment,capture_output=True)
    for name,data in [('stdout.log',result.stdout),('stderr.log',result.stderr),
                      ('combined.log',result.stdout+result.stderr),('exit.txt',str(result.returncode)+'\n')]:
        p.write(folder/name,data)
    outputs=[]
    if '-o' in arguments:
        obj=p.PROJECT/arguments[arguments.index('-o')+1]
        if obj.exists():outputs.extend(sorted(obj.parent.glob(obj.name+'*')))
    selected=folder/'selected-paths.json'
    row=dict(label=label,attempt=attempt,command=command,cwd=str(p.PROJECT),
        exit_code=result.returncode,elapsed_seconds=round(time.monotonic()-started,3),
        input_bindings=inputs,output_bindings=[p.binding(path) for path in outputs],
        stdout=p.binding(folder/'stdout.log'),stderr=p.binding(folder/'stderr.log'),
        log=p.binding(folder/'combined.log'),exit_file=p.binding(folder/'exit.txt'),
        selected_paths=p.binding(selected) if selected.exists() else None,
        failure_retained=result.returncode!=0,
        actual_executor_sha256=p.sha(Path(__file__)),actual_executor_binding=p.binding(Path(__file__)),
        actual_environment={key:environment[key] for key in ['LEAN_NUM_THREADS','LAKE_JOBS']},
        original_executor_unchanged=p.binding(p.OUT/'execute_oracles.py'))
    retain_actual_inputs.retain(row,folder)
    receipt['rows'].append(row);p.dump(receipt_path,receipt)
    p.write(p.OUT/(label+'.log'),result.stdout+result.stderr)
    p.write(p.OUT/(label+'-exit.txt'),str(result.returncode)+'\n')
    print(label+': actual exit '+str(result.returncode),flush=True)
    if result.returncode:
        print((result.stdout+result.stderr).decode('utf-8',errors='replace'),flush=True)
    assert result.returncode==0,'Actual failed versioned attempt retained.'
    paths=p.load(selected)
    for key in ['LEAN_PATH','LEAN_SRC_PATH']:
        assert all((p.PROJECT/Path(raw)).resolve().is_relative_to(p.PROJECT.resolve()) or
                   (p.PROJECT/Path(raw)).resolve().is_relative_to((p.ROOT/'.lake/packages').resolve())
                   for raw in paths[key]['filtered'])
    original.gate()

def compile_module(label,module):
    obj='b/lib/lean/'+module.replace('.','/')+'.olean'
    (p.PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
    run(label,['-o',obj,module.replace('.','/')+'.lean'])

def main():
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--lane-granted',action='store_true',required=True)
    parser.parse_args()
    grant=p.load(p.OUT/'lane1-resume-grant-2026-10-07.json')
    assert grant['explicit_new_parent_lane1_resume_granted'] and grant['lane']==1
    os.environ['LEAN_NUM_THREADS']='1';os.environ['LAKE_JOBS']='1'
    print('reference actual exit0 and context-verified own resolver retained; no Lean rerun.',flush=True)
    plan=p.load(p.OUT/'author-controls-plan-2026-10-07.json')
    compile_module('author-native-reachable-v1',plan['native_control'])
    for row in plan['staged_controls']:
        compile_module('author-staged-'+row['label'].split('_')[1]+'-v1',row['label'])

if __name__=='__main__': main()
