"""Root-granted serial actual author executions, with complete retained records."""
from pathlib import Path
import argparse, os, subprocess, time, sys
sys.dont_write_bytecode=True
import prepare_native as p

def gate():
    assert p.load(p.OUT/'lane1-grant-2026-10-07.json')['Root_explicit_grant']
    for name,expected in p.EXPECTED.items():
        assert p.sha(p.TASK/'formalization'/(name+'.lean'))==expected
    state=p.load(p.OUT/'preparation-state.json')
    for row in state['configs']:
        path=p.TASK/row['task_relative']
        assert path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256']
    junction=p.PROJECT/'.lake/packages'
    assert junction.is_junction() and junction.resolve()==(p.ROOT/'.lake/packages').resolve()

def run(label,arguments):
    gate()
    receipt_path=p.OUT/'compile-receipt.json'
    receipt=p.load(receipt_path) if receipt_path.exists() else dict(role='native actual phase AUTHOR',project='.rt/aph1',
        initially_fresh=True,foreign_proof_objects_borrowed=False,Root_proof_fallback=False,rows=[])
    inputs=[p.binding(p.PROJECT/n) for n in ['lakefile.lean','lake-manifest.json','lean-toolchain','leaf.py']]
    inputs.append(p.binding(Path(__file__)))
    if label.startswith('control-'):
        for module in p.EXPECTED:
            relative='missions/zeta9/formalization/'+module
            inputs.append(p.binding(p.PROJECT/(relative+'.lean')))
            obj=p.PROJECT/('b/lib/lean/'+relative+'.olean')
            assert obj.exists(), 'Controls require previously SOURCE-built own objects'
            for path in sorted(obj.parent.glob(obj.name+'*')):
                inputs.append(p.binding(path))
    absolute=[]
    for argument in arguments:
        if str(argument).endswith(('.lean','.olean')):
            path=p.PROJECT/argument
            absolute.append(str(path))
            if str(argument).endswith('.lean'):inputs.append(p.binding(path))
        else:absolute.append(argument)
    prior=next((r for r in reversed(receipt['rows']) if r['label']==label and r['exit_code']==0 and r['input_bindings']==inputs),None)
    if prior is not None:
        for row in prior['output_bindings']+[prior[k] for k in ['stdout','stderr','log','exit_file','selected_paths']]:
            path=p.TASK/row['task_relative'];assert path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256']
        print(label+': retained same-batch actual success',flush=True);return
    attempt=1+sum(r['label']==label for r in receipt['rows'])
    folder=p.OUT/'actual-runs'/(label+'-'+str(attempt).zfill(2));folder.mkdir(parents=True,exist_ok=False)
    snapshots=[]
    for i,b in enumerate(inputs):
        dst=folder/'inputs'/(str(i).zfill(3)+'.bin');p.write(dst,(p.TASK/b['task_relative']).read_bytes())
        snapshots.append(dict(original_binding=b,snapshot_binding=p.binding(dst)))
    env=dict(os.environ);env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
    env['LEAN_NUM_THREADS']='1';env['LAKE_JOBS']='1'
    env['ACTUAL_PHASE_PATH_RECEIPT']=str(folder/'selected-paths.json')
    command=['lake','env',p.PYTHON,str(p.PROJECT/'leaf.py'),'lean','-j1','--root='+str(p.PROJECT)]+absolute
    started=time.monotonic();result=subprocess.run(command,cwd=p.PROJECT,env=env,capture_output=True)
    for name,data in [('stdout.log',result.stdout),('stderr.log',result.stderr),
                      ('combined.log',result.stdout+result.stderr),('exit.txt',str(result.returncode)+'\n')]:p.write(folder/name,data)
    outputs=[]
    if '-o' in arguments:
        obj=p.PROJECT/arguments[arguments.index('-o')+1]
        if obj.exists():outputs.extend(sorted(obj.parent.glob(obj.name+'*')))
    kept=[]
    for i,path in enumerate(outputs):
        dst=folder/'outputs'/(str(i).zfill(3)+'.bin');p.write(dst,path.read_bytes())
        kept.append(dict(original_binding=p.binding(path),snapshot_binding=p.binding(dst)))
    paths=folder/'selected-paths.json'
    row=dict(label=label,attempt=attempt,command=command,cwd=str(p.PROJECT),actual_environment={k:env[k] for k in ['LEAN_NUM_THREADS','LAKE_JOBS']},
        elapsed_seconds=round(time.monotonic()-started,3),exit_code=result.returncode,
        input_bindings=inputs,retained_inputs=snapshots,output_bindings=[p.binding(x) for x in outputs],retained_outputs=kept,
        stdout=p.binding(folder/'stdout.log'),stderr=p.binding(folder/'stderr.log'),log=p.binding(folder/'combined.log'),
        exit_file=p.binding(folder/'exit.txt'),selected_paths=p.binding(paths) if paths.exists() else None,
        failed_attempt_retained=result.returncode!=0)
    receipt['rows'].append(row);p.dump(receipt_path,receipt)
    print(label+': actual exit '+str(result.returncode),flush=True)
    if result.returncode:print('\n'.join(line for line in (result.stdout+result.stderr).decode('utf-8',errors='replace').splitlines() if not line.startswith('AP_RECORD|')),flush=True)
    assert result.returncode==0,'Actual failed attempt fully retained; no PASS.'
    actual=p.load(paths)
    for key in ['LEAN_PATH','LEAN_SRC_PATH']:
        assert all((p.PROJECT/Path(raw)).resolve().is_relative_to(p.PROJECT.resolve()) or
                   (p.PROJECT/Path(raw)).resolve().is_relative_to((p.ROOT/'.lake/packages').resolve()) for raw in actual[key]['filtered'])
    gate()

def compile_module(label,module):
    obj='b/lib/lean/'+module.replace('.','/')+'.olean'
    (p.PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
    run(label,['-o',obj,module.replace('.','/')+'.lean'])

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    q=argparse.ArgumentParser();q.add_argument('--lane-granted',action='store_true',required=True)
    q.add_argument('--phase',choices=['source','types','kernel','boundary'],default='source');a=q.parse_args()
    if a.phase=='source':
        run('runtime-version',['--version'])
        compile_module('native-base-v1','missions.zeta9.formalization.AnalyticPhase')
        compile_module('native-upper-v1','missions.zeta9.formalization.AnalyticPhaseUpperBound')
    elif a.phase=='types':compile_module('control-types-v1','APTypes')
    elif a.phase=='kernel':compile_module('control-kernel-v1','APKernel')
    else:compile_module('control-boundary-v1','APBoundary')
if __name__=='__main__':main()
