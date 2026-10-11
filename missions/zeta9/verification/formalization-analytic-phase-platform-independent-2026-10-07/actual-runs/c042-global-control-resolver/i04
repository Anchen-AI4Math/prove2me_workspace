from pathlib import Path
import json, os, re, subprocess, sys, time
import inspect_prepare as p
PY=r'C:\Users\anche\AppData\Local\Programs\Python\Python312\python.exe'

def gate():
    grant=p.load(p.OUT/'Root-platform-independent-lane2-grant.json')
    assert grant['Root_explicit_grant'] and grant['lane']==2 and grant['owner']=='parameter_author_recovery_1007'
    assert grant['role']=='Analytic Phase platform INDEPENDENT' and grant['serial_lean_j1_only']
    assert not grant['scope_shared_modules_API_writes_permitted']
    assert grant['author_report_sha256']==p.PLATFORM_AUTHOR_SHA and p.sha(p.BATCH/'author-audit.json')==p.PLATFORM_AUTHOR_SHA
    rootgate=p.TASK/grant['Root_author_rehash'];assert p.sha(rootgate)==grant['Root_author_rehash_sha256']
    prep=p.load(p.OUT/'source-preparation.json');p.check(prep['stable_files'])
    pure=p.load(p.OUT/'personal-author-complete-binding-rehash.json')
    assert pure['personally_stream_rehashed_all'] and pure['stable_bindings']==26180 and pure['mismatches']==0
    control=p.load(p.OUT/'control-preparation.json');p.check(control['source_bindings'])
    return prep

def configure(ctx):
    link=ctx/'.lake/packages';expected=p.ROOT/'.lake/packages'
    if not link.exists():
        link.parent.mkdir(parents=True,exist_ok=True)
        result=subprocess.run(['pwsh','-NoProfile','-Command','New-Item -ItemType Junction -Path "'+str(link)+'" -Target "'+str(expected)+'" | Out-Null'],capture_output=True)
        (p.OUT/('junction-'+ctx.name+'.log')).write_bytes(result.stdout+result.stderr);assert result.returncode==0
    assert link.is_junction() and link.resolve()==expected.resolve()

def own_dependencies(ctx,source,receipt,tag):
    result={};visiting=set()
    def visit(path):
        for module in re.findall(r'^import\s+([A-Za-z0-9_.]+)',path.read_text(encoding='utf-8'),re.M):
            local=ctx/(module.replace('.','/')+'.lean')
            if not local.is_file() or module in visiting:continue
            visiting.add(module);visit(local)
            row=next((r for r in reversed(receipt['rows']) if r['tag']==tag and r['module']==module and r['exit_code']==0),None)
            assert row is not None,'No own actual0 SOURCE receipt for '+tag+'/'+module
            p.check(row['input_bindings']+row['output_bindings']+row['evidence_bindings'])
            for binding in row['output_bindings']:result[str(p.resolve(binding).resolve()).casefold()]=binding
    if source:visit(ctx/source)
    return [result[key] for key in sorted(result)]

def run(tag,label,module=None,source=None):
    prep=gate();ctx=p.PROJECT/tag;configure(ctx)
    rp=p.OUT/'execution-receipt.json';receipt=p.load(rp) if rp.exists() else dict(role='Analytic Phase platform INDEPENDENT',rows=[])
    inputs=[p.bind(ctx/name) for name in ['lakefile.toml','lean-toolchain','lake-manifest.json','lean_call.py']]+[p.bind(p.OUT/'run_independent.py')]
    if source:inputs.append(p.bind(ctx/source))
    inputs+=own_dependencies(ctx,source,receipt,tag)
    old=next((r for r in reversed(receipt['rows']) if r['tag']==tag and r['label']==label and r['exit_code']==0 and r['input_bindings']==inputs),None)
    if old:
        p.check(old['output_bindings']+old['evidence_bindings']);print(tag+'/'+label+': own exact actual0 retained',flush=True);return
    occupied=[int(path.name[1:4]) for path in (p.OUT/'actual-runs').glob('c[0-9][0-9][0-9]-*')] if (p.OUT/'actual-runs').exists() else []
    num=max([len(receipt['rows'])]+occupied)+1
    folder=p.OUT/'actual-runs'/('c'+str(num).zfill(3)+'-'+tag+'-'+label);folder.mkdir(parents=True,exist_ok=False)
    snapshots=[]
    for i,binding in enumerate(inputs):
        target=folder/('i'+str(i).zfill(2));target.write_bytes(p.resolve(binding).read_bytes());snapshots.append(dict(original=binding,retained=p.bind(target)))
    obj=ctx/'b/lib/lean'/(module.replace('.','/')+'.olean') if module else None
    if obj:obj.parent.mkdir(parents=True,exist_ok=True)
    args=['lean','-j1']+(['-o',str(obj.relative_to(ctx)),source] if module else ['--version'])
    command=['lake','env',PY,'lean_call.py']+args
    env=dict(os.environ);env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
    env['LEAN_NUM_THREADS']='1';env['LAKE_JOBS']='1';env['PHASE_PLATFORM_INDEPENDENT_PATH_RECEIPT']=str(folder/'selected-paths.json')
    start=time.monotonic()
    with (folder/'stdout.log').open('wb') as out,(folder/'stderr.log').open('wb') as err:
        actual=subprocess.run(command,cwd=ctx,env=env,stdout=out,stderr=err)
    with (folder/'combined.log').open('wb') as out:
        for name in ['stdout.log','stderr.log']:
            with (folder/name).open('rb') as handle:
                while block:=handle.read(1024*1024):out.write(block)
    (folder/'exit.txt').write_text(str(actual.returncode)+'\n',encoding='ascii')
    outputs=[]
    if obj and obj.exists():
        for file in sorted(obj.parent.glob(obj.name+'*')):
            binding=p.bind(file);outputs.append(binding);snap=folder/('o'+str(len(outputs)).zfill(2));snap.write_bytes(file.read_bytes());snapshots.append(dict(original=binding,retained=p.bind(snap)))
    evidence=[p.bind(folder/name) for name in ['stdout.log','stderr.log','combined.log','exit.txt','selected-paths.json'] if (folder/name).exists()]
    row=dict(tag=tag,label=label,module=module,source=source,command=command,execution_CWD=str(ctx),exit_code=actual.returncode,elapsed_seconds=round(time.monotonic()-start,3),input_bindings=inputs,output_bindings=outputs,evidence_bindings=evidence,immutable_snapshots=snapshots,folder_task_relative=folder.relative_to(p.TASK).as_posix(),all_actual_handles_terminal=True,whole_failed_run_excluded=actual.returncode!=0,actual_environment=dict(LEAN_NUM_THREADS='1',LAKE_JOBS='1'))
    receipt['rows'].append(row);p.dump(rp,receipt)
    print(tag+'/'+label+': actual '+str(actual.returncode)+' ('+str(row['elapsed_seconds'])+'s)',flush=True)
    if actual.returncode:
        with (folder/'combined.log').open('rb') as handle:
            handle.seek(max(0,handle.seek(0,2)-7000));print(handle.read().decode('utf-8',errors='replace'),flush=True)
    assert actual.returncode==0,'Actual whole failed run retained; originals/staged payloads immutable'
    gate()

def main():
    sys.stdout.reconfigure(encoding='utf-8');prep=gate();run('native','runtime')
    for context in prep['contexts']:
        for row in context['math_sources']:run(context['tag'],row['label'],row['module'],row['path'])
    p.dump(p.OUT/'source-terminal.json',dict(status='FRESH_PLATFORM_INDEPENDENT_SOURCE_COMPILATIONS_ACTUAL0',all_actual_handles_terminal=True,independent_PASS_claimed=False,API_calls=0))
    for context in p.load(p.OUT/'control-preparation.json')['contexts']:
        for row in context['rows']:run(context['tag'],row['label'],row['module'],row['path'])
    p.dump(p.OUT/'controls-terminal.json',dict(status='FOUR_ISOLATED_CONTEXTS_FULL_TYPES_VALUES_RFL_HELPERS_BOUNDS_IMPORT_CONTROLS_ACTUAL0',all_actual_handles_terminal=True,independent_PASS_claimed=False,API_calls=0))

if __name__=='__main__':main()
