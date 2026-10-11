"""Future one-lane fresh native Jets independent execution; no import-time Lean."""
from pathlib import Path
import argparse, json, os, re, subprocess, sys, time
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import prepare_sources as p

OUT, TASK, ROOT, PROJECT = p.OUT, p.TASK, p.ROOT, p.PROJECT
CACHE = PROJECT/'b/lib/lean'

def records(path):
    return [json.loads(line) for line in path.read_text(encoding='utf-8-sig').splitlines()
            if line.startswith('{')]

def check_bindings(rows):
    for row in rows:
        path=(TASK/row['task_relative']).resolve()
        assert path.is_relative_to(TASK.resolve())
        assert path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256'], str(path)

def gate(initial=False):
    grant_resume = p.load(HERE / "lane-resume-grant.json")
    assert grant_resume["explicit_new_parent_lane2_resume_granted"] is True
    assert grant_resume["lane"] == 2 and grant_resume["maximum_global_Lean_lanes"] == 2
    assert grant_resume["checkpoint_inspection_sha256"] == p.sha(HERE / "checkpoint-inspection.json")
    assert grant_resume["author_sha256"] == p.AUTHOR_SHA and grant_resume["source_sha256"] == p.SOURCE_SHA
    assert grant_resume["preparation_sha256"] == p.sha(OUT / "preparation-freeze.json")
    assert grant_resume["only_this_serial_lane"] and grant_resume["parent_message_verbatim"]
    assert not grant_resume["foreign_proof_objects_allowed"]
    inspection = p.load(HERE / "checkpoint-inspection.json")
    for orphan in inspection["orphan_attempts"]: check_bindings(orphan["files"])
    frozen_path=OUT/'preparation-freeze.json'
    prep=p.load(frozen_path)
    assert prep['status']=='PURE_INDEPENDENT_PREPARATION_ONLY'
    assert prep['verdict'] is None and prep['Lean_Lake_compiler_invocations']==0
    grant=p.load(OUT/'lane-grant.json')
    assert grant['explicit_parent_Lean_lane_granted'] is True
    assert grant['lane']==2 and grant['maximum_global_Lean_lanes']==2
    assert grant['preparation_sha256']==p.sha(frozen_path)
    assert grant['author_sha256']==p.AUTHOR_SHA and grant['source_sha256']==p.SOURCE_SHA
    assert grant['project_task_relative']=='.rt/tj1' and grant['only_this_serial_lane'] is True
    assert grant['parent_message_verbatim'] and not grant['Root_API_credentials_scope_modified']
    assert p.sha(p.AUTHOR/'author-audit.json')==p.AUTHOR_SHA
    check_bindings(prep['stable_files'])
    if initial:
        check_bindings(p.load(p.AUTHOR/'author-audit.json')['stable_files'])
        if not (OUT/'execution-receipt.json').exists():
            assert not (PROJECT/'b').exists() and not (PROJECT/'.lake/build').exists()
            assert not list(PROJECT.rglob('*.olean'))
    return prep

def configure():
    package_path=PROJECT/'.lake/packages'
    expected=(ROOT/'.lake/packages').resolve()
    if not package_path.exists():
        package_path.parent.mkdir(parents=True,exist_ok=True)
        result=subprocess.run(['pwsh','-NoProfile','-Command',
            'New-Item -ItemType Junction -Path "'+str(package_path)+'" -Target "'+str(expected)+'" | Out-Null'],
            capture_output=True)
        p.write(OUT/'package-junction.log',result.stdout+result.stderr)
        p.write(OUT/'package-junction-exit.txt',str(result.returncode)+'\n')
        assert result.returncode==0
    assert package_path.is_junction() and package_path.resolve()==expected

def run(label,args,output_object=None):
    gate()
    receipt_path=OUT/'execution-receipt.json'
    receipt=p.load(receipt_path) if receipt_path.exists() else dict(
        role='Jets native independent fresh-source reviewer; Data/Bounds foundation author disclosed',
        source_sha256=p.SOURCE_SHA,author_sha256=p.AUTHOR_SHA,
        preparation_sha256=p.sha(OUT/'preparation-freeze.json'),
        project_task_relative='.rt/tj1',cache_objects_borrowed=False,
        Root_or_author_proof_fallback_permitted=False,rows=[])
    inputs=[p.binding(PROJECT/name) for name in ['lakefile.lean','lean-toolchain','lake-manifest.json','lean_call.py']]
    inputs.extend(p.binding(PROJECT/arg) for arg in args if str(arg).endswith('.lean') and (PROJECT/arg).is_file())
    previous=next((r for r in reversed(receipt['rows']) if r['label']==label and r['exit_code']==0
                   and r['input_bindings']==inputs),None)
    if previous is not None:
        check_bindings(previous['input_bindings']+previous['output_bindings']+previous['evidence_bindings'])
        print(label+': previous exact actual0 retained; not a second fresh compile',flush=True)
        return
    inspection=p.load(HERE/'checkpoint-inspection.json')
    orphan_attempts=sum(label == 'source-'+m.rsplit('.',1)[-1] for x in inspection['orphan_attempts'] for m in x['source_modules_matching_snapshot'])
    attempt=1+sum(r['label']==label for r in receipt['rows'])+orphan_attempts
    occupied=[int(re.match(r'c(\d+)',x.name).group(1)) for x in (OUT/'actual-runs').iterdir() if re.match(r'c(\d+)',x.name)]
    number=max([len(receipt['rows'])]+occupied)+1
    receipt.setdefault('takeover_resume', dict(date='2026-10-07',role='New independent takeover reviewer; did not author Jets proofs',inherited_successful_calls=14,inherited_fresh_native_source_calls=13,inherited_receipt=p.binding(HERE/'inherited-execution-receipt.json'),checkpoint_inspection=p.binding(HERE/'checkpoint-inspection.json'),unrecorded_interrupted_attempts_preserved=1,all19_fresh_on_this_takeover_not_claimed=True))
    folder=OUT/'actual-runs'/('c'+str(number).zfill(3)+'-a'+str(attempt).zfill(2))
    folder.mkdir(parents=True,exist_ok=False)
    immutable_inputs=[]
    for i,row in enumerate(inputs):
        source=TASK/row['task_relative']
        copy=folder/('i'+str(i).zfill(2))
        p.write(copy,source.read_bytes())
        immutable_inputs.append(dict(original=row,retained=p.binding(copy)))
    environment=dict(os.environ)
    environment.pop('LEAN_PATH',None); environment.pop('LEAN_SRC_PATH',None)
    environment['JETS_INDEPENDENT_PATH_RECEIPT']=str(folder/'selected-paths.json')
    command=['lake','env',r'C:\Users\anche\AppData\Local\Programs\Python\Python312\python.exe','lean_call.py','lean','-j1']+list(args)
    start=time.monotonic()
    # Stream actual output so even a failed large diagnostic is retained in full.
    with (folder/'stdout.log').open('wb') as stdout, (folder/'stderr.log').open('wb') as stderr:
        result=subprocess.run(command,cwd=PROJECT,env=environment,stdout=stdout,stderr=stderr)
    with (folder/'combined.log').open('wb') as combined:
        for name in ['stdout.log','stderr.log']:
            with (folder/name).open('rb') as source:
                while block:=source.read(8*1024*1024): combined.write(block)
    p.write(folder/'exit.txt',str(result.returncode)+'\n')
    outputs=[]
    if output_object is not None:
        target=PROJECT/output_object
        if target.exists():
            outputs=[p.binding(q) for q in sorted(target.parent.glob(target.name+'*')) if q.is_file()]
    path_receipt=folder/'selected-paths.json'
    evidence=[p.binding(folder/name) for name in ['stdout.log','stderr.log','combined.log','exit.txt']]
    if path_receipt.exists(): evidence.append(p.binding(path_receipt))
    row=dict(label=label,attempt=attempt,command=command,exit_code=result.returncode,
        elapsed_seconds=round(time.monotonic()-start,3),actual_executor=p.binding(Path(__file__)),
        input_bindings=inputs,immutable_input_snapshots=immutable_inputs,output_bindings=outputs,
        evidence_bindings=evidence,folder_task_relative=folder.relative_to(TASK).as_posix(),
        failed_whole_run_excluded=result.returncode!=0,all_subprocess_handles_terminal=True)
    receipt['rows'].append(row); p.dump(receipt_path,receipt)
    print(label+': actual exit '+str(result.returncode)+' ('+str(row['elapsed_seconds'])+'s)',flush=True)
    if result.returncode:
        with (folder/'combined.log').open('rb') as source:
            source.seek(max(0,source.seek(0,2)-7000))
            print(source.read().decode('utf-8',errors='replace'),flush=True)
    assert result.returncode==0, 'Actual failed whole run retained; repair own new control only.'
    assert path_receipt.exists()
    selected=p.load(path_receipt)
    for key in ['LEAN_PATH','LEAN_SRC_PATH']:
        allowed={str(Path(raw).resolve()).casefold() for raw in selected[key]['allowed_exact_set']}
        assert all(str(Path(raw).resolve()).casefold() in allowed for raw in selected[key]['filtered'])
        assert str(ROOT.resolve()).casefold() not in allowed
        assert not any('/.rt/ja1/' in raw.replace('\\','/').lower() for raw in selected[key]['filtered'])
    gate()

def schedule(source):
    bymodule={r['module']:r for r in source}
    active,done=set(),set(); result=[]
    def visit(module):
        if module in done:return
        assert module not in active
        active.add(module)
        text=(PROJECT/bymodule[module]['project_relative']).read_text(encoding='utf-8-sig')
        for line in re.findall(r'^import\s+([^\n]+)',text,re.M):
            for dep in line.split():
                if dep in bymodule: visit(dep)
        active.remove(module);done.add(module);result.append(bymodule[module])
    for module in bymodule:visit(module)
    return result

def build(label,module,relative):
    object_relative='b/lib/lean/'+module.replace('.','/')+'.olean'
    (PROJECT/object_relative).parent.mkdir(parents=True,exist_ok=True)
    run(label,['-o',object_relative,relative],object_relative)

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser()
    parser.add_argument('--parent-lane-authorized',action='store_true',required=True)
    parser.parse_args()
    prep=gate(initial=True); configure()
    run('runtime',['--version'])
    for row in schedule(prep['source_records']):
        build('source-'+row['module'].rsplit('.',1)[-1],row['module'],row['project_relative'])
    for module in ['IndependentExprDagV3','IndependentExprDagValidationV3']:
        build('serializer-'+module,module,module+'.lean')
    for module in prep['planned_control_modules']:
        build('control-'+module,module,module+'.lean')
    run('actual-own-object-resolution',['JetsActualResolver.lean'])
    receipt=p.load(OUT/'execution-receipt.json')
    latest={r['label']:r for r in receipt['rows']}
    assert len(latest)==27 and all(r['exit_code']==0 for r in latest.values())
    final=latest['actual-own-object-resolution']
    rows=records(TASK/final['folder_task_relative']/'stdout.log')
    actual=[r for r in rows if r.get('kind')=='actual_own_findOLean']
    assert len(actual)==25 and all(r['exact_own_cache'] for r in actual)
    check_bindings(p.load(p.AUTHOR/'author-audit.json')['stable_files'])
    p.dump(OUT/'terminal-execution-gate.json',dict(
        status='ALL_PLANNED_ACTUAL_CALLS_TERMINAL_REVIEW_FREEZE_STILL_REQUIRED',
        final_success_labels=27,actual_attempts=len(receipt['rows']),
        actual_failed_attempts=sum(r['exit_code']!=0 for r in receipt['rows']),
        own_native_fresh_sources=19,own_serializer_sources=2,actual_own_resolutions=25,
        all_handles_terminal=True,independent_PASS_claimed=False,
        inherited_actual_success_calls=14,inherited_fresh_native_source_calls=13,
        takeover_actual_success_calls=sum(r['exit_code']==0 for r in receipt['rows'][14:]),takeover_fresh_native_source_calls=6,
        unrecorded_interrupted_attempts_preserved=1,unrecorded_exit_code_not_fabricated=True,
        execution_receipt=p.binding(OUT/'execution-receipt.json')))
    print('All 27 planned labels have terminal actual0; independent report freeze still required.',flush=True)

if __name__=='__main__':main()
