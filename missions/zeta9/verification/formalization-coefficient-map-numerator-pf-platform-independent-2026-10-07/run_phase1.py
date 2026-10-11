"""Own fresh SOURCE and official oracle phase; one serial Lean -j1 lane."""
from pathlib import Path
import argparse, json, os, re, subprocess, sys, time
import inspect_author as p

OUT,TASK,ROOT,PROJECT,AUTHOR=p.OUT,p.TASK,p.ROOT,p.PROJECT,p.AUTHOR
PY=r'C:\Users\anche\AppData\Local\Programs\Python\Python312\python.exe'

def dump(path, value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

def gate():
    grant=p.load(OUT/'lane2-grant.json')
    assert grant['explicit_parent_lane2_granted'] and grant['maximum_global_Lean_lanes']==2
    assert grant['single_serial_Lean_j1'] and not grant['foreign_proof_objects_allowed']
    assert grant['source_preparation_sha256']==p.sha(OUT/'source-preparation.json')
    assert p.sha(AUTHOR/'author-audit.json')==p.AUTHOR_SHA
    assert p.sha(AUTHOR/'preparation-verification.json')==p.PREPARATION_SHA
    prep=p.load(OUT/'source-preparation.json'); p.check(prep['stable_files'])
    return prep

def configure():
    link=PROJECT/'.lake/packages'; expected=ROOT/'.lake/packages'
    if not link.exists():
        link.parent.mkdir(parents=True,exist_ok=True)
        command=['pwsh','-NoProfile','-Command','New-Item -ItemType Junction -Path "'+str(link)+'" -Target "'+str(expected)+'" | Out-Null']
        result=subprocess.run(command,capture_output=True)
        (OUT/'package-junction.log').write_bytes(result.stdout+result.stderr)
        (OUT/'package-junction-exit.txt').write_text(str(result.returncode)+'\n',encoding='ascii')
        assert result.returncode==0
    assert link.is_junction() and link.resolve()==expected.resolve()

def run(label,args,output_paths=()):
    gate()
    receipt_path=OUT/'execution-receipt.json'
    receipt=p.load(receipt_path) if receipt_path.exists() else dict(
        role='Independent NumeratorPF platform reviewer; no payload authorship',
        project_task_relative='.rt/pfi1',foreign_proof_objects_borrowed=False,rows=[])
    inputs=[p.bind(PROJECT/name) for name in ['lakefile.lean','lean-toolchain','lake-manifest.json','lean_call.py']]
    inputs += [p.bind(PROJECT/x) for x in args if str(x).endswith('.lean') and (PROJECT/x).is_file()]
    previous=next((x for x in reversed(receipt['rows']) if x['label']==label and x['exit_code']==0 and x['input_bindings']==inputs),None)
    if previous:
        p.check(previous['input_bindings']+previous['output_bindings']+previous['evidence_bindings'])
        print(label+': retained own exact prior actual0; no repeat',flush=True); return
    root=OUT/'actual-runs'; root.mkdir(exist_ok=True)
    occupied=[int(x.name[1:4]) for x in root.iterdir() if re.match(r'c\d{3}-a\d+',x.name)]
    number=max([len(receipt['rows'])]+occupied)+1
    attempt=1+sum(x['label']==label for x in receipt['rows'])
    folder=root/('c'+str(number).zfill(3)+'-a'+str(attempt).zfill(2)); folder.mkdir(exist_ok=False)
    snapshots=[]
    for i,row in enumerate(inputs):
        target=folder/('i'+str(i).zfill(2)); target.write_bytes((TASK/row['task_relative']).read_bytes())
        snapshots.append(dict(original=row,retained=p.bind(target)))
    env=dict(os.environ); env.pop('LEAN_PATH',None); env.pop('LEAN_SRC_PATH',None)
    env['PF_INDEPENDENT_PATH_RECEIPT']=str(folder/'selected-paths.json')
    command=['lake','env',PY,'lean_call.py','lean','-j1']+list(args)
    started=time.monotonic()
    with (folder/'stdout.log').open('wb') as stdout,(folder/'stderr.log').open('wb') as stderr:
        result=subprocess.run(command,cwd=PROJECT,env=env,stdout=stdout,stderr=stderr)
    with (folder/'combined.log').open('wb') as combined:
        for name in ['stdout.log','stderr.log']:
            with (folder/name).open('rb') as source:
                while block:=source.read(8*1024*1024): combined.write(block)
    (folder/'exit.txt').write_text(str(result.returncode)+'\n',encoding='ascii')
    outputs=[]
    for relative in output_paths:
        target=PROJECT/relative
        if target.is_file():
            selected=sorted(target.parent.glob(target.name+'*')) if target.suffix=='.olean' else [target]
            for source in selected:
                outputs.append(p.bind(source))
                snapshot=folder/('o'+str(len(outputs)).zfill(2)); snapshot.write_bytes(source.read_bytes())
                snapshots.append(dict(original=p.bind(source),retained=p.bind(snapshot)))
    evidence=[p.bind(folder/name) for name in ['stdout.log','stderr.log','combined.log','exit.txt','selected-paths.json'] if (folder/name).exists()]
    row=dict(label=label,attempt=attempt,command=command,execution_CWD=str(PROJECT),exit_code=result.returncode,
        elapsed_seconds=round(time.monotonic()-started,3),executor=p.bind(Path(__file__)),
        input_bindings=inputs,immutable_input_output_snapshots=snapshots,output_bindings=outputs,
        evidence_bindings=evidence,folder_task_relative=folder.relative_to(TASK).as_posix(),
        whole_failed_run_excluded=result.returncode!=0,all_subprocess_handles_terminal=True)
    receipt['rows'].append(row); dump(receipt_path,receipt)
    print(label+': actual exit '+str(result.returncode)+' ('+str(row['elapsed_seconds'])+'s)',flush=True)
    if result.returncode:
        with (folder/'combined.log').open('rb') as f:
            f.seek(max(0,f.seek(0,2)-6000)); print(f.read().decode('utf-8',errors='replace'),flush=True)
    assert result.returncode==0,'Actual whole failed run retained and excluded; version any repaired source.'
    selected=p.load(folder/'selected-paths.json')
    for key in ['LEAN_PATH','LEAN_SRC_PATH']:
        exact={str(Path(x).resolve()).casefold() for x in selected[key]['allowed_exact_set']}
        assert all(Path(x).is_absolute() and str(Path(x).resolve()).casefold() in exact for x in selected[key]['filtered'])
        assert str(ROOT.resolve()).casefold() not in exact
        assert not any('/.rt/pa1/' in x.replace('\\','/').lower() or '/.rt/tj1/' in x.replace('\\','/').lower() for x in selected[key]['filtered'])
    gate()

def schedule(rows):
    modules={x['module']:x for x in rows}; active,done,result=set(),set(),[]
    def visit(module):
        if module in done:return
        assert module not in active; active.add(module)
        source=(PROJECT/modules[module]['project_relative']).read_text(encoding='utf-8-sig')
        for line in re.findall(r'^import\s+([^\n]+)',source,re.M):
            for dep in line.split():
                if dep in modules:visit(dep)
        active.remove(module); done.add(module); result.append(modules[module])
    for module in modules:visit(module)
    return result

def build(label,module,source):
    obj='b/lib/lean/'+module.replace('.','/')+'.olean'
    (PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
    run(label,['-o',obj,source],[obj])

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser(); parser.add_argument('--parent-lane2-authorized',action='store_true',required=True); parser.parse_args()
    prep=gate(); configure(); run('runtime',['--version'])
    for row in schedule(prep['native_sources']):build('native-'+row['module'].rsplit('.',1)[-1],row['module'],row['project_relative'])
    run('official-native-declaration-graph',['PFIndependentGraph.lean'],['native-decl-graph.jsonl'])
    for row in prep['native_sources']:
        run('official-parser-'+row['module'].rsplit('.',1)[-1],['--run','PFIndependentParser.lean',row['project_relative'],'ZetaNine'])
    native_names={x['module'] for x in prep['native_sources']}
    for row in schedule(prep['parent_definition_sources']):
        if row['module'] not in native_names:build('parent-'+row['module'].rsplit('.',1)[-1],row['module'],row['project_relative'])
    for row in sorted(prep['seven_payloads'],key=lambda x:(0 if x['project_relative'].startswith('Definitions/') else 1,x['project_relative'])):
        build('payload-'+row['module'].rsplit('.',1)[-1],row['module'],row['project_relative'])
    receipt=p.load(OUT/'execution-receipt.json'); latest={x['label']:x for x in receipt['rows']}
    assert len(latest)==45 and all(x['exit_code']==0 for x in latest.values())
    dump(OUT/'phase1-terminal.json',dict(status='FRESH_SOURCE_AND_OWN_ORACLES_COMPLETE_SEMANTIC_CONTROLS_STILL_REQUIRED',
        success_calls=45,native_SOURCE_calls=16,additional_parent_SOURCE_calls=4,exact_payload_SOURCE_calls=7,
        official_graph_calls=1,official_parser_calls=16,runtime_calls=1,
        all_actual_handles_terminal=True,independent_PASS_claimed=False,receipt=p.bind(OUT/'execution-receipt.json')))
    print('Phase1 terminal actual0; full independent semantic review still required.',flush=True)

if __name__=='__main__':main()
