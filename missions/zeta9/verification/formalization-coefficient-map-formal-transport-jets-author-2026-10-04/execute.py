"""Future serial Jets native author compilation. Explicit Root lane grant required.

Importing/byte-compiling this file never runs Lean. Each actual attempt keeps
source/output/path/log hashes; neither Root proof objects nor another lane's
cache can satisfy a source compile. No install, API, credential or scope action.
"""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys, time
import prepare as p
import retain_actual_inputs

OUT, TASK, ROOT, PROJECT = p.OUT, p.TASK, p.ROOT, p.PROJECT


def rows(path):
    return [json.loads(line) for line in path.read_text(encoding='utf-8-sig').splitlines()
            if line.startswith('{')]


def gate():
    p.native_gate()
    state=p.load(OUT/'preparation-state.json')
    frozen=p.load(OUT/'preparation-verification.json')
    assert frozen['status']=='PURE_AUTHOR_RUNTIME_PREPARATION_ONLY'
    assert frozen['Lean_invocations']==0 and not frozen['author_PASS_claimed']
    for row in frozen['files']:
        path=TASK/row['task_relative']
        assert path.stat().st_size==row['bytes'] and p.sha(path)==row['sha256']
    ledger_path=OUT/'private-proof-repairs.json'
    ledger=p.load(ledger_path) if ledger_path.exists() else dict(allowed_current_source_bindings=[])
    allowed={r['task_relative']:r for r in ledger['allowed_current_source_bindings']}
    def check_copy(path,old,initial,is_main=False,is_control=False):
        if p.sha(path)==initial['sha256']:return
        assert is_main or is_control,'Only the own main proof or own controls may be repaired.'
        receipt=p.load(OUT/'compile-receipt.json')
        assert any(r['exit_code']!=0 for r in receipt['rows']),'Retain actual failure before repair.'
        assert ledger['shared_original_source_and_old5bindings_unchanged'] is True
        assert ledger['proof_bodies_only_no_original_header_changes'] is True
        actual=p.binding(path);assert allowed[actual['task_relative']]==actual
        assert p.statement_headers(path.read_bytes())==p.statement_headers(old.read_bytes())
        if is_control:
            marker=b'\nopen Lean Meta\n'
            assert path.read_bytes().split(marker)[-1]==old.read_bytes().split(marker)[-1]
    for row in state['source']:
        old=TASK/row['immutable_initial_snapshot']['task_relative']
        assert p.sha(old)==row['sha256']
        check_copy(PROJECT/row['project_relative'],old,row['initial_project_copy'],row['module']==p.NATIVE)
    for row in state['controls']:
        old=TASK/row['immutable_source']['task_relative']
        check_copy(PROJECT/row['project_relative'],old,row['initial_project_copy'],is_control=True)
    assert all(r['passed'] and r['path_plus_64']<=259 for r in state['path_checks'])
    return state


def configure_packages():
    destination = PROJECT/'.lake/packages'
    expected = (ROOT/'.lake/packages').resolve()
    destination.parent.mkdir(parents=True, exist_ok=True)
    if not destination.exists():
        result = subprocess.run(['cmd', '/c', 'mklink', '/J', str(destination), str(expected)],
                                capture_output=True)
        p.write(OUT/'package-junction.log', result.stdout+result.stderr)
        p.write(OUT/'package-junction-exit.txt', str(result.returncode)+'\n')
        assert result.returncode == 0
    assert destination.is_junction() and destination.resolve() == expected


def run(label, arguments, output=None):
    state = gate()
    receipt_path = OUT/'compile-receipt.json'
    receipt = p.load(receipt_path) if receipt_path.exists() else dict(
        role='Jets native author, fresh source-only compilation; independent review required',
        source_sha256=p.SOURCE_SHA, project_task_relative=PROJECT.relative_to(TASK).as_posix(),
        fresh_build_task_relative=(PROJECT/'b').relative_to(TASK).as_posix(),
        cache_objects_borrowed=False, Root_proof_fallback_permitted=False,
        Root_API_credentials_scope_modified=False, rows=[])
    inputs = [p.binding(PROJECT/name) for name in ['lakefile.lean', 'lean-toolchain',
                                                       'lake-manifest.json', 'lean_call.py']]
    for argument in arguments:
        candidate = PROJECT/argument
        if str(argument).endswith('.lean') and candidate.is_file(): inputs.append(p.binding(candidate))
    previous = next((r for r in reversed(receipt['rows']) if r['label'] == label and r['exit_code'] == 0 and r['input_bindings'] == inputs and all((TASK/b['task_relative']).exists() and p.sha(TASK/b['task_relative']) == b['sha256'] for b in r['output_bindings'])), None)
    if previous is not None:
        assert previous['input_bindings'] == inputs
        for row in previous['output_bindings']+[previous[k] for k in ['stdout','stderr','log','exit_file','selected_paths']]:
            path = TASK/row['task_relative']
            assert path.stat().st_size == row['bytes'] and p.sha(path) == row['sha256']
        print(label+': exact prior actual success retained', flush=True)
        return
    attempt = 1+sum(r['label'] == label for r in receipt['rows'])
    folder = OUT/'actual-runs'/(label+'-'+str(attempt).zfill(2))
    folder.mkdir(parents=True, exist_ok=False)
    environment = dict(os.environ)
    environment.pop('LEAN_PATH', None); environment.pop('LEAN_SRC_PATH', None)
    environment['JETS_RUN_LABEL'] = label
    environment['JETS_RUN_PATHS_RECEIPT'] = str(folder/'selected-paths.json')
    command = ['lake','env','python','lean_call.py','lean']+list(arguments)
    start = time.monotonic()
    result = subprocess.run(command, cwd=PROJECT, env=environment, capture_output=True)
    for name,data in [('stdout.log',result.stdout),('stderr.log',result.stderr),
                      ('combined.log',result.stdout+result.stderr),('exit.txt',str(result.returncode)+'\n')]:
        p.write(folder/name,data)
    if output is not None: p.write(OUT/output, result.stdout)
    output_paths = []
    if '-o' in arguments:
        obj = PROJECT/arguments[arguments.index('-o')+1]
        if obj.exists(): output_paths.extend(sorted(obj.parent.glob(obj.name+'*')))
    if label == 'stage1-extract' and (OUT/'decl_graph.jsonl').exists(): output_paths.append(OUT/'decl_graph.jsonl')
    if label.startswith('stage2-'):
        snapshot = OUT/(label.removeprefix('stage2-')+'-oracle-input.lean')
        if snapshot.exists(): output_paths.append(snapshot)
    if output is not None: output_paths.append(OUT/output)
    path_receipt = folder/'selected-paths.json'
    row = dict(label=label, attempt=attempt, command=command, cwd=str(PROJECT),
        exit_code=result.returncode, elapsed_seconds=round(time.monotonic()-start,3),
        input_bindings=inputs, output_bindings=[p.binding(path) for path in output_paths],
        stdout=p.binding(folder/'stdout.log'), stderr=p.binding(folder/'stderr.log'),
        log=p.binding(folder/'combined.log'), exit_file=p.binding(folder/'exit.txt'),
        selected_paths=p.binding(path_receipt) if path_receipt.exists() else None,
        failure_retained=result.returncode != 0)
    retain_actual_inputs.retain(row,folder)
    row['actual_executor_sha256']=p.sha(Path(__file__))
    receipt['rows'].append(row); p.dump(receipt_path, receipt)
    p.write(OUT/(label+'.log'),result.stdout+result.stderr)
    p.write(OUT/(label+'-exit.txt'),str(result.returncode)+'\n')
    print(label+': actual exit '+str(result.returncode), flush=True)
    if result.returncode:
        print((result.stdout+result.stderr).decode('utf-8',errors='replace'),flush=True)
    assert result.returncode == 0, 'Actual failed attempt retained; no PASS or continuation claimed.'
    assert path_receipt.exists()
    selected = p.load(path_receipt)
    for key in ['LEAN_PATH','LEAN_SRC_PATH']:
        assert all(Path(raw).resolve().is_relative_to(PROJECT.resolve()) or
            Path(raw).resolve().is_relative_to((ROOT/'.lake/packages').resolve())
            for raw in selected[key]['filtered'])
    gate()


def topological_sources(records, relative_key):
    """Scheduling hint from fixed import lines, not new actual header evidence."""
    bymodule = {r['module']:r for r in records}
    result, active, done = [], set(), set()
    def visit(module):
        if module in done: return
        assert module not in active, 'Cyclic scheduling hint.'
        active.add(module)
        text = (PROJECT/bymodule[module][relative_key]).read_text(encoding='utf-8-sig')
        for line in text.splitlines():
            if line.startswith('import '):
                for dep in line.removeprefix('import ').split():
                    if dep in bymodule: visit(dep)
        active.remove(module); done.add(module); result.append(bymodule[module])
    for module in bymodule: visit(module)
    return result


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser()
    parser.add_argument('--lane-granted',action='store_true',required=True)
    parser.parse_args()
    state=gate()
    if not (OUT/'compile-receipt.json').exists():
        assert not (PROJECT/'b').exists(),'Fresh own cache required before the first real call.'
    configure_packages()
    run('toolchain',['--version'])
    for row in state['source']:
        obj='b/lib/lean/'+row['module'].replace('.','/')+'.olean'
        (PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
        run('source-'+row['module'].rsplit('.',1)[1],['-o',obj,row['project_relative']])
    for row in state['controls']:
        obj='b/lib/lean/'+row['module']+'.olean'
        run('control-'+row['module'],['-o',obj,row['project_relative']])
    run('own-object-resolution',['resolver.lean'])
    receipt=p.load(OUT/'compile-receipt.json')
    latest={row['label']:row for row in receipt['rows']}
    assert len(latest)==23 and all(row['exit_code']==0 for row in latest.values())
    resolved=rows(OUT/'own-object-resolution.log')
    assert len(resolved)==21 and all(Path(r['olean']).resolve()==
        (PROJECT/'b/lib/lean'/(r['module'].replace('.','/')+'.olean')).resolve() for r in resolved)
    print('Actual calls terminal; native author source/type/axiom/boundary evidence freeze still required.')


if __name__=='__main__':main()
