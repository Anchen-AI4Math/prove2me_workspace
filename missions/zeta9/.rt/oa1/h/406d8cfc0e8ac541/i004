"""Authorized serial Outputs AUTHOR derivative. Frozen preparation is immutable.

Only runtime identity, output recording directory, and cwd-sensitive resolver
normalization differ from the original recorder. No foreign proof cache is used.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, inspect, json, os, sys

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
PREP = TASK / 'verification/formalization-coefficient-map-formal-transport-outputs-preparation-2026-10-04'
PROJECT = TASK / '.rt/oa1'
PY312 = Path('C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe')
BIN = Path('C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
LAKE, LEAN = BIN / 'lake.exe', BIN / 'lean.exe'
LEAF = OUT / 'execute_leaf.py'
sys.path.insert(0, str(PREP))
import prepare as p


def load(path): return json.loads(path.read_text(encoding='utf-8-sig'))
def save(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')


def gate():
    grant = load(PREP / 'Root-lane-grant.json')
    assert grant['lane'] == 1 and grant['serial_only'] and grant['Lean_threads'] == 1
    assert grant['source_sha256'] == 'f16dc8be54bd58c09f240ed3404ba3810297e1a8e9d9ab9806893d410862f09d'
    assert not grant['foreign_proof_objects_permitted'] and not grant['API_or_old_mission_operations_permitted']
    p.native_gate()
    frozen, state = load(PREP/'preparation-verification.json'), load(PREP/'preparation-state.json')
    for row in frozen['files']:
        path = TASK / row['task_relative']
        assert path.stat().st_size == row['bytes'] and p.sha(path) == row['sha256']
    ledger = load(OUT/'private-proof-repairs.json') if (OUT/'private-proof-repairs.json').exists() else {}
    permitted = {row['task_relative']: row for row in ledger.get('allowed_current_source_bindings', [])}

    def source_check(path, old, initial, own=False, control=False):
        assert old.stat().st_size == initial['bytes'] and p.sha(old) == initial['sha256']
        if path.stat().st_size == initial['bytes'] and p.sha(path) == initial['sha256']:
            return
        assert own or control, 'No dependency source repair authorized.'
        receipt = load(OUT/'compile-receipt.json')
        assert any(row['exit_code'] != 0 for row in receipt['rows']), 'Retain a real failure before repair.'
        assert ledger['original_source_headers_preserved'] and ledger['shared_original_and_frozen_sources_unchanged']
        assert permitted[path.relative_to(TASK).as_posix()] == p.binding(path)
        assert p.statement_headers(path.read_bytes()) == p.statement_headers(old.read_bytes())
        if control:
            assert path.read_bytes().split(b'\nopen Lean Meta\n')[-1] == old.read_bytes().split(b'\nopen Lean Meta\n')[-1]

    for row in state['source']:
        source_check(PROJECT/row['project_relative'], TASK/row['immutable_initial_snapshot']['task_relative'],
                     row['immutable_initial_snapshot'], own=row['module'] == p.NATIVE)
    for row in state['controls']:
        source_check(PROJECT/row['project_relative'], TASK/row['immutable_source']['task_relative'],
                     row['immutable_source'], control=True)
    assert all(row['passed'] and row['path_plus_64'] <= 259 for row in state['path_checks'])
    return state


def rehash_initial_preflight():
    checks=[]
    def check(group, row, path=None):
        path = path or TASK/row['task_relative']
        passed=path.is_file() and path.stat().st_size == row['bytes'] and p.sha(path) == row['sha256']
        checks.append(dict(group=group,path=str(path),sha256=p.sha(path) if path.is_file() else None,passed=passed))
    frozen, inputs, state = load(PREP/'preparation-verification.json'), load(PREP/'source-inputs.json'), gate()
    for row in frozen['files']: check('original_preparation',row)
    for row in inputs['sources']:
        check('source_origin',row,Path(row['origin_absolute']))
        check('initial_source_copy',row['initial_project_copy'])
        check('immutable_snapshot',row['immutable_initial_snapshot'])
    for row in inputs['prior_freeze_descriptors']: check('prior_freeze_descriptor',row)
    for row in state['controls']:
        check('control',row['immutable_source']);check('control',row['initial_project_copy'])
    assert len(checks)==129 and all(row['passed'] for row in checks)
    sums=[]
    for line in (PREP/'SHA256SUMS.txt').read_text(encoding='utf-8-sig').splitlines():
        if not line.strip():continue
        expected,relative=line.split(maxsplit=1)
        path=TASK/relative.lstrip('*')
        sums.append(dict(path=str(path),expected_sha256=expected,actual_sha256=p.sha(path),passed=p.sha(path)==expected))
    assert len(sums)==54 and all(row['passed'] for row in sums)
    assert not (PROJECT/'b').exists() and not (PROJECT/'.lake').exists()
    assert not list(PROJECT.rglob('*.olean')) and not list(PROJECT.rglob('*.ilean'))
    save(OUT/'initial-runtime-preflight.json',dict(role='Author personally rehashed before any Lean',
        original_binding_occurrences=129,original_SHA256SUMS_occurrences=54,failures=0,checks=checks,sums=sums,
        original_source_sha256=p.sha(p.CANDIDATE),verified_Jets_source_sha256=p.sha(p.VERIFIED_JETS),
        object_cache_absent=True,package_link_absent=True,Lean_calls_before_this_preflight=0))


def load_recorder():
    assert p.sha(PREP/'execute.py')=='7b17f375c271030e3b994340b58e1fb315b151cf9e316f0cef34e84f6e891067'
    spec=importlib.util.spec_from_file_location('outputs_original_recorder',PREP/'execute.py')
    recorder=importlib.util.module_from_spec(spec);spec.loader.exec_module(recorder)
    original=inspect.getsource(recorder.run)
    old="command = ['lake','env','python','lean_call.py','lean']+list(arguments)"
    new="command = [str(LAKE),'env',str(PY312),str(LEAF),str(LEAN),'-j1']+list(arguments)"
    assert original.count(old)==1
    derived=original.replace(old,new)
    marker='    for argument in arguments:\n'
    assert derived.count(marker)==1
    derived=derived.replace(marker,
        "    inputs.extend([p.binding(Path(__file__)),p.binding(LEAF),p.binding(PREP/'execute.py'),p.binding(PREP/'Root-lane-grant.json')])\n"+marker)
    recorder.OUT=OUT;recorder.gate=gate;recorder.__file__=str(Path(__file__))
    recorder.PREP=PREP;recorder.PY312=PY312;recorder.LEAF=LEAF;recorder.LAKE=LAKE;recorder.LEAN=LEAN
    path=OUT/'derived_run_source.py'
    if path.exists():assert path.read_text(encoding='utf-8')==derived
    else:path.write_text(derived,encoding='utf-8')
    exec(compile(derived,str(path),'exec'),recorder.__dict__)
    return recorder


def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser();parser.add_argument('--lane-granted',action='store_true',required=True);parser.parse_args()
    assert Path(sys.executable).resolve()==PY312.resolve()
    for path in [PY312,LAKE,LEAN,LEAF]:assert path.is_file()
    if not (OUT/'compile-receipt.json').exists():rehash_initial_preflight()
    recorder=load_recorder();state=gate()
    provenance=dict(role='Native Outputs author executor derivative; not independent review',
        original_executor=p.binding(PREP/'execute.py'),actual_executor=p.binding(Path(__file__)),
        derived_recorder_source=p.binding(OUT/'derived_run_source.py'),actual_leaf=p.binding(LEAF),
        original_leaf=p.binding(PROJECT/'lean_call.py'),interpreter=str(PY312),lake=str(LAKE),lean=str(LEAN),
        Lean_threads=1,serial_only=True,output_directory=OUT.relative_to(TASK).as_posix(),
        modifications=['absolute PY312 and pinned executables','separate author recording directory',
                       'actual findOLean relative paths resolved against actual execution cwd',
                       'frozen gate rechecks and retained-failure private repairs'],
        borrowed_foreign_proof_objects=False,API_or_mission_operations=False)
    if not (OUT/'executor-provenance.json').exists():save(OUT/'executor-provenance.json',provenance)
    recorder.configure_packages()
    recorder.run('toolchain',['--version'])
    for row in state['source']:
        obj='b/lib/lean/'+row['module'].replace('.','/')+'.olean'
        (PROJECT/obj).parent.mkdir(parents=True,exist_ok=True)
        recorder.run('source-'+row['module'].rsplit('.',1)[1],['-o',obj,row['project_relative']])
    for row in state['controls']:
        obj='b/lib/lean/'+row['module']+'.olean'
        recorder.run('control-'+row['module'],['-o',obj,row['project_relative']])
    recorder.run('own-object-resolution',['resolver.lean'])
    receipt=load(OUT/'compile-receipt.json');latest={row['label']:row for row in receipt['rows']}
    assert len(latest)==27 and all(row['exit_code']==0 for row in latest.values())
    actual=recorder.rows(OUT/'own-object-resolution.log');assert len(actual)==25
    resolved=[]
    for row in actual:
        raw=Path(row['olean']);absolute=raw.resolve() if raw.is_absolute() else (PROJECT/raw).resolve()
        expected=(PROJECT/'b/lib/lean'/(row['module'].replace('.','/')+'.olean')).resolve()
        assert absolute==expected
        resolved.append(dict(**row,actual_execution_cwd=str(PROJECT),resolved_absolute=str(absolute),
                             expected_own_absolute=str(expected),own_object_resolution_passed=True))
    save(OUT/'actual-own-object-resolution.json',resolved)
    save(OUT/'terminal-runtime-state.json',dict(actual_rows=len(receipt['rows']),
        actual_successful_rows=sum(row['exit_code']==0 for row in receipt['rows']),
        actual_failed_rows=sum(row['exit_code']!=0 for row in receipt['rows']),
        final_required_calls=27,final_success_calls=27,own_object_resolutions=25,
        author_audit_and_freeze_still_required=True,independent_review_still_required=True))
    print('All actual serial calls terminal; author audit and freeze still required.',flush=True)


if __name__=='__main__':main()
