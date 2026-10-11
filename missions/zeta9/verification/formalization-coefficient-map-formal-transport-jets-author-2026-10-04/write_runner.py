"""Source-only adaptation of the existing actual recorder; executes no Lean."""
from pathlib import Path
import prepare as p

GATE='''
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
            marker=b'\\nopen Lean Meta\\n'
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

'''

MAIN='''
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
'''


def main():
    assert not (p.OUT/'preparation-verification.json').exists()
    previous=p.TASK/'formalization/platform/coefficient-map-matrix'
    driver=(previous/'run_actual.py').read_text(encoding='utf-8-sig')
    first=driver.index('\ndef gate():');last=driver.index('\ndef configure_packages():',first)
    driver=driver[:first]+GATE+driver[last:]
    first=driver.index('\ndef main():');driver=driver[:first]+MAIN
    driver=driver.replace('Future serial Matrix author oracles.','Future serial Jets native author compilation.')
    driver=driver.replace("role='Matrix platform author, independent review required'",
        "role='Jets native author, fresh source-only compilation; independent review required'")
    driver=driver.replace('MATRIX_RUN_','JETS_RUN_')
    p.write(p.OUT/'execute.py',driver)
    p.write(p.OUT/'retain_actual_inputs.py',(previous/'retain_actual_inputs.py').read_bytes())
    p.dump(p.OUT/'runner-provenance.json',dict(Lean_invocations=0,
        original_actual_recorder_source=p.binding(previous/'run_actual.py'),
        original_short_snapshot_helper=p.binding(previous/'retain_actual_inputs.py'),
        source_only_copy=True,compiler_objects_copied=False,
        adaptations=['own pure gate and explicit 23-call main','JETS runtime path env',
            'unchanged log/input/output snapshot mechanism','private proof-only repair ledger after actual failure'],
        outputs=[p.binding(p.OUT/name) for name in ['execute.py','retain_actual_inputs.py']]))


if __name__=='__main__':main()
