"""Versioned resume avoiding an unreceipted interrupted attempt directory."""
import argparse, os, sys
sys.dont_write_bytecode = True
import prepare as p
import author_stage as a

def main():
    q=argparse.ArgumentParser()
    q.add_argument('--lane-granted',action='store_true',required=True)
    q.parse_args()
    grant=p.load(p.OUT/'lane1-resume-grant-2026-10-07.json')
    assert grant['explicit_new_parent_lane1_resume_granted'] and grant['lane']==1
    assert not (p.OUT/'author-audit.json').exists()
    orphan=p.OUT/'actual-runs/build-2-reference-01'
    assert sorted(x.name for x in orphan.iterdir())==['selected-paths.json']
    p.dump(p.OUT/'resume-prelaunch-failure-and-orphan-2026-10-07.json',dict(
        failed_driver=p.binding(p.OUT/'run_author_controls_20261007.py'),
        actual_command=['C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe',
            'formalization/platform/coefficient-map-numerator-pf/run_author_controls_20261007.py','--lane-granted'],
        actual_exit=1,Lean_started=False,receipt_rows_appended=0,
        actual_exception='FileExistsError: [WinError 183] actual-runs/build-2-reference-01',
        reason='Interrupted old call left only selected-paths.json; no old stdout, stderr, exit, object or receipt row exists.',
        orphan_directory_unchanged=True,orphan_files=[p.binding(x) for x in orphan.iterdir()],
        reference_input=p.binding(p.PROJECT/'Theorems/Thm_ZetaNine_CoefficientMapNumeratorPF_injective.lean'),
        new_attempt_label='resume-build-2-reference-v1',
        original_executor_unchanged=p.binding(p.OUT/'execute_oracles.py')))
    os.environ['LEAN_NUM_THREADS']='1'
    os.environ['LAKE_JOBS']='1'
    a.compile_module('resume-build-2-reference-v1','Theorems.Thm_ZetaNine_CoefficientMapNumeratorPF_injective')
    plan=p.load(p.OUT/'author-controls-plan-2026-10-07.json')
    a.compile_module('author-native-reachable-v1',plan['native_control'])
    for row in plan['staged_controls']:
        suffix=row['label'].split('_')[1]
        a.compile_module('author-staged-'+suffix+'-v1',row['label'])
    print('Five continued/new actual author calls completed; final author audit pending.',flush=True)

if __name__=='__main__': main()
