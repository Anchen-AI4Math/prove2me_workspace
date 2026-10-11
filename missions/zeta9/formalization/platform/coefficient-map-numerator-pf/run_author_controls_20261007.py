"""Continue five missing/new author calls only; a new Root lane grant is required."""
import argparse, os, sys
sys.dont_write_bytecode = True
import prepare as p
import author_stage as a

def main():
    q=argparse.ArgumentParser()
    q.add_argument('--lane-granted',action='store_true',required=True)
    q.parse_args()
    assert not (p.OUT/'author-audit.json').exists()
    os.environ['LEAN_NUM_THREADS']='1'
    os.environ['LAKE_JOBS']='1'
    p.dump(p.OUT/'author-resume-lane-2026-10-07.json',dict(
        role='continued same AUTHOR batch',lane=1,new_Root_lane_grant_required=True,
        LEAN_NUM_THREADS=os.environ['LEAN_NUM_THREADS'],LAKE_JOBS=os.environ['LAKE_JOBS'],
        serial=True,initial_43_not_rerun=True,own_existing_pa1_objects_reused=True,
        independent_review_claimed=False))
    a.compile_module('build-2-reference','Theorems.Thm_ZetaNine_CoefficientMapNumeratorPF_injective')
    plan=p.load(p.OUT/'author-controls-plan-2026-10-07.json')
    a.compile_module('author-native-reachable-v1',plan['native_control'])
    for row in plan['staged_controls']:
        suffix=row['label'].split('_')[1]
        a.compile_module('author-staged-'+suffix+'-v1',row['label'])
    print('Five continued/new actual author calls completed; full hash freeze still pending.',flush=True)

if __name__=='__main__': main()
