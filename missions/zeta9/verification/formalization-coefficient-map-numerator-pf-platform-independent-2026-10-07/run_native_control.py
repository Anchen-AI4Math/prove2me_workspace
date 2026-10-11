"""Run our own native semantic control after the serial SOURCE/oracle phase."""
import argparse, sys
from pathlib import Path
import inspect_author as p
import run_phase1 as engine

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    parser=argparse.ArgumentParser(); parser.add_argument('--parent-lane2-authorized',action='store_true',required=True); parser.parse_args()
    terminal=p.load(p.OUT/'phase1-terminal.json')
    assert terminal['success_calls']==45 and terminal['all_actual_handles_terminal']
    receipt=p.OUT/'execution-receipt.json'
    checkpoint=p.OUT/'immutable-phase1-execution-receipt.json'
    if checkpoint.exists():
        assert len(p.load(checkpoint)['rows'])==45
    else:
        checkpoint.write_bytes(receipt.read_bytes())
    assert p.sha(checkpoint)==terminal['receipt']['sha256']
    prepared=p.load(p.OUT/'native-control-preparation-v2.json')
    p.check([prepared[k] for k in ['own_graph','selection','independent_mathematical_spec','source','source_snapshot']])
    engine.build('independent-native-semantic','PFIndependentNativeV2','PFIndependentNativeV2.lean')
    engine.dump(p.OUT/'native-semantic-terminal.json',dict(
        status='OWN_NATIVE_SEMANTIC_ACTUAL0_STAGED_REVIEW_STILL_REQUIRED',
        driver=p.bind(Path(__file__)),immutable_phase1_receipt=p.bind(checkpoint),
        native_control=prepared['source'],independent_PASS_claimed=False))
    print('Own native semantic control completed actual0; no platform independent PASS yet.',flush=True)

if __name__=='__main__':main()
