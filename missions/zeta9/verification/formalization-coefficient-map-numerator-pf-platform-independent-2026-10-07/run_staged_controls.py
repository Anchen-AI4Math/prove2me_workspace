"""Serial lane2 actual compilation of independently generated staged controls."""
import sys
import inspect_author as p
import run_phase1 as engine

def main():
    sys.stdout.reconfigure(encoding='utf-8')
    plan=p.load(p.OUT/'staged-control-preparation.json')
    p.check([plan['native_actual_stdout'],plan['semantic_spec'],plan['selection']])
    for row in plan['controls']:
        p.check([row['source'],row['source_snapshot']])
        engine.build('independent-staged-semantic-'+row['suffix'],row['module'],row['project_relative'])
    engine.dump(p.OUT/'staged-semantic-terminal.json',dict(status='THREE_ISOLATED_STAGED_SEMANTIC_CONTROLS_ACTUAL0',
        driver=p.bind(p.OUT/'run_staged_controls.py'),preparation=p.bind(p.OUT/'staged-control-preparation.json'),
        all_three_actual_exit0=True,independent_PASS_claimed=False))

if __name__=='__main__':main()
