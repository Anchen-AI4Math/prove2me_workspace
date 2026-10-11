"""Native SOURCE validation before using any constructor snapshot in stages."""
import sys
import inspect_author as p
import run_phase1 as engine
sys.stdout.reconfigure(encoding='utf-8')
plan=p.load(p.OUT/'staged-control-preparation-v2.json')
p.check([plan['captures'],plan['original_raw_capture'],plan['encoder_stdout']])
native=plan['native_roundtrip']; p.check([native['source'],native['snapshot']])
engine.build('independent-native-lossless-roundtrip',native['module'],native['project_relative'])
for row in plan['controls']:
    p.check([row['source'],row['snapshot']])
    engine.build('independent-staged-semantic-v2-'+row['suffix'],row['module'],row['project_relative'])
engine.dump(p.OUT/'staged-semantic-terminal-v2.json',dict(status='NATIVE_LOSSLESS_SOURCE_AND_THREE_STAGED_SEMANTIC_CONTROLS_ACTUAL0',
    driver=p.bind(p.OUT/'run_staged_controls_v2.py'),preparation=p.bind(p.OUT/'staged-control-preparation-v2.json'),
    native_roundtrip_Expr_equal_isDefEq57=True,all_three_actual_exit0=True,independent_PASS_claimed=False))
