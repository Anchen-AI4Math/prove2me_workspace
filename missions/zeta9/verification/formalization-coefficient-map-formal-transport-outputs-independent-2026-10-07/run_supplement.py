import sys
import inspect_prepare as p
import run_sources as engine
sys.stdout.reconfigure(encoding='utf-8')
assert p.load(p.OUT/'semantic-terminal-v3.json')['semantic_exit0']
plan=p.load(p.OUT/'generated-closure-preparation.json')
r=plan['source'];p.check([r['source'],r['snapshot']]);engine.build('independent-all-generated-closure-v1',r['module'],r['project_relative'])
plan=p.load(p.OUT/'resolution-preparation-v2.json')
r=plan['source'];p.check([r['source'],r['snapshot']]);engine.build('independent-actual-resolution-v2',r['module'],r['project_relative'])
p.dump(p.OUT/'supplement-terminal.json',dict(status='ALL_MODULE_DECLARATION_STD3_GENERATED_HELPERS_AND_26_ACTUAL_OWN_RESOLUTIONS_ACTUAL0',driver=p.bind(p.OUT/'run_supplement.py'),all_generated_closure_exit0=True,actual_resolution_exit0=True,independent_PASS_claimed=False))
