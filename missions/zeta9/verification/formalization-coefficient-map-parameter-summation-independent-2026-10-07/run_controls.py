import sys
import inspect_prepare as p
import run_sources as engine
sys.stdout.reconfigure(encoding='utf-8')
assert p.load(p.OUT/'native-source-terminal.json')['actual_SOURCE_modules']==22
plan=p.load(p.OUT/'control-preparation.json')
for kind in ['assertions','semantic','generated']:
 r=plan[kind];p.check([r['source'],r['snapshot']]);engine.build('independent-'+kind+'-v1',r['module'],r['project_relative'])
plan=p.load(p.OUT/'resolution-preparation.json');r=plan['source'];p.check([r['source'],r['snapshot']]);engine.build('independent-actual-resolution-v1',r['module'],r['project_relative'])
p.dump(p.OUT/'control-terminal.json',dict(status='OWN_17_FORALL_FULL_DEFINITION_RFL_9_BOUNDARIES_ALL_GENERATED_VALUES_AND27_OBJECT_RESOLUTIONS_ACTUAL0',driver=p.bind(p.OUT/'run_controls.py'),assertions_exit0=True,semantic_exit0=True,generated_exit0=True,resolution_exit0=True,independent_PASS_claimed=False))
