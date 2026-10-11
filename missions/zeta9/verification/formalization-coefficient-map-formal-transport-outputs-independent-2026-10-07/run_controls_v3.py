import sys
import inspect_prepare as p
import run_sources as engine
sys.stdout.reconfigure(encoding='utf-8')
assert p.load(p.OUT/'native-source-terminal.json')['actual_SOURCE_modules']==21
recovery=p.load(p.OUT/'recovery-inspection-v4.json')
assert recovery['verdict']=='PASS_PREVIOUS_INDEPENDENT_SOURCE_RUNS_REVALIDATED'
assert all(x['passed'] for x in recovery['checks'])
plan=p.load(p.OUT/'control-preparation-v3.json')
for kind in ['assertions','semantic']:
 r=plan[kind];p.check([r['source'],r['snapshot']]);engine.build('independent-'+kind+'-v3',r['module'],r['project_relative'])
p.dump(p.OUT/'semantic-terminal-v3.json',dict(status='OWN_FULL_FORALL_DEFINITION_BOUNDARY_AND_HELPER_CONTROLS_ACTUAL0',driver=p.bind(p.OUT/'run_controls_v3.py'),control_preparation=p.bind(p.OUT/'control-preparation-v3.json'),assertions_exit0=True,semantic_exit0=True,independent_PASS_claimed=False))
