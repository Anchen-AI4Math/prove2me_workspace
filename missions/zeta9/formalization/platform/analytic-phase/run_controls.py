import sys
import inspect_prepare as p
import run_sources as engine
sys.stdout.reconfigure(encoding='utf-8')
assert p.load(p.OUT/'source-terminal.json')['all_actual_handles_terminal']
plan=p.load(p.OUT/'control-preparation.json')
for context in plan['contexts']:
 for row in context['rows']:
  p.check([row['binding']]);engine.run(context['tag'],row['label'],row['module'],row['path'])
p.dump(p.OUT/'controls-terminal.json',dict(status='FOUR_ISOLATED_CONTEXTS_COMPLETE_34_FORALL_7_VALUES_RFL_HELPER_BOUNDARY_AND_IMPORT_CONTROLS_ACTUAL0',all_actual_handles_terminal=True,author_PASS_claimed=False,API_calls=0))
