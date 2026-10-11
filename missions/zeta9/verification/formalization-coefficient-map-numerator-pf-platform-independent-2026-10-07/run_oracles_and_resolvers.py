import sys
import inspect_author as p
import run_phase1 as engine
sys.stdout.reconfigure(encoding='utf-8')
assert p.load(p.OUT/'staged-semantic-terminal-v2.json')['all_three_actual_exit0']
plan=p.load(p.OUT/'oracle-resolver-preparation.json')
for row in plan['parser_payloads']:
    p.check([row['project_copy'],row['snapshot']])
    engine.run('official-payload-parser-'+row['module'].rsplit('.',1)[-1],['--run','PFIndependentParser.lean',row['project_relative'],'ZetaNine'])
for row in plan['graphs']:
    p.check([row['source'],row['snapshot']])
    engine.run('official-staged-graph-'+row['context'],[row['project_relative']],[row['output']])
for kind in ['resolvers','references']:
    for row in plan[kind]:
        p.check([row['source'],row['snapshot']])
        engine.build('independent-'+kind+'-'+row['context'],row['module'],row['project_relative'])
engine.dump(p.OUT/'oracle-resolver-terminal.json',dict(status='OWN_PAYLOAD_ORACLES_CONTEXTUAL_GRAPHS_RESOLVERS_REFERENCE_TYPES_ACTUAL0',
    driver=p.bind(p.OUT/'run_oracles_and_resolvers.py'),preparation=p.bind(p.OUT/'oracle-resolver-preparation.json'),
    actual_findOLean_and_module_header_checks=108,reference_stubs_type_checked_only=3,independent_PASS_claimed=False))
