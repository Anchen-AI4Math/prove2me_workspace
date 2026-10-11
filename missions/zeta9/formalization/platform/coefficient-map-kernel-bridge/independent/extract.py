"""Execute the actual official declaration graph, source/ref/header oracles."""
from run_step import *

verify()
assert load(OUT / 'fresh-source-summary.json')['complete']
enrollment = load(OUT / 'execution-preparation.json')
run('actual independent Stage1 graph', OUT / 'g.lean', N)
for name in enrollment['native_order'] + ['HarmonicStability']:
    source = PROJECT / ('Definitions/Def_ZetaNine_HarmonicStability.lean' if name == 'HarmonicStability'
                        else 'missions/zeta9/formalization/' + name + '.lean')
    run('actual independent Stage2 ' + name, OUT / ('parse-' + name + '.lean'), N,
        args=[source.as_posix(), 'ZetaNine'], copy=OUT / (name + '-facts.jsonl'))
for module in enrollment['control_modules']:
    run('actual independent control parser ' + module, OUT / ('parse-' + module + '.lean'), N,
        args=[(PROJECT / (module + '.lean')).as_posix(), 'ZetaNine'], copy=OUT / (module + '-facts.jsonl'))
run('actual independent header', OUT / 'extract_header.lean', N,
    args=[(PROJECT / 'missions/zeta9/formalization/CoefficientMapKernelBridge.lean').as_posix()],
    copy=OUT / 'header.jsonl')
dump(OUT / 'extraction-summary.json', {'complete': True,
    'actual_graph_records': len(rows(OUT / 'decl_graph.jsonl')), 'source_Stage2_runs': 12,
    'native_control_Stage2_runs': 2, 'header_runs': 1, 'no_author_objects': True})
