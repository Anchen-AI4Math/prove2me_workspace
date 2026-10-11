"""Fresh independent first phase; forbidden before parent lane and Root5 freeze."""
from run_step import *
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--parent-lane-authorized', action='store_true')
options = parser.parse_args()
assert options.parent_lane_authorized, 'Await explicit parent Lean lane allocation'
verify()
enrollment = load(OUT / 'execution-preparation.json')
assert enrollment['all_planned_object_paths_plus64_below260']
assert not BUILD.exists(), 'No borrowed, old or author proof objects allowed'
run('native pure Harmonic Definition', PROJECT / 'Definitions/Def_ZetaNine_HarmonicStability.lean', N,
    N / 'Definitions/Def_ZetaNine_HarmonicStability.olean')
for name in enrollment['native_order']:
    run('native ' + name, PROJECT / 'missions/zeta9/formalization' / (name + '.lean'), N,
        N / 'missions/zeta9/formalization' / (name + '.olean'))
for module in enrollment['control_modules']:
    run('native control ' + module, PROJECT / (module + '.lean'), N, N / (module + '.olean'))
for name in enrollment['true_Def_compile_order']:
    relative = 'Definitions/Def_ZetaNine_' + name + '.lean'
    run('pure Definition ' + name, PROJECT / relative, P, P / (relative.removesuffix('.lean') + '.olean'))
for context, cache in [('native', N), ('staged', P)]:
    alias_name = 'NativeValueComparisonDefinition' if context == 'native' else 'StagedValueComparisonDefinition'
    run(context + ' Aggregate alias', PROJECT / (alias_name + '.lean'), cache, cache / (alias_name + '.olean'))
    run(context + ' Aggregate six actual full-kernel and nine closed equalities',
        OUT / ('aggregate-' + context + '-values.lean'), cache)
receipt = load(OUT / 'review-compile-receipt.json')
assert len(receipt['rows']) == 29 and all(r['exit_code'] == 0 for r in receipt['rows'])
dump(OUT / 'fresh-source-summary.json', {'complete': True, 'actual_successful_Lean_invocations': 29,
    'own_native_and_platform_caches_separate': True, 'Root_or_author_objects_borrowed': False})
print('Fresh native11, trueDef11, native37/56 and both Aggregate value environments complete.', flush=True)
