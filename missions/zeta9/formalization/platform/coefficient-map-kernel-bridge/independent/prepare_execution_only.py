"""Prepare fresh independent replay programs; executes no Lean/Lake."""
from verify_handoff import *
import re

verify(require_root=False)
assert not BUILD.exists(), 'Preparation requires the independent cache to remain absent'
prep = load(OUT / 'preparation-state.json')
order = list(load(BATCH / 'preparation-state.json')['sources_sha256'])
assert len(order) == 11 and order[-1] == 'CoefficientMapKernelBridge'
for name, original in [('NativeKernelAuthorControl', OUT / 'native-control-author.lean'),
                       ('NativeKernelIndependentControl', OUT / 'native-control-independent.lean')]:
    write(PROJECT / (name + '.lean'), original.read_bytes())

graph = (BATCH / 'extract_decl_graph.lean').read_text(encoding='utf-8-sig')
for name in ['decl_graph.jsonl', 'lean-path-selected.json']:
    old = '"../' + name + '"'
    assert graph.count(old) == 1
    graph = graph.replace(old, '"' + (OUT / name).as_posix() + '"')
write(OUT / 'g.lean', graph)
for suffix in ['NativeValueComparisonDefinition', 'StagedValueComparisonDefinition',
               'NativeKernelValueComparisonDefinition', 'StagedKernelValueComparisonDefinition']:
    write(PROJECT / (suffix + '.lean'), (BATCH / 'p' / (suffix + '.lean')).read_bytes())
for prefix in ['aggregate', 'kernel']:
    for context in ['native', 'staged']:
        source = BATCH / 'p' / (prefix + '-' + context + '-value-details.lean')
        assert source.exists()
        write(OUT / (prefix + '-' + context + '-values.lean'), source.read_bytes())
        write(PROJECT / (prefix + '-' + context + '-value-details.lean'), source.read_bytes())

modules = ['missions.zeta9.formalization.' + name for name in order]
modules += ['NativeKernelAuthorControl', 'NativeKernelIndependentControl',
            'NativeValueComparisonDefinition', 'StagedValueComparisonDefinition',
            'NativeKernelValueComparisonDefinition', 'StagedKernelValueComparisonDefinition']
modules += [r['root_relative'].removesuffix('.lean').replace('/', '.')
            for r in prep['source_and_pure_Definition_bindings'] if r['root_relative'].startswith('Definitions/')]
modules += [r['root_relative_destination'].removesuffix('.lean').replace('/', '.')
            for r in load(BATCH / 'root-copy-plan.json')['files']]
guards = []
for cache in [N, P]:
    for module in modules:
        object_path = cache / (module.replace('.', '/') + '.olean.private')
        guards.append({'module': module, 'path': str(object_path), 'characters': len(str(object_path)),
                       'temporary_suffix_margin': 64, 'path_plus_64': len(str(object_path)) + 64,
                       'pass': len(str(object_path)) + 64 <= 259})
assert all(r['pass'] for r in guards)
dump(OUT / 'execution-preparation.json', {'status': 'NO_LEAN_EXECUTED', 'actual_Lean_Lake_invocations': 0,
    'native_order': order, 'control_modules': ['NativeKernelAuthorControl', 'NativeKernelIndependentControl'],
    'true_Def_compile_order': ['HarmonicStability'] + order[:-1],
    'source_programs_only_copied_no_objects': True, 'independent_cache_absent': True,
    'all_planned_object_paths_plus64_below260': True, 'path_guards': guards,
    'actual_max_path_plus64': max(r['path_plus_64'] for r in guards),
    'first_phase_expected_successes': 29, 'root_freeze_and_explicit_parent_lane_grant_required': True})
print('Independent replay execution programs prepared, no Lean/Lake; guarded maximum',
      max(r['path_plus_64'] for r in guards), flush=True)
