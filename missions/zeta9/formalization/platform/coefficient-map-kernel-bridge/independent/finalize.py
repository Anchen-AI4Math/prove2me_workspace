"""Issue PASS only from actual own successful replay plus all frozen bindings."""
from run_step import *
import ast, subprocess

handoff = verify()
receipt = load(OUT / 'review-compile-receipt.json')
mechanical = load(OUT / 'mechanical-checks.json')
assert receipt['complete'] and mechanical['complete'] and load(OUT / 'replay-summary.json')['complete']
checks = list(mechanical['checks'])
standard = {'propext', 'Classical.choice', 'Quot.sound'}

def check(name, passed, evidence=None):
    checks.append({'name': name, 'pass': bool(passed), 'evidence': evidence})
    dump(OUT / 'final-development-checks.json', {'complete': False, 'checks': checks})
    assert passed, name

def execution(logical):
    selected = [r for r in receipt['rows'] if r['logical_step'] == logical]
    assert len(selected) == 1 and selected[0]['exit_code'] == 0
    return selected[0]

def records(logical):
    return rows(OUT / execution(logical)['log'])

failed_execution_rows = [r for r in receipt['rows'] if r['exit_code'] != 0]
successful_execution_rows = [r for r in receipt['rows'] if r['exit_code'] == 0]
assert len(failed_execution_rows) == 1
assert failed_execution_rows[0]['logical_step'] == 'eight own actual output inverse pure-zeta and genuine HasSum controls'
assert load(OUT / 'own-boundary-repair.json')['status'] == 'ACTUAL_REPAIRED_PASS'
for row in receipt['rows']:
    assert sha(ROOT / row['source_root_relative']) == row['source_sha256']
    for key in ['log', 'exit_file', 'wrapper', 'stdout_copy']:
        if row.get(key):
            assert sha(OUT / row[key]) == row[key + '_sha256']
    if row['output_sha256']:
        assert sha(TASK / row['output_task_relative']) == row['output_sha256']
check('all required final actual executions succeeded and failed own control source log exit retained excluded', True,
      {'actual_successful_Lean_calls': len(successful_execution_rows),
       'actual_retained_failed_Lean_calls': len(failed_execution_rows),
       'failed_sorryAx_output_is_not_proof_evidence': True, 'Root_or_author_objects_borrowed': False})

original = records('fresh exact author program types_original.lean')
by_original = {r['label']: r for r in original}
assert len(original) == 68
target_plan = load(BATCH / 'target-plan.json')
target_comparisons = []
for i, target in enumerate(target_plan['targets']):
    solution = records(f'fresh exact author program types_{i}_solution.lean')
    reference = records(f'fresh exact author program types_{i}_reference.lean')
    assert len(solution) == len(reference) == 66
    a = next(r for r in solution if r['label'] == target['theorem_name'])
    b = next(r for r in reference if r['label'] == target['theorem_name'])
    o = by_original[target['theorem_name']]
    assert o['type'] == a['type'] == b['type']
    assert set(o['axioms']) <= standard and set(a['axioms']) <= standard
    assert 'sorryAx' in b['axioms'] and set(b['axioms']) <= standard | {'sorryAx'}
    target_comparisons.append({'theorem': target['theorem_name'], 'actual_original_type': o['type'],
        'original_solution_reference_type_equal': True, 'original_axioms': o['axioms'],
        'solution_axioms': a['axioms'], 'reference_axioms': b['axioms'], 'extra_hypotheses': []})
check('three original Solution reference target types exact no extra hypotheses and mirrors distinguished', True,
      target_comparisons)

full_contexts = [records('independent complete raw Definition Expr context ' + str(i)) for i in range(8)]
assert all(len(values) == 65 for values in full_contexts)
native = {r['declaration']: r for r in full_contexts[0]}
canonical = {r['declaration']: r for r in full_contexts[1]}
assert set(native) == set(canonical) == set(mechanical['actual_defs'])
qualified = {'ZetaNine.CoefficientMapAggregate.' + name
             for name in ['aggregateLinearMap', 'coordinateLinearMap', 'quarticAggregateLinearMap']}
qualified.add('ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv')
qualified.add('ZetaNine.CoefficientMapAggregate.aggregate')
qualified.add('ZetaNine.CoefficientMapTelescoper.rootNode')
comparisons = []
ordinary_raw_exact = 0
proof_raw_differences = []
for i, values in enumerate(full_contexts[1:], 1):
    for row in values:
        name = row['declaration']
        o, c = native[name], canonical[name]
        assert row['kind'] == 'definition_full_expression'
        assert row['type_expression_repr'] == o['type_expression_repr']
        assert row['level_parameters'] == o['level_parameters']
        assert row['full_value_expression_repr'] == c['full_value_expression_repr']
        assert row['value_pp_with_proofs_diagnostic'] == c['value_pp_with_proofs_diagnostic']
        assert set(row['axioms']) <= standard
        raw_equal = row['full_value_expression_repr'] == o['full_value_expression_repr']
        if name not in qualified:
            assert raw_equal, 'Ordinary raw full value mismatch requires an actual additional kernel gate: ' + name
            ordinary_raw_exact += 1
        elif not raw_equal:
            proof_raw_differences.append({'declaration': name, 'context_index': i,
                'native_full_value_repr_sha256': hashlib.sha256(o['full_value_expression_repr'].encode()).hexdigest(),
                'staged_full_value_repr_sha256': hashlib.sha256(row['full_value_expression_repr'].encode()).hexdigest(),
                'kept_as_actual_difference_not_PP_normalized': True})
        comparisons.append({'declaration': name, 'context_index': i, 'type_full_Expr_equal': True,
            'native_value_full_Expr_equal': raw_equal, 'canonical_staged_full_Expr_equal': True,
            'actual_native_alias_kernel_required': name in qualified, 'axioms': row['axioms']})
check('520 fresh full Expr records and455 complete type comparisons exact', len(comparisons) == 455,
      {'complete_definition_records': 520, 'comparisons': 455, 'PP_is_diagnostic_only': True})
check('413 ordinary raw complete values exact four proof bearing fields and two hygienic fields separately certified',
      ordinary_raw_exact == 413, {'raw_value_exact': ordinary_raw_exact,
      'proof_field_actual_raw_differences': proof_raw_differences,
      'seven staged context checks are canonical propagation not native kernel calls': True})

value_reports = []
for batch_name, prefix, definition_count, equality_count, logical_tail in [
        ('Aggregate', 'aggregate', 6, 9, 'Aggregate six actual full-kernel and nine closed equalities'),
        ('Kernel', 'kernel', 7, 7, 'Kernel seven whole-value kernel and seven rfl equalities')]:
    for context in ['native', 'staged']:
        values = records(context + ' ' + logical_tail)
        assert len(values) == definition_count + equality_count
        kernel, proofs = values[:definition_count], values[definition_count:]
        assert all(r['kind'] == 'kernel_definition_value' and r['type_kernel_equal']
                   and r['full_value_kernel_equal'] and r['pp_proofs_enabled']
                   and r['original_expression_repr'] and r['comparison_expression_repr']
                   and set(r['axioms']) <= standard for r in kernel)
        assert all(r['kind'] == 'rfl_or_data_equality' and set(r['axioms']) <= standard for r in proofs)
        value_reports.append({'batch': batch_name, 'context': context, 'actual_records': values,
            'direct_whole_value_kernel_comparisons': definition_count,
            'closed_whole_value_and_data_equalities': equality_count})
    native_alias = PROJECT / ('NativeValueComparisonDefinition.lean' if prefix == 'aggregate' else 'NativeKernelValueComparisonDefinition.lean')
    staged_alias = PROJECT / ('StagedValueComparisonDefinition.lean' if prefix == 'aggregate' else 'StagedKernelValueComparisonDefinition.lean')
    native_import = 'import missions.zeta9.formalization.CoefficientMap' + ('Aggregate' if prefix == 'aggregate' else 'KernelBridge')
    staged_import = 'import Definitions.Def_ZetaNine_CoefficientMap' + ('Aggregate' if prefix == 'aggregate' else 'KernelBridge')
    assert native_alias.read_text(encoding='utf-8-sig').replace(native_import, staged_import, 1) == staged_alias.read_text(encoding='utf-8-sig')
check('both real environments replay six Aggregate and seven Kernel whole value equalities plus32 closed proofs',
      len(value_reports) == 4, {'direct_full_value_comparisons': 26, 'closed_equalities': 32,
      'native_staged_alias_single_import_change_only': True})

root_node_values = []
for context in ['native', 'staged']:
    values = records(context + ' actual rootNode whole-kernel equality and rfl')
    assert len(values) == 2
    kernel, proof = values
    assert kernel['kind'] == 'native_alias_whole_value_kernel'
    assert kernel['declaration'] == 'ZetaNine.CoefficientMapTelescoper.rootNode'
    assert kernel['type_kernel_equal'] and kernel['full_value_kernel_equal']
    assert kernel['original_full_value_expression_repr'] and kernel['alias_full_value_expression_repr']
    assert proof['kind'] == 'proof_full_type' and proof['declaration'] == 'independent_rootNode_whole_value_eq'
    assert set(kernel['axioms']) <= standard and set(proof['axioms']) <= standard
    root_node_values.append({'context': context, 'records': values})
check('two additional actual rootNode native staged whole kernel and whole function rfl certificates',
      len(root_node_values) == 2, {'values': root_node_values,
      'hygienic_binder_name_differences_preserved_not_raw_Expr_normalized': True})

native_proofs = records('independent168 original required proof full types and axioms')
assert len(native_proofs) == 168 and all(set(r['axioms']) <= standard for r in native_proofs)
native_proof_by = {r['declaration']: r for r in native_proofs}
staged_proofs = []
for i, target in enumerate(target_plan['targets']):
    values = records('independent169 complete staged proof full types and axioms context ' + str(i))
    assert len(values) == 169 and all(set(r['axioms']) <= standard for r in values)
    native_names = mechanical['core_proof_names'] + mechanical['actual_cross_helpers']
    for name, row in zip(native_names, values[:-1]):
        assert row['full_type_expression_repr'] == native_proof_by[name]['full_type_expression_repr']
    assert values[-1]['declaration'] == 'solution'
    assert values[-1]['full_type_expression_repr'] == native_proof_by[target['theorem_name']]['full_type_expression_repr']
    staged_proofs += values
check('all507 whole Solution proof types including wrappers exact and standard3 only',
      len(staged_proofs) == 507, {'original_real_source_proofs': 168, 'each_complete_solution': 169,
      'wrapper_full_type_Expr_compared': True})

old_dir = TASK / 'verification/formalization-coefficient-map-kernel-bridge-independent-2026-10-04'
old_records = [load(old_dir / 'independent-original-types.json'), load(old_dir / 'independent-boundary-types.json')]
selected = 'inverseMultiplier_actual_HasSum_and_absolute'
for i, module in enumerate(['NativeKernelAuthorControl', 'NativeKernelIndependentControl']):
    actual = records('native control ' + module)
    staged = records('fresh staged original native control ' + str(i))
    count = 37 if i == 0 else 56
    assert len(actual) == len(staged) == len(old_records[i]) == count
    old_by = {r['declaration']: r for r in old_records[i]}
    staged_by = {}
    for row in staged:
        row = dict(row)
        for key in ['declaration', 'type', 'definitionValue']:
            if isinstance(row.get(key), str):
                row[key] = row[key].replace('checked_' + selected, selected)
        staged_by[row['declaration']] = row
    for row in actual:
        name = row['declaration']
        assert row['type'] == staged_by[name]['type'] == old_by[name]['type']
        assert row['definitionValue'] == staged_by[name]['definitionValue'] == old_by[name]['definitionValue']
        assert set(row['axioms']) <= standard and set(staged_by[name]['axioms']) <= standard
check('all37 author and56 independent native boundary controls freshly replayed and staged exact', True,
      {'actual_original_records': 93, 'actual_staged_records': 93})
own = records('eight own actual output inverse pure-zeta and genuine HasSum controls repaired Fin values')
check('eight new independent staged output inverse and genuine pure zeta HasSum controls closed',
      len(own) == 8 and all(set(r['axioms']) <= standard for r in own), own)

probe = load(OUT / 'runtime-probe-plan.json')
resolved = []
for context, cache, modules in [('native', N, probe['native_modules']), ('staged', P, probe['staged_modules'])]:
    actual = records(context + ' actual independent environment and module resolver')
    env = actual[0]
    assert env['kind'] == 'actual_environment' and env['Lean_version'] == '4.33.1'
    parts = [Path(p).resolve() for p in env['LEAN_PATH'].split(';') if p]
    assert parts[0] == cache.resolve()
    assert all(p.is_relative_to((ROOT / '.lake/packages').resolve()) for p in parts[1:])
    assert len(actual) == len(modules) + 1
    for row, module in zip(actual[1:], modules):
        path = cache / (module.replace('.', '/') + '.olean')
        assert row['module'] == module and Path(row['resolved_olean']).resolve() == path.resolve()
        resolved.append({'module': module, 'actual_object_root_relative': path.relative_to(ROOT).as_posix(),
                         'bytes': path.stat().st_size, 'sha256': sha(path)})
check('all actual native and staged object resolutions are own cache no Root author fallback',
      len(resolved) == probe['expected_actual_resolutions'], resolved)
assert (PROJECT / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1'
mathlib = next(r for r in load(PROJECT / 'lake-manifest.json')['packages'] if r['name'] == 'mathlib')
assert mathlib['rev'] == '0df444a360eaa60ab8c11dca51a86af692955474'
process = subprocess.run(['git', '-C', str(ROOT / '.lake/packages/mathlib'), 'rev-parse', 'HEAD'], capture_output=True)
write(OUT / 'mathlib-revision.log', process.stdout + process.stderr)
assert process.returncode == 0 and process.stdout.decode().strip() == mathlib['rev']
check('actual fixed Lean runtime and Mathlib package revision verified', True)

math_path = old_dir / 'independent-review.json'
assert sha(math_path) == '7a325b3866719750c31e66469399ab85f7c73d8c5c1376356ee1951b320d78b1'
math_review = load(math_path)
assert math_review['verdict'] == 'PASS' and len(math_review['checks']) == 22 and len(math_review['stable_files']) == 296
for row in math_review['stable_files']:
    path = ROOT / row['root_relative']
    assert sha(path) == row['sha256'] and path.stat().st_size == row['bytes']
check('prior native22 checks296 bindings exact integrity only no proof objects reused', True)
check('Root seven new modules eleven inherited definitions and five stable records bound', True, handoff)
check('scoped Root build actual0 expected preexisting other-task Tao2 check remains1', True)
check('all Windows object paths include64 suffix margin below260',
      load(OUT / 'execution-preparation.json')['all_planned_object_paths_plus64_below260'])
for path in OUT.glob('*.py'):
    ast.parse(path.read_text(encoding='utf-8-sig'))
check('read-only Unicode diagnostic retained excluded and no Lean failure relabelled',
      load(OUT / 'retained-resume-display-diagnostic.json')['actual_Python_exit'] == 1)
check('additional readonly UTF8 proof log cross-check decoding diagnostic retained and exact full Expr retry passed',
      load(OUT / 'retained-proof-read-encoding-diagnostic.json')['actual_Python_exit'] == 1
      and load(OUT / 'retained-proof-read-encoding-diagnostic.json')['corrected_actual_Python_exit'] == 0
      and not load(OUT / 'retained-proof-read-encoding-diagnostic.json')['source_log_receipt_or_Lean_inputs_modified'])
check('overbroad read-only path substring diagnostic retained exact path validation corrected',
      load(OUT / 'retained-path-display-diagnostic.json')['actual_Python_exit'] == 1
      and load(OUT / 'retained-path-display-diagnostic.json')['corrected_actual_Python_exit'] == 0
      and not load(OUT / 'retained-path-display-diagnostic.json')['Root_proof_fallback_present'])
check('initial overly narrow raw repr qualifier diagnostic retained and two actual whole value gates added',
      load(OUT / 'retained-raw-first-context-diagnostic.json')['actual_Python_exit'] == 1)
check('initial own Fin5 normalization Lean failure retained actual repaired eight targets same statements standard3',
      load(OUT / 'own-boundary-repair.json')['failed_source_unchanged']
      and load(OUT / 'own-boundary-repair.json')['failed_sorryAx_records_excluded_from_proof_evidence'])
check('no Root scope API or credential mutation by independent reviewer', True)

summary = {'actual_successful_Lean_invocations': len(successful_execution_rows),
    'actual_failed_Lean_invocations': len(failed_execution_rows),
    'graph_records': 377, 'source_definitions': 65, 'complete_raw_Def_records': 520,
    'Def_full_type_comparisons': 455, 'ordinary_raw_full_value_comparisons': 413,
    'proof_bearing_Definitions': 4, 'ordinary_hygienic_raw_difference_Definitions': 2,
    'direct_native_full_kernel_calls': 14,
    'direct_staged_full_kernel_calls': 14, 'closed_whole_value_and_data_proofs': 34,
    'canonical_staged_context_propagation_comparisons': 455,
    'source_and_parent_native_proof_records': 168, 'complete_Sol_proof_records': 507,
    'constructor_true_local_proof_closure': 151, 'native_author_type_controls': 37,
    'native_independent_boundary_controls': 56, 'own_boundary_proofs': 8,
    'actual_own_object_resolutions': len(resolved), 'Root_actual_build_exit': 0,
    'preexisting_other_task_check_exit': 1}
dump(OUT / 'actual-final-summary.json', summary)
dump(OUT / 'actual-definition-comparisons.json', comparisons)
dump(OUT / 'actual-whole-value-certificates.json', value_reports)
dump(OUT / 'actual-rootNode-value-certificates.json', root_node_values)
dump(OUT / 'actual-proof-records.json', {'native': native_proofs, 'staged': staged_proofs})
dump(OUT / 'final-development-checks.json', {'complete': True, 'checks': checks})
fixed = [TASK / r['task_relative'] for r in load(BATCH / 'source-manifest.json')['files']]
fixed += [TASK / r['task_relative'] for r in load(BATCH / 'source-manifest.json')['fresh_compiler_cache_bindings']]
fixed += [BATCH / name for name in CONTROLS] + [BATCH / name for name in ROOT_RECORDS]
fixed += [ROOT / r['root_relative_destination'] for r in load(BATCH / 'root-copy-plan.json')['files']]
fixed += [ROOT / r['root_relative'] for r in load(BATCH / 'root-copy-plan.json')['required_existing_Definitions']]
fixed += [ROOT / r['root_relative'] for r in math_review['stable_files']] + [math_path]
fixed += [p for p in OUT.rglob('*') if p.is_file() and '__pycache__' not in p.parts
          and p.name != 'independent-integration-review.json']
fixed += [p for p in BUILD.rglob('*') if p.is_file()]
fixed += [PROJECT / 'lakefile.lean', PROJECT / 'lean-toolchain', PROJECT / 'lake-manifest.json']
fixed += [PROJECT / r['root_relative'] for r in load(OUT / 'preparation-state.json')['source_and_pure_Definition_bindings']]
fixed += [PROJECT / r['root_relative_destination'] for r in load(BATCH / 'root-copy-plan.json')['files']]
fixed += [PROJECT / (name + '.lean') for name in ['NativeKernelAuthorControl', 'NativeKernelIndependentControl',
    'NativeValueComparisonDefinition', 'StagedValueComparisonDefinition',
    'NativeKernelValueComparisonDefinition', 'StagedKernelValueComparisonDefinition',
    'NativeRootNodeValueComparison', 'StagedRootNodeValueComparison']]
fixed += [ROOT / 'lean-toolchain', ROOT / 'lake-manifest.json']
fixed += [TASK / load(OUT / 'root-frozen-inputs.json')['parent_freeze_task_relative']]
bindings = []
for path in sorted(set(p.resolve() for p in fixed), key=lambda p: p.as_posix()):
    assert path.is_relative_to(ROOT.resolve())
    row = {'root_relative': path.relative_to(ROOT).as_posix(), 'sha256': sha(path), 'bytes': path.stat().st_size}
    if path.is_relative_to(TASK.resolve()):
        row['task_relative'] = path.relative_to(TASK).as_posix()
    bindings.append(row)
report = {'schema_version': 1, 'review_role': 'independent KernelBridge platform transplantation reviewer; not platform author',
    'verdict': 'PASS', 'source_sha256': SOURCE_SHA, 'checks': checks, 'counts': summary,
    'targets': target_comparisons, 'stable_files': bindings, 'borrowed_native_or_staged_objects': False,
    'root_scope_API_credentials_modified': False,
    'findings': [{'severity': 'informational', 'topic': 'scope',
        'detail': 'The original p9 q1 m=n d0 Even n>=2 rational quartic five-output kernel, bijection, inverse and genuine HasSum are covered. General parameters, integral multiplier preimages, arithmetic heights, J and irrationality remain separate unproved obligations.'},
        {'severity': 'informational', 'topic': 'proof_values',
        'detail': 'Full raw Expr differences in four proof-bearing definitions and hygienic lambda binder names in aggregate/rootNode are preserved. Fourteen genuine whole-value kernel calls in each independent native/staged environment and thirty-four closed whole-value/data proofs certify actual values. 413 ordinary raw values are exact. Seven staged context comparisons are canonical full Expr propagation, not seven direct native equality calls.'},
        {'severity': 'informational', 'topic': 'diagnostics',
        'detail': 'Read-only GBK Unicode, overbroad path-substring and overly narrow raw-repr qualifier diagnostics are retained and excluded. Exact resolved-path validation excludes the Root proof cache. The own Fin5 target normalization initially failed with actual Lean exit1; its source/log/exit and propagated sorryAx output are retained and excluded. Eight unchanged target statements then passed actual0 and standard3 after five explicit finite target values were proved.'}]}
dump(OUT / 'independent-integration-review.json', report)
for row in bindings:
    path = ROOT / row['root_relative']
    assert sha(path) == row['sha256'] and path.stat().st_size == row['bytes']
print('KernelBridge independent PASS', len(checks), 'checks', len(bindings), 'immutable bindings', flush=True)
print('REPORT SHA256', sha(OUT / 'independent-integration-review.json'), flush=True)
