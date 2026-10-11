"""Freeze only observed actual summation evidence; never rebuild frozen parents."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys

sys.stdout.reconfigure(encoding='utf-8')
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
SOURCE = TASK / 'formalization/CoefficientMapSummation.lean'
OBJECT = SOURCE.with_suffix('.olean')
LOG = SOURCE.with_suffix('.compile.log')
EXIT = SOURCE.with_suffix('.compile-exit.txt')
AUDIT = OUT / 'type-audit.lean'
AUDIT_LOG = OUT / 'type-audit.log'
AUDIT_EXIT = OUT / 'type-audit-exit.txt'
NOTE = TASK / 'research/coefficient-map-summation-2026-10-04.md'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for path in [EXIT, AUDIT_EXIT]:
    assert int(path.read_text(encoding='utf-8-sig').strip()) == 0
source_text = SOURCE.read_text(encoding='utf-8-sig')
source_log = LOG.read_text(encoding='utf-8-sig')
audit_log = AUDIT_LOG.read_text(encoding='utf-8-sig')
for log in [source_log, audit_log]:
    assert ': error:' not in log and 'sorryAx' not in log and ': warning:' not in log
assert not re.search(r'\b(sorry|admit)\b|^axiom\s', source_text, re.M)
printed = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", source_log, re.S)
assert len(printed) == 12
assert all({a.strip() for a in axioms.split(',')} <= STANDARD for _, axioms in printed)
assert OBJECT.stat().st_mtime >= SOURCE.stat().st_mtime
records = [json.loads(line) for line in audit_log.splitlines() if line.startswith('{')]
source_declarations = re.findall(r'^(?:def|theorem) (\w+)', source_text, re.M)
checked = {'checked_original_Eq_four_tsum', 'checked_absolute_and_HasSum',
    'checked_unconditional_finite_odd', 'checked_tail_including_simple_poles',
    'checked_n_zero_X_four_boundary', 'checked_n_zero_X_four_actual_series',
    'checked_n_zero_constant_HasSum'}
expected = {'ZetaNine.CoefficientMapSummation.' + x for x in source_declarations} | checked
assert len(source_declarations) == 24 and len(records) == 31
assert {r['declaration'] for r in records} == expected
assert all(set(r['axioms']) <= STANDARD for r in records)
assert sum(r['definitionValue'] is not None for r in records) == 3
(OUT / 'type-report.json').write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

parents, parent_files = [], []
for name, directory in [
    ('CoefficientMap', 'formalization-coefficient-map-2026-10-03'),
    ('CoefficientMapJet', 'formalization-coefficient-map-jet-2026-10-03'),
    ('CoefficientMapInjectivity', 'formalization-coefficient-map-injectivity-2026-10-03'),
    ('CoefficientMapPartialFractions', 'formalization-coefficient-map-partial-fractions-2026-10-03'),
    ('CoefficientMapReflection', 'formalization-coefficient-map-reflection-2026-10-03'),
    ('CoefficientMapFiniteSum', 'formalization-coefficient-map-finite-sum-2026-10-03')]:
    parent_source = TASK / f'formalization/{name}.lean'
    parent_object = parent_source.with_suffix('.olean')
    parent_receipt = TASK / f'verification/{directory}/compile-receipt.json'
    saved = json.loads(parent_receipt.read_text(encoding='utf-8'))
    assert sha(parent_source) == saved['source_sha256']
    assert sha(parent_object) == saved['source_compile']['object_sha256']
    parents.append({'source': str(parent_source), 'source_sha256': sha(parent_source),
        'object': str(parent_object), 'object_sha256': sha(parent_object),
        'receipt': str(parent_receipt), 'receipt_sha256': sha(parent_receipt)})
    parent_files.extend([parent_source, parent_object, parent_receipt])
    if name == 'CoefficientMapFiniteSum':
        environment = saved['environment']
manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
mathlib_revision = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
assert mathlib_revision == '0df444a360eaa60ab8c11dca51a86af692955474'
assert (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip() == 'leanprover/lean4:v4.33.1'
pure_definition = ROOT / 'Definitions/Def_ZetaNine_HarmonicStability.lean'
pure_definition_object = ROOT / '.lake/build/lib/lean/Definitions/Def_ZetaNine_HarmonicStability.olean'
failed_import_log = OUT / 'import-resolution-root-prefix-failure.log'
failed_import_exit = OUT / 'import-resolution-root-prefix-failure-exit.txt'
assert int(failed_import_exit.read_text(encoding='utf-8-sig').strip()) == 1
source_command = ['lake', 'env', 'lean', '-o', OBJECT.relative_to(ROOT).as_posix(), SOURCE.relative_to(ROOT).as_posix()]
audit_command = ['lake', 'env', 'lean', AUDIT.relative_to(ROOT).as_posix()]
receipt = {
    'verdict': 'PASS_ACTUAL_P9_D0_EQ4_ABSOLUTELY_SUMMABLE_EXACT_INFINITE_L',
    'date_utc': datetime.now(timezone.utc).isoformat(),
    'source': str(SOURCE), 'source_sha256': sha(SOURCE),
    'imports': re.findall(r'^import (.+)$', source_text, re.M),
    'source_compile': {'working_directory': str(ROOT), 'command': source_command,
        'outer_powershell_environment_setup': "$env:LEAN_PATH='D:/users/self_projects/prove2me_workspace;'+$env:LEAN_PATH",
        'exit_code': 0, 'status': 'observed',
        'observed_exit_file': str(EXIT), 'observed_exit_file_sha256': sha(EXIT),
        'log': str(LOG), 'log_sha256': sha(LOG), 'object': str(OBJECT),
        'object_sha256': sha(OBJECT), 'printed_targets': 12, 'only_standard_three_axioms': True,
        'observed_exec_session_id': 26384, 'observed_completion_chunk_id': '7dc93d'},
    'imported_statement_audit': {'working_directory': str(ROOT), 'command': audit_command,
        'outer_powershell_environment_setup': "$env:LEAN_PATH='D:/users/self_projects/prove2me_workspace;'+$env:LEAN_PATH",
        'exit_code': 0, 'status': 'observed', 'source': str(AUDIT), 'source_sha256': sha(AUDIT),
        'observed_exit_file': str(AUDIT_EXIT), 'observed_exit_file_sha256': sha(AUDIT_EXIT),
        'log': str(AUDIT_LOG), 'log_sha256': sha(AUDIT_LOG),
        'records': len(records), 'source_definitions': 3, 'source_theorems': 21,
        'additional_exact_statements': 7, 'actual_definition_values': 3,
        'all_source_declarations_covered': True, 'only_standard_three_axioms': True,
        'report': 'type-report.json', 'report_sha256': sha(OUT / 'type-report.json'),
        'observed_exec_session_id': 31873, 'observed_completion_chunk_id': 'ebc044'},
    'environment': environment,
    'current_toolchain_manifest_checked': {'lean_toolchain': 'leanprover/lean4:v4.33.1',
        'mathlib_manifest_revision': mathlib_revision},
    'unchanged_frozen_dependencies': parents,
    'actual_pure_definition_dependency': {'source': str(pure_definition),
        'source_sha256': sha(pure_definition), 'cached_object': str(pure_definition_object),
        'cached_object_sha256': sha(pure_definition_object),
        'status': 'existing official shared cache read only; not rebuilt by this batch'},
    'import_resolution': {
        'corrected_order': 'outer inherited ROOT prefix, then lake env lean prepends official root .lake/build/lib/lean before ROOT; Definitions uses official cache, missions uses ROOT',
        'preserved_initial_failure': {'exit_code': 1, 'status': 'observed import resolution failure, no mathematical proof claim',
            'cause': 'ROOT prepended inside lake env pwsh shadows cached Definitions with source-only root Definitions',
            'log': str(failed_import_log), 'log_sha256': sha(failed_import_log),
            'exit_file': str(failed_import_exit), 'exit_file_sha256': sha(failed_import_exit)},
        'api_probe': {'source': 'api-probe.lean', 'log': 'api-probe.log',
            'status': 'retained exploratory diagnostic with unknown guessed names; not proof evidence'}},
    'scope_note': {'path': str(NOTE), 'sha256': sha(NOTE)},
    'mathematical_checks': {
        'unconditional_actual_finite_odd_identity_from_true_reflection_and_strong_degree': True,
        'actual_harmonic_power_real_cast_and_positive_indexing': True,
        'zeta_identity_proved_from_official_mathlib_zeta_nat_tsum_theorem': True,
        'actual_harmonic_powers_gt_one_converge_to_zetaReal': True,
        'all_fixed_finite_shifted_tails_zero_for_s_ge_one_including_simple_poles': True,
        'actual_finiteL_tendsto_exactL_under_even_and_strong_degree': True,
        'actual_positive_points_regular_for_all_poles': True,
        'actual_simple_poles_cancel_using_proved_rho_one_zero': True,
        'simple_pole_difference_bounded_by_j_over_positive_t_squared': True,
        'shifted_higher_actual_poles_summable_from_real_p_series': True,
        'actual_series_summable_before_using_partial_sum_limit': True,
        'actual_series_norm_summable_absolute_convergence': True,
        'actual_HasSum_and_tsum_exactL': True,
        'original_even_n_ge_two_integer_quartic_Eq4_tsum_checked_explicitly': True,
        'n_zero_constant_multiplier_actual_HasSum': True,
        'n_zero_X_four_proper_but_not_strong_actual_rho_one_is_one': True,
        'n_zero_X_four_actual_positive_series_is_reciprocal_t_plus_one': True,
        'new_rho_cancellation_zeta_identity_or_summability_assumptions': []},
    'strong_degree_domain': '2*n + 2*W.natDegree <= 9*(n+1)-2',
    'actual_absolute_summability_domain': 'all n and rational W satisfying strong degree bound; even n is unnecessary for Summable/norm Summable',
    'actual_exact_odd_zeta_infinite_L_domain': 'even n and rational W satisfying strong degree bound; includes original even n>=2 integer quartic W via proved wrapper',
    'actual_p9_q1_m_equals_n_d0_Eq4_specialization_closed': True,
    'general_p_or_multilayer_or_positive_d_Eq4_closed': False,
    'rho_one_zero_from_strict_proper_alone': False,
    'original_five_dimensional_aggregated_F_injectivity_closed': False,
    'prescribed_integer_output_inverse_image_and_target_exact_L_closed': False,
    'remaining_Z9_F_obligations': [
        'General p, multilayer or d>0 summation/convergence beyond the current actual p9 q1 m=n d0 specialization.',
        'Denominator integrality and original five-dimensional aggregated coefficient-map invertibility.',
        'Exact prescribed integer-output inverse image and its prescribed target L.'],
    'full_Z9_F_closed': False, 'irrationality_closed': False,
    'root_shared_scope_API_credentials_writes': False}
(OUT / 'compile-receipt.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
files = [SOURCE, OBJECT, LOG, EXIT, AUDIT, AUDIT_LOG, AUDIT_EXIT, OUT / 'type-report.json',
    OUT / 'compile-receipt.json', Path(__file__).resolve(), OUT / 'prepare_summation_audit.py', NOTE,
    failed_import_log, failed_import_exit, OUT / 'api-probe.lean', OUT / 'api-probe.log', *parent_files]
external_files = [pure_definition, pure_definition_object]
(OUT / 'SHA256SUMS.txt').write_text('\n'.join(sha(p) + '  ' + p.relative_to(TASK).as_posix() for p in files) +
    '\n' + '\n'.join(sha(p) + '  ' + p.relative_to(TASK, walk_up=True).as_posix() for p in external_files) + '\n', encoding='utf-8')
for line in (OUT / 'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
    digest, rel = line.split('  ', 1)
    assert sha(TASK / rel) == digest
print(json.dumps({'verdict': receipt['verdict'], 'source_sha256': sha(SOURCE),
    'receipt_sha256': sha(OUT / 'compile-receipt.json'), 'manifest_sha256': sha(OUT / 'SHA256SUMS.txt'),
    'records': len(records), 'frozen_files': len(files) + len(external_files), 'full_Z9_F_closed': False}))
