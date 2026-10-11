"""Freeze observed genuine quartic aggregate kernel, inverse and exact L evidence."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys
sys.stdout.reconfigure(encoding='utf-8')
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
SOURCE = TASK / 'formalization/CoefficientMapKernelBridge.lean'
OBJECT = SOURCE.with_suffix('.olean')
LOG = SOURCE.with_suffix('.compile.log')
EXIT = SOURCE.with_suffix('.compile-exit.txt')
AUDIT = OUT / 'type-audit.lean'
AUDIT_LOG = OUT / 'type-audit.log'
AUDIT_EXIT = OUT / 'type-audit-exit.txt'
NOTE = TASK / 'research/coefficient-map-kernel-2026-10-04.md'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
for p in [EXIT, AUDIT_EXIT]: assert int(p.read_text(encoding='utf-8-sig').strip()) == 0
source_text = SOURCE.read_text(encoding='utf-8-sig')
source_log = LOG.read_text(encoding='utf-8-sig')
audit_log = AUDIT_LOG.read_text(encoding='utf-8-sig')
for log in [source_log, audit_log]:
    assert ': error:' not in log and ': warning:' not in log and 'sorryAx' not in log
assert not re.search(r'\b(sorry|admit)\b|^axiom\s', source_text, re.M)
printed = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", source_log, re.S)
assert len(printed) == 17
assert all({a.strip() for a in axs.split(',')} <= STANDARD for _, axs in printed)
assert OBJECT.stat().st_mtime >= SOURCE.stat().st_mtime
records = [json.loads(line) for line in audit_log.splitlines() if line.startswith('{')]
decls = re.findall(r'^(?:def|theorem) (\w+)', source_text, re.M)
checks = {'checked_actual_five_zero_coordinates_force_quartic_zero',
    'checked_nonzero_pure_zeta_nine_rational_lift', 'checked_unique_integer_output_rational_lift',
    'checked_original_integer_quartic_injectivity', 'checked_actual_R_shift_ratio_right',
    'checked_derived_inverse_both_laws', 'checked_explicit_prescribed_L_absolute_HasSum'}
assert len(decls) == 30 and len(records) == 37
assert {r['declaration'] for r in records} == {'ZetaNine.CoefficientMapKernelBridge.' + n for n in decls} | checks
assert all(set(r['axioms']) <= STANDARD for r in records)
assert sum(r['definitionValue'] is not None for r in records) == 7
(OUT / 'type-report.json').write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
telescoper_receipt = TASK / 'verification/formalization-coefficient-map-telescoper-2026-10-04/compile-receipt.json'
telescoper = json.loads(telescoper_receipt.read_text(encoding='utf-8'))
parents = telescoper['unchanged_frozen_dependencies'].copy()
parents.append({'source': telescoper['source'], 'source_sha256': telescoper['source_sha256'],
    'object': telescoper['source_compile']['object'], 'object_sha256': telescoper['source_compile']['object_sha256'],
    'receipt': str(telescoper_receipt), 'receipt_sha256': sha(telescoper_receipt)})
shift_receipt = TASK / 'verification/formalization-coefficient-map-shift-degree-2026-10-04/compile-receipt.json'
shift = json.loads(shift_receipt.read_text(encoding='utf-8'))
shift_source = ROOT / shift['source']
assert sha(shift_receipt) == '93595416db563dd9cd8ffb5030455eed1edfe678b392ec64b1bd4930fdb7f853'
parents.append({'source': str(shift_source), 'source_sha256': shift['source_sha256'],
    'object': str(shift_source.with_suffix('.olean')), 'object_sha256': shift['source_compile']['object_sha256'],
    'receipt': str(shift_receipt), 'receipt_sha256': sha(shift_receipt)})
parent_files = []
assert len(parents) == 10
for item in parents:
    for name in ['source', 'object', 'receipt']:
        path = Path(item[name]); assert sha(path) == item[name + '_sha256']; parent_files.append(path)
definition = telescoper['actual_pure_definition_dependency']
assert sha(Path(definition['source'])) == definition['source_sha256']
assert sha(Path(definition['cached_object'])) == definition['cached_object_sha256']
manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
mathlib_revision = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
assert mathlib_revision == telescoper['environment']['mathlib_manifest_revision'] == shift['environment']['mathlib_rev']
assert (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip() == telescoper['environment']['lean_toolchain']
shift_manifest = shift_receipt.parent / 'source-manifest.json'
shift_sums = shift_receipt.parent / 'SHA256SUMS.txt'
assert sha(shift_manifest) == '8918a99aed1d1ab8d75079feaac4996f70f0e96cf66cec2dff713a0454210044'
assert sha(shift_sums) == '88f22efde6ad2e4552c878e55ca09f5247f9ab4ffa567c7d5edc91036808f4c5'
receipt = {
    'verdict': 'PASS_ACTUAL_ORIGINAL_QUARTIC_F_KERNEL_ZERO_BIJECTION_AND_PRESCRIBED_RATIONAL_INFINITE_L',
    'date_utc': datetime.now(timezone.utc).isoformat(),
    'source': str(SOURCE), 'source_sha256': sha(SOURCE), 'imports': re.findall(r'^import (.+)$', source_text, re.M),
    'source_compile': {'status': 'observed', 'exit_code': 0, 'working_directory': str(ROOT),
        'command': ['lake', 'env', 'lean', '-o', OBJECT.relative_to(ROOT).as_posix(), SOURCE.relative_to(ROOT).as_posix()],
        'outer_powershell_environment_setup': "$env:LEAN_PATH='D:/users/self_projects/prove2me_workspace;'+$env:LEAN_PATH",
        'observed_exec_session_id': 21823, 'observed_completion_chunk_id': '7aac6e',
        'observed_exit_file': str(EXIT), 'observed_exit_file_sha256': sha(EXIT),
        'log': str(LOG), 'log_sha256': sha(LOG), 'object': str(OBJECT), 'object_sha256': sha(OBJECT),
        'printed_targets': 17, 'only_standard_three_axioms': True},
    'imported_statement_audit': {'status': 'observed', 'exit_code': 0, 'working_directory': str(ROOT),
        'command': ['lake', 'env', 'lean', AUDIT.relative_to(ROOT).as_posix()],
        'outer_powershell_environment_setup': "$env:LEAN_PATH='D:/users/self_projects/prove2me_workspace;'+$env:LEAN_PATH",
        'observed_exec_session_id': 14851, 'observed_completion_chunk_id': 'a1cd91',
        'source': str(AUDIT), 'source_sha256': sha(AUDIT), 'log': str(AUDIT_LOG), 'log_sha256': sha(AUDIT_LOG),
        'observed_exit_file': str(AUDIT_EXIT), 'observed_exit_file_sha256': sha(AUDIT_EXIT),
        'records': 37, 'source_definitions': 7, 'source_theorems': 23, 'additional_exact_statements': 7,
        'actual_definition_values': 7, 'all_source_declarations_covered': True,
        'only_standard_three_axioms': True, 'report': 'type-report.json', 'report_sha256': sha(OUT / 'type-report.json')},
    'environment': telescoper['environment'], 'unchanged_frozen_dependencies': parents,
    'actual_pure_definition_dependency': definition,
    'independently_authored_shift_degree_binding': {'source': str(shift_source), 'source_sha256': sha(shift_source),
        'receipt': str(shift_receipt), 'receipt_sha256': sha(shift_receipt),
        'source_manifest': str(shift_manifest), 'source_manifest_sha256': sha(shift_manifest),
        'SHA256SUMS': str(shift_sums), 'SHA256SUMS_sha256': sha(shift_sums)},
    'scope_note': {'path': str(NOTE), 'sha256': sha(NOTE)},
    'mathematical_checks': {
        'actual_finite_numerator_and_pole_product_shift_identities': True,
        'genuine_R_t_plus_one_A_t_plus_one_equals_R_t_B_t_at_proved_regular_points': True,
        'actual_R_shift_ratio_checked_on_safe_t_above_n_plus_one_domain': True,
        'actual_n_factorial_seventh_Pzero_numerator_factor_identity': True,
        'actual_R_A_equals_n_factorial_seventh_Pzero_over_actual_M_ninth': True,
        'actual_telescoper_quotient_Q_equals_R_A_H_over_n_factorial_seventh': True,
        'actual_R_nonzero_on_infinite_right_regular_domain': True,
        'actual_quotient_and_difference_produce_true_polynomial_relation_not_input_assumption': True,
        'actual_kernel_main_theorem_derives_H_existence_and_degree_from_genuine_aggregate_zero': True,
        'quartic_degree_at_most_eight_conflicts_with_proved_shift_coefficient_unless_H_zero': True,
        'n_factorial_seventh_nonzero_and_true_quadratic_composition_cancel_to_W_zero': True,
        'original_even_n_ge_two_quartic_actual_aggregate_kernel_zero': True,
        'original_actual_quartic_W_V_aggregate_injectivity': True,
        'actual_five_dimensional_rational_linear_endomorphism_bijective_from_proved_injectivity': True,
        'actual_linear_equivalence_defined_only_after_proved_bijection': True,
        'every_exact_rational_five_output_has_unique_actual_quartic_preimage': True,
        'explicit_inverseMultiplier_actual_F_output_and_unique_preimage': True,
        'nonzero_output_forces_actual_inverse_polynomial_nonzero': True,
        'actual_inverseMultiplier_has_exact_prescribed_L_and_absolutely_summable_HasSum': True,
        'explicit_integer_five_output_has_unique_rational_quartic_preimage_checked': True,
        'nonzero_pure_zeta_nine_rational_quartic_preimage_and_actual_HasSum_checked': True,
        'new_determinant_inverse_kernel_triviality_or_polynomial_relation_assumptions': []},
    'domain': 'p=9, q=1, m=n, d=0; original even n>=2; W rational with natDegree<=4; target b in rational Fin5 space',
    'original_quartic_actual_five_dimensional_F_injectivity_closed': True,
    'original_quartic_actual_five_dimensional_F_rational_inverse_closed': True,
    'prescribed_rational_output_actual_exact_infinite_L_closed': True,
    'arbitrary_integer_output_guaranteed_integer_coefficient_W': False,
    'retained_boundary': {'n_zero_X_four': 'Aggregate frozen audit proves actual F=0, W!=0 and rho1=1; all current kernel/inverse endpoints require even n>=2',
        'n_one_resonance': 'ShiftDegree frozen audit preserves the out-of-domain X^5 resonance'},
    'remaining_Z9_F_obligations': [
        'Local coefficient and harmonic denominator integrality and quantitative arithmetic costs.',
        'Uniform inverse-image height bounds and an infinite low-height nonzero sequence after low-zeta elimination.',
        'Higher-degree full-kernel classification/fixed-degree reduction and parameter families beyond current p9 q1 m=n d0 quartic domain.'],
    'full_Z9_F_closed': False, 'irrationality_closed': False, 'root_shared_scope_API_credentials_writes': False}
(OUT / 'compile-receipt.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
files = [SOURCE, OBJECT, LOG, EXIT, AUDIT, AUDIT_LOG, AUDIT_EXIT, OUT / 'type-report.json',
    OUT / 'compile-receipt.json', Path(__file__).resolve(), OUT / 'prepare_audit.py', NOTE, *parent_files,
    Path(definition['source']), Path(definition['cached_object']), shift_manifest, shift_sums]
(OUT / 'SHA256SUMS.txt').write_text('\n'.join(sha(p) + '  ' + p.relative_to(TASK, walk_up=True).as_posix() for p in files) + '\n', encoding='utf-8')
for line in (OUT / 'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
    digest, rel = line.split('  ', 1); assert sha(TASK / rel) == digest
print(json.dumps({'verdict': receipt['verdict'], 'source_sha256': sha(SOURCE),
    'receipt_sha256': sha(OUT / 'compile-receipt.json'), 'manifest_sha256': sha(OUT / 'SHA256SUMS.txt'),
    'records': 37, 'frozen_files': len(files)}))
