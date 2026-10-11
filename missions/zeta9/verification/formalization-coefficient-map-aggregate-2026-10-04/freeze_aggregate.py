"""Bind observed compile/type evidence for the actual aggregate increment."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys
sys.stdout.reconfigure(encoding='utf-8')
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
SOURCE = TASK / 'formalization/CoefficientMapAggregate.lean'
OBJECT = SOURCE.with_suffix('.olean')
LOG = SOURCE.with_suffix('.compile.log')
EXIT = SOURCE.with_suffix('.compile-exit.txt')
AUDIT = OUT / 'type-audit.lean'
AUDIT_LOG = OUT / 'type-audit.log'
AUDIT_EXIT = OUT / 'type-audit-exit.txt'
NOTE = TASK / 'research/coefficient-map-aggregate-2026-10-04.md'
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
assert len(printed) == 6
assert all({a.strip() for a in axs.split(',')} <= STANDARD for _, axs in printed)
assert OBJECT.stat().st_mtime >= SOURCE.stat().st_mtime
records = [json.loads(line) for line in audit_log.splitlines() if line.startswith('{')]
decls = re.findall(r'^(?:def|theorem) (\w+)', source_text, re.M)
checks = {'checked_five_actual_coordinates', 'checked_actual_monomial_basis', 'checked_basis_columns',
    'checked_n_zero_X_four_aggregate_kernel', 'checked_original_quartic_zero_all_orders',
    'checked_original_quartic_zero_exact_sum'}
assert len(decls) == 26 and len(records) == 32
assert {r['declaration'] for r in records} == {'ZetaNine.CoefficientMapAggregate.' + n for n in decls} | checks
assert all(set(r['axioms']) <= STANDARD for r in records)
assert sum(r['definitionValue'] is not None for r in records) == 6
(OUT / 'type-report.json').write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
summation_receipt = TASK / 'verification/formalization-coefficient-map-summation-2026-10-04/compile-receipt.json'
summation = json.loads(summation_receipt.read_text(encoding='utf-8'))
parents = summation['unchanged_frozen_dependencies'].copy()
parents.append({'source': summation['source'], 'source_sha256': summation['source_sha256'],
    'object': summation['source_compile']['object'], 'object_sha256': summation['source_compile']['object_sha256'],
    'receipt': str(summation_receipt), 'receipt_sha256': sha(summation_receipt)})
parent_files = []
for item in parents:
    for name in ['source', 'object', 'receipt']:
        path = Path(item[name])
        assert sha(path) == item[name + '_sha256']
        parent_files.append(path)
definition = summation['actual_pure_definition_dependency']
assert sha(Path(definition['source'])) == definition['source_sha256']
assert sha(Path(definition['cached_object'])) == definition['cached_object_sha256']
manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
assert next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib') == summation['environment']['mathlib_manifest_revision']
assert (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip() == summation['environment']['lean_toolchain']
receipt = {
    'verdict': 'PASS_ACTUAL_FIVE_DIMENSIONAL_LINEAR_AGGREGATE_AND_QUARTIC_COORDINATE_RECOVERY_ONLY',
    'date_utc': datetime.now(timezone.utc).isoformat(),
    'source': str(SOURCE), 'source_sha256': sha(SOURCE),
    'imports': re.findall(r'^import (.+)$', source_text, re.M),
    'source_compile': {'status': 'observed', 'exit_code': 0, 'working_directory': str(ROOT),
        'command': ['lake', 'env', 'lean', '-o', OBJECT.relative_to(ROOT).as_posix(), SOURCE.relative_to(ROOT).as_posix()],
        'outer_powershell_environment_setup': "$env:LEAN_PATH='D:/users/self_projects/prove2me_workspace;'+$env:LEAN_PATH",
        'observed_exec_session_id': 56294, 'observed_completion_chunk_id': '9fbeed',
        'observed_exit_file': str(EXIT), 'observed_exit_file_sha256': sha(EXIT),
        'log': str(LOG), 'log_sha256': sha(LOG), 'object': str(OBJECT), 'object_sha256': sha(OBJECT),
        'printed_targets': 6, 'only_standard_three_axioms': True},
    'imported_statement_audit': {'status': 'observed', 'exit_code': 0, 'working_directory': str(ROOT),
        'command': ['lake', 'env', 'lean', AUDIT.relative_to(ROOT).as_posix()],
        'outer_powershell_environment_setup': "$env:LEAN_PATH='D:/users/self_projects/prove2me_workspace;'+$env:LEAN_PATH",
        'observed_exec_session_id': 48694, 'observed_completion_chunk_id': 'e7e0c4',
        'source': str(AUDIT), 'source_sha256': sha(AUDIT), 'log': str(AUDIT_LOG), 'log_sha256': sha(AUDIT_LOG),
        'observed_exit_file': str(AUDIT_EXIT), 'observed_exit_file_sha256': sha(AUDIT_EXIT),
        'records': 32, 'source_definitions': 6, 'source_theorems': 20, 'additional_exact_statements': 6,
        'actual_definition_values': 6, 'all_source_declarations_covered': True,
        'only_standard_three_axioms': True, 'report': 'type-report.json', 'report_sha256': sha(OUT / 'type-report.json')},
    'environment': summation['environment'], 'unchanged_frozen_dependencies': parents,
    'actual_pure_definition_dependency': definition,
    'scope_note': {'path': str(NOTE), 'sha256': sha(NOTE)},
    'mathematical_checks': {
        'actual_F_entries_B_rho_three_five_seven_nine': True,
        'actual_local_power_series_coefficients_additive_and_scalar_linear': True,
        'actual_finite_harmonic_B_and_rho_scalar_linear': True,
        'actual_F_as_rational_linear_map': True,
        'actual_Fin_five_to_quartic_polynomial_linear_map': True,
        'quartic_natural_degree_bound_and_all_five_coefficients_restore': True,
        'every_degree_at_most_four_polynomial_restored_from_its_coefficients': True,
        'standard_coordinate_basis_gives_actual_monomials': True,
        'quartic_F_basis_columns_are_actual_aggregate_monomial_outputs': True,
        'zero_aggregate_and_proved_strong_even_cancellation_force_all_nine_rho_zero': True,
        'zero_aggregate_has_actual_exact_infinite_L_zero_on_original_quartic_domain': True,
        'n_zero_X_four_nonzero_actual_aggregate_zero_and_rho_one_is_one': True,
        'n_zero_X_four_strict_proper_but_outside_strong_domain': True,
        'determinant_rank_injectivity_inverse_or_kernel_triviality_assumptions': []},
    'quartic_kernel_claim_domain': 'original even n>=2; kernel triviality remains open',
    'quartic_F_injectivity_closed': False, 'five_dimensional_F_inverse_closed': False,
    'remaining_Z9_F_obligations': ['Actual telescoper, its numerator roots/divisibility and highest-coefficient degree contradiction for the quartic kernel.',
        'Full five-dimensional aggregate invertibility and exact prescribed integer-output inverse image.',
        'Denominator integrality, prescribed target L and the required infinite low-height nonzero construction.'],
    'full_Z9_F_closed': False, 'irrationality_closed': False,
    'root_shared_scope_API_credentials_writes': False}
(OUT / 'compile-receipt.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
files = [SOURCE, OBJECT, LOG, EXIT, AUDIT, AUDIT_LOG, AUDIT_EXIT, OUT / 'type-report.json',
    OUT / 'compile-receipt.json', Path(__file__).resolve(), OUT / 'prepare_audit.py', NOTE, *parent_files,
    Path(definition['source']), Path(definition['cached_object'])]
(OUT / 'SHA256SUMS.txt').write_text('\n'.join(sha(p) + '  ' + p.relative_to(TASK, walk_up=True).as_posix() for p in files) + '\n', encoding='utf-8')
for line in (OUT / 'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
    digest, rel = line.split('  ', 1)
    assert sha(TASK / rel) == digest
print(json.dumps({'verdict': receipt['verdict'], 'source_sha256': sha(SOURCE),
    'receipt_sha256': sha(OUT / 'compile-receipt.json'), 'manifest_sha256': sha(OUT / 'SHA256SUMS.txt'),
    'records': 32, 'frozen_files': len(files), 'quartic_F_injectivity_closed': False}))
