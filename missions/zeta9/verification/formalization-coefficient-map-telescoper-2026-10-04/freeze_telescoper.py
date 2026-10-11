"""Freeze the observed actual telescoper and quotient-degree bridge."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys
sys.stdout.reconfigure(encoding='utf-8')
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[1]
ROOT = TASK.parents[1]
SOURCE = TASK / 'formalization/CoefficientMapTelescoper.lean'
OBJECT = SOURCE.with_suffix('.olean')
LOG = SOURCE.with_suffix('.compile.log')
EXIT = SOURCE.with_suffix('.compile-exit.txt')
AUDIT = OUT / 'type-audit.lean'
AUDIT_LOG = OUT / 'type-audit.log'
AUDIT_EXIT = OUT / 'type-audit-exit.txt'
NOTE = TASK / 'research/coefficient-map-telescoper-2026-10-04.md'
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
assert len(printed) == 15
assert all({a.strip() for a in axs.split(',')} <= STANDARD for _, axs in printed)
assert OBJECT.stat().st_mtime >= SOURCE.stat().st_mtime
records = [json.loads(line) for line in audit_log.splitlines() if line.startswith('{')]
decls = re.findall(r'^(?:def|theorem) (\w+)', source_text, re.M)
checks = {'checked_original_quartic_telescoper_chain', 'checked_node_pole_separation',
    'checked_actual_quotient_and_rational_function', 'checked_actual_finite_boundary'}
assert len(decls) == 31 and len(records) == 35
assert {r['declaration'] for r in records} == {'ZetaNine.CoefficientMapTelescoper.' + n for n in decls} | checks
assert all(set(r['axioms']) <= STANDARD for r in records)
assert sum(r['definitionValue'] is not None for r in records) == 6
(OUT / 'type-report.json').write_text(json.dumps(records, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
aggregate_receipt = TASK / 'verification/formalization-coefficient-map-aggregate-2026-10-04/compile-receipt.json'
aggregate = json.loads(aggregate_receipt.read_text(encoding='utf-8'))
parents = aggregate['unchanged_frozen_dependencies'].copy()
parents.append({'source': aggregate['source'], 'source_sha256': aggregate['source_sha256'],
    'object': aggregate['source_compile']['object'], 'object_sha256': aggregate['source_compile']['object_sha256'],
    'receipt': str(aggregate_receipt), 'receipt_sha256': sha(aggregate_receipt)})
parent_files = []
for item in parents:
    for name in ['source', 'object', 'receipt']:
        path = Path(item[name]); assert sha(path) == item[name + '_sha256']; parent_files.append(path)
definition = aggregate['actual_pure_definition_dependency']
assert sha(Path(definition['source'])) == definition['source_sha256']
assert sha(Path(definition['cached_object'])) == definition['cached_object_sha256']
manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
assert next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib') == aggregate['environment']['mathlib_manifest_revision']
assert (ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip() == aggregate['environment']['lean_toolchain']
receipt = {
    'verdict': 'PASS_ACTUAL_CUMULATIVE_TELESCOPER_REFLECTION_AND_PZERO_DIVISIBILITY_BRIDGE',
    'date_utc': datetime.now(timezone.utc).isoformat(),
    'source': str(SOURCE), 'source_sha256': sha(SOURCE), 'imports': re.findall(r'^import (.+)$', source_text, re.M),
    'source_compile': {'status': 'observed', 'exit_code': 0, 'working_directory': str(ROOT),
        'command': ['lake', 'env', 'lean', '-o', OBJECT.relative_to(ROOT).as_posix(), SOURCE.relative_to(ROOT).as_posix()],
        'outer_powershell_environment_setup': "$env:LEAN_PATH='D:/users/self_projects/prove2me_workspace;'+$env:LEAN_PATH",
        'observed_exec_session_id': 57659, 'observed_completion_chunk_id': 'e85974',
        'observed_exit_file': str(EXIT), 'observed_exit_file_sha256': sha(EXIT),
        'log': str(LOG), 'log_sha256': sha(LOG), 'object': str(OBJECT), 'object_sha256': sha(OBJECT),
        'printed_targets': 15, 'only_standard_three_axioms': True},
    'imported_statement_audit': {'status': 'observed', 'exit_code': 0, 'working_directory': str(ROOT),
        'command': ['lake', 'env', 'lean', AUDIT.relative_to(ROOT).as_posix()],
        'outer_powershell_environment_setup': "$env:LEAN_PATH='D:/users/self_projects/prove2me_workspace;'+$env:LEAN_PATH",
        'observed_exec_session_id': 9526, 'observed_completion_chunk_id': 'f7ebd7',
        'source': str(AUDIT), 'source_sha256': sha(AUDIT), 'log': str(AUDIT_LOG), 'log_sha256': sha(AUDIT_LOG),
        'observed_exit_file': str(AUDIT_EXIT), 'observed_exit_file_sha256': sha(AUDIT_EXIT),
        'records': 35, 'source_definitions': 6, 'source_theorems': 25, 'additional_exact_statements': 4,
        'actual_definition_values': 6, 'all_source_declarations_covered': True,
        'only_standard_three_axioms': True, 'report': 'type-report.json', 'report_sha256': sha(OUT / 'type-report.json')},
    'environment': aggregate['environment'], 'unchanged_frozen_dependencies': parents,
    'actual_pure_definition_dependency': definition, 'scope_note': {'path': str(NOTE), 'sha256': sha(NOTE)},
    'mathematical_checks': {
        'actual_cumulative_coefficient_from_genuine_local_coefficients': True,
        'all_nine_rho_zero_derived_from_actual_five_vector_zero_and_proved_even_strong_domain': True,
        'genuine_weightedR_equals_actual_Q_difference_at_regular_points': True,
        'finite_sum_equals_actual_Q_one_minus_actual_Q_T_plus_one': True,
        'actual_Q_T_plus_one_tends_zero': True,
        'actual_Q_one_zero_from_actual_finiteL_limit': True,
        'actual_R_positive_numerator_zeros_one_through_n': True,
        'actual_Q_positive_zeros_one_through_n_plus_one': True,
        'actual_cumulative_coefficient_reflection_without_periodic_rational_classification': True,
        'actual_Q_reflection_one_minus_n_minus_t': True,
        'actual_Q_negative_zeros_minus_n_through_minus_two_n': True,
        'genuine_polynomial_numerator_representation_with_proved_nonzero_regular_denominator': True,
        'actual_numerator_degree_at_most_nine_n_minus_one': True,
        'two_n_plus_two_actual_root_nodes_injective_and_disjoint_from_poles': True,
        'actual_Pzero_equals_explicit_positive_and_negative_linear_factor_products': True,
        'actual_Pzero_monic_degree_two_n_plus_two': True,
        'actual_nodes_zero_imply_entire_Pzero_divides_actual_numerator': True,
        'actual_polynomial_quotient_exists_with_degree_at_most_seven_n_minus_three': True,
        'new_telescoper_or_kernel_triviality_assumptions': []},
    'domain': 'n>=1, Even n, StrongProperMultiplier n W and actual aggregate n W=0; checked original even n>=2 quartic specialization derives Strong',
    'exploratory_api_probe': {'source': 'api-probe.lean', 'log': 'api-probe.log',
        'observed_exec_session_id': 19045, 'observed_completion_chunk_id': '9da9b8', 'exit_code': 1,
        'status': 'diagnostic unknown guessed coefficient lemma name; not proof evidence'},
    'quartic_F_injectivity_closed_by_this_file': False,
    'remaining_in_this_increment': ['Actual Q0=R*A and shift identity link the actual quotient to A*H-B*H(X+1).',
        'Highest-coefficient degree obstruction then closes the original quartic aggregate kernel.'],
    'full_Z9_F_closed': False, 'irrationality_closed': False, 'root_shared_scope_API_credentials_writes': False}
(OUT / 'compile-receipt.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
files = [SOURCE, OBJECT, LOG, EXIT, AUDIT, AUDIT_LOG, AUDIT_EXIT, OUT / 'type-report.json',
    OUT / 'compile-receipt.json', Path(__file__).resolve(), OUT / 'prepare_audit.py', NOTE,
    OUT / 'api-probe.lean', OUT / 'api-probe.log', *parent_files,
    Path(definition['source']), Path(definition['cached_object'])]
(OUT / 'SHA256SUMS.txt').write_text('\n'.join(sha(p) + '  ' + p.relative_to(TASK, walk_up=True).as_posix() for p in files) + '\n', encoding='utf-8')
for line in (OUT / 'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines():
    digest, rel = line.split('  ', 1); assert sha(TASK / rel) == digest
print(json.dumps({'verdict': receipt['verdict'], 'source_sha256': sha(SOURCE),
    'receipt_sha256': sha(OUT / 'compile-receipt.json'), 'manifest_sha256': sha(OUT / 'SHA256SUMS.txt'),
    'records': 35, 'frozen_files': len(files)}))
