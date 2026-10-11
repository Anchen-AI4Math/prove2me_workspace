"""Explicit Fin5 normalization repair; preserve and exclude failed original control."""
from run_step import *

verify()
receipt = load(OUT / 'review-compile-receipt.json')
failed = [r for r in receipt['rows'] if r['exit_code'] != 0]
assert len(failed) == 1 and failed[0]['logical_step'] == 'eight own actual output inverse pure-zeta and genuine HasSum controls'
assert len(receipt['rows']) == 82
for row in receipt['rows']:
    assert sha(ROOT / row['source_root_relative']) == row['source_sha256']
    for key in ['log', 'exit_file', 'wrapper', 'stdout_copy']:
        if row.get(key):
            assert sha(OUT / row[key]) == row[key + '_sha256']
    if row['output_sha256']:
        assert sha(TASK / row['output_task_relative']) == row['output_sha256']
original = (OUT / 'ob.lean').read_text(encoding='utf-8-sig')
old = '  norm_num [prescribedL, pureNine]\n'
assert original.count(old) == 1
new = '''  have h0 : pureNine (0 : Fin 5) = 0 := by decide
  have h1 : pureNine (1 : Fin 5) = 0 := by decide
  have h2 : pureNine (2 : Fin 5) = 0 := by decide
  have h3 : pureNine (3 : Fin 5) = 0 := by decide
  have h4 : pureNine (4 : Fin 5) = 1 := by decide
  simp [prescribedL, h0, h1, h2, h3, h4]
'''
source = OUT / 'ob2.lean'
write(source, original.replace(old, new, 1))
run('eight own actual output inverse pure-zeta and genuine HasSum controls repaired Fin values', source, P)
row = load(OUT / 'review-compile-receipt.json')['rows'][-1]
actual = rows(OUT / row['log'])
assert len(actual) == 8 and all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for r in actual)
dump(OUT / 'own-boundary-repair.json', {'status': 'ACTUAL_REPAIRED_PASS',
    'retained_actual_failed_execution': failed[0], 'failed_source_unchanged': True,
    'failed_sorryAx_records_excluded_from_proof_evidence': True,
    'actual_repaired_execution': row, 'actual_repaired_closed_boundary_records': actual,
    'proof_change': 'Five explicit decidable Fin5 target-coordinate values discharge casts/sums; target statements unchanged',
    'original_native_and_staged_proof_sources_unchanged': True})
mechanical = load(OUT / 'mechanical-checks.json')
changes = load(BATCH / 'stage-boundary-report.json')
dump(OUT / 'replay-summary.json', {'complete': True,
    'original_required_proofs': mechanical['core_proof_names'] + mechanical['actual_cross_helpers'],
    'staged_complete_proof_records_expected': 507, 'Definition_contexts': 8,
    'Def_fullExpr_records_expected': 520, 'Def_seven_staged_vs_native_comparisons_expected': 455,
    'native_staged_controls_actual_records': 93, 'own_boundary_source_proofs': 8,
    'failed_original_own_control_retained_excluded': True, 'actual_explicit_repair_succeeded': True,
    'raw_Expr_PP_kernel_alias_and_canonical_propagation_reported_separately': True})
receipt = load(OUT / 'review-compile-receipt.json')
receipt['complete'] = True
dump(OUT / 'review-compile-receipt.json', receipt)
print('Eight own repaired controls actual0 and standard3; failed ob.lean/r82 records unchanged and excluded.', flush=True)
