"""Fresh staged proof/full-value replay after exact own mechanical reconstruction."""
from run_step import *

verify()
mechanical = load(OUT / 'mechanical-checks.json')
assert mechanical['complete'] and all(r['pass'] for r in mechanical['checks'])
plan = load(BATCH / 'root-copy-plan.json')
for row in plan['files']:
    relative = row['root_relative_destination']
    source = PROJECT / relative
    assert sha(source) == row['sha256'] and source.stat().st_size == row['bytes']
    run('staged ' + relative, source, P, P / (relative.removesuffix('.lean') + '.olean'))
for name in ['types_original.lean', 'types_definition.lean'] + [f'types_{i}_{kind}.lean'
        for i in range(3) for kind in ['solution', 'reference']] + [f'helpers_{i}.lean' for i in range(3)]:
    source = OUT / name
    write(source, (BATCH / name).read_bytes())
    run('fresh exact author program ' + name, source, N if name == 'types_original.lean' else P)

# Copy source-only aliases from fixed author inputs. Mechanical reconstruction
# has independently established their actual complete Definition source.
for context, cache in [('native', N), ('staged', P)]:
    module = 'NativeKernelValueComparisonDefinition' if context == 'native' else 'StagedKernelValueComparisonDefinition'
    run(context + ' Kernel actual closed source alias', PROJECT / (module + '.lean'), cache,
        cache / (module + '.olean'))
    run(context + ' Kernel seven whole-value kernel and seven rfl equalities',
        OUT / ('kernel-' + context + '-values.lean'), cache)

contexts = ['missions.zeta9.formalization.CoefficientMapKernelBridge']
contexts += [r['root_relative_destination'].removesuffix('.lean').replace('/', '.') for r in plan['files']]
assert len(contexts) == 8
helper = (OUT / 'full-kernel-audit.helper.lean').read_text(encoding='utf-8-sig')
for i, module in enumerate(contexts):
    code = 'import ' + module + '\n' + helper
    code += '\nrun_meta do\n  for name in [' + ', '.join('`' + name for name in mechanical['actual_defs']) + '] do\n    emitIndependentDefinition name\n'
    source = OUT / (f'fv{i}.lean')
    write(source, code)
    run('independent complete raw Definition Expr context ' + str(i), source, N if i == 0 else P)

proof_names = mechanical['core_proof_names'] + mechanical['actual_cross_helpers']
assert len(proof_names) == 168
code = 'import missions.zeta9.formalization.CoefficientMapKernelBridge\n' + helper
code += '\nrun_meta do\n  for name in [' + ', '.join('`' + name for name in proof_names) + '] do\n    emitIndependentProof name\n'
source = OUT / 'np.lean'
write(source, code)
run('independent168 original required proof full types and axioms', source, N)

target_plan = load(BATCH / 'target-plan.json')
for i, target in enumerate(target_plan['targets']):
    module = target['local_solution'].removesuffix('.lean').replace('/', '.')
    selected_name = target['theorem_name']
    actual_names = [selected_name.rsplit('.', 1)[0] + '.checked_' + selected_name.rsplit('.', 1)[1]
                    if name == selected_name else name for name in proof_names] + ['solution']
    code = 'import ' + module + '\n' + helper
    code += '\nrun_meta do\n  for name in [' + ', '.join('`' + name for name in actual_names) + '] do\n    emitIndependentProof name\n'
    source = OUT / (f'pc{i}.lean')
    write(source, code)
    run('independent169 complete staged proof full types and axioms context ' + str(i), source, P)

selected = 'inverseMultiplier_actual_HasSum_and_absolute'
changes = []
for i, source_name in enumerate(['native-control-author.lean', 'native-control-independent.lean']):
    original = OUT / source_name
    code = original.read_text(encoding='utf-8-sig')
    old_import = 'import missions.zeta9.formalization.CoefficientMapKernelBridge'
    assert code.count(old_import) == 1
    code = code.replace(selected, 'checked_' + selected)
    code = code.replace(old_import, 'import Solutions.Sol_ZetaNine_CoefficientMapKernelBridge_' + selected)
    source = OUT / (f'bc{i}.lean')
    write(source, code)
    expected = BATCH / ('stage-native-author-audit.lean' if i == 0 else 'stage-independent-boundary-audit.lean')
    assert source.read_bytes() == expected.read_bytes()
    run('fresh staged original native control ' + str(i), source, P)
    changes.append({'original_source': source_name, 'original_sha256': sha(original), 'staged_sha256': sha(source),
        'changes': ['native import to genuine complete Solution', 'selected endpoint and quoted diagnostic name only'],
        'proof_bodies_modified': False, 'expected_records': 37 if i == 0 else 56})

source = OUT / 'ob.lean'
write(source, '''import Solutions.Sol_ZetaNine_CoefficientMapKernelBridge_inverseMultiplier_actual_HasSum_and_absolute
import Lean
open Polynomial Finset
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapFiniteSum
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapSummation
namespace KernelIndependentOwn

def pureNine : Fin 5 → ℚ := fun i => if i = 4 then 1 else 0

theorem outputOrderB (n : ℕ) (W : ℚ[X]) : aggregate n W 0 = constantTerm n W := rfl

theorem outputOrderNine (n : ℕ) (W : ℚ[X]) : aggregate n W 4 = rho n 9 W := rfl

theorem zeroInverse (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) : inverseMultiplier n hn2 hn 0 = 0 := by
  exact (inverseMultiplier_unique n hn2 hn 0 0 (by simp) (aggregateLinearMap n).map_zero).symm

theorem rationalInverseQuartic (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    (inverseMultiplier n hn2 hn b).natDegree ≤ 4 := inverseMultiplier_natDegree_le n hn2 hn b

theorem pureNineNonzero : pureNine ≠ 0 := by
  intro h
  have v := congrFun h (4 : Fin 5)
  norm_num [pureNine] at v

theorem pureNineL : prescribedL pureNine = zetaReal 9 := by
  norm_num [prescribedL, pureNine]

theorem pureNineActualCoefficient (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    rho n 9 (inverseMultiplier n hn2 hn pureNine) = 1 := by
  have h := congrFun (inverseMultiplier_actual_aggregate n hn2 hn pureNine) (4 : Fin 5)
  simpa [aggregate, pureNine] using h

theorem pureNineRealHasSum (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    HasSum (fun k : ℕ => (ZetaNine.CoefficientMap.weightedR n (inverseMultiplier n hn2 hn pureNine)
      ((k + 1 : ℕ) : ℚ) : ℝ)) (zetaReal 9) := by
  have h := (checked_inverseMultiplier_actual_HasSum_and_absolute n hn2 hn pureNine).1
  simpa only [pureNineL] using h

end KernelIndependentOwn
set_option pp.fullNames true
run_meta do
  let env ← Lean.getEnv
  for (name, ci) in env.constants.toList do
    unless name.getPrefix == `KernelIndependentOwn do continue
    let .thmInfo _ := ci | continue
    let typ ← Lean.Meta.ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Lean.Json.mkObj [("declaration",Lean.Json.str name.toString),
      ("type",Lean.Json.str typ.pretty),("axioms",Lean.toJson (axs.toList.map Lean.Name.toString))]).compress
''')
run('eight own actual output inverse pure-zeta and genuine HasSum controls', source, P)
dump(OUT / 'replay-summary.json', {'complete': True, 'original_required_proofs': proof_names,
    'staged_complete_proof_records_expected': 507, 'Definition_contexts': contexts,
    'Def_fullExpr_records_expected': 520, 'Def_seven_staged_vs_native_comparisons_expected': 455,
    'native_control_changes': changes, 'own_boundary_source_proofs_expected': 8,
    'raw_Expr_PP_kernel_alias_and_canonical_propagation_must_be_reported_separately': True})
receipt = load(OUT / 'review-compile-receipt.json')
receipt['complete'] = True
dump(OUT / 'review-compile-receipt.json', receipt)
print('Actual independent replay complete; final PASS awaits parsed whole-value/proof and frozen Root evidence.', flush=True)
