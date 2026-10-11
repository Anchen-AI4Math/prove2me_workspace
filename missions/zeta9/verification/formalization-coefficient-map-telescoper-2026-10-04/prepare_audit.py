from pathlib import Path
import re
out = Path(__file__).resolve().parent
task = out.parents[1]
names = re.findall(r'^(?:def|theorem) (\w+)', (task / 'formalization/CoefficientMapTelescoper.lean').read_text(encoding='utf-8-sig'), re.M)
assert len(names) == 31
checks = ['checked_original_quartic_telescoper_chain', 'checked_node_pole_separation',
    'checked_actual_quotient_and_rational_function', 'checked_actual_finite_boundary']
text = '''import missions.zeta9.formalization.CoefficientMapTelescoper
import Lean
open Lean Meta Polynomial Finset
open scoped BigOperators
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapReflection
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapTelescoper
set_option pp.fullNames true
set_option pp.universes false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem checked_original_quartic_telescoper_chain (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : aggregate n W = 0) :
    (∀ t : ℚ, (∀ k ≤ n, t + (k : ℚ) ≠ 0) →
      ZetaNine.CoefficientMap.weightedR n W t = telescoper n W t - telescoper n W (t + 1)) ∧
    telescoper n W 1 = 0 ∧
    (∀ t : ℚ, telescoper n W (1 - (n : ℚ) - t) = telescoper n W t) ∧
    (∀ k, 1 ≤ k → k ≤ n + 1 → telescoper n W (k : ℚ) = 0) ∧
    (∀ k ≤ n, telescoper n W (-(n : ℚ) - (k : ℚ)) = 0) ∧
    rootPolynomial n ∣ telescoperNumerator n W := by
  have hs := quartic_is_strong_proper n (by omega) W hW
  exact ⟨fun t ht => actual_weightedR_is_difference n hn W hs hzero t ht,
    telescoper_at_one_zero n hn W hs hzero,
    fun t => telescoper_reflection n (by omega) hn W hs hzero t,
    fun k hk1 hkn => telescoper_positive_zeros n k hn W hs hzero hk1 hkn,
    fun k hk => telescoper_negative_zeros n k (by omega) hn W hs hzero hk,
    all_kernel_nodes_divide_telescoperNumerator n (by omega) hn W hs hzero⟩

theorem checked_node_pole_separation (n : ℕ) (hn1 : 1 ≤ n)
    (i : Fin (n + 1) ⊕ Fin (n + 1)) (k : ℕ) (hk : k < n) : rootNode n i + (k : ℚ) ≠ 0 := by
  cases i with
  | inl l => simp only [rootNode]; exact ne_of_gt (by positivity)
  | inr l =>
    simp only [rootNode]
    have hkn : (k : ℚ) < (n : ℚ) := by exact_mod_cast hk
    have hl : (0 : ℚ) ≤ (l.val : ℚ) := Nat.cast_nonneg _
    exact ne_of_lt (by linarith)

theorem checked_actual_quotient_and_rational_function (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hs : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    ∃ H : ℚ[X], H.natDegree ≤ 7 * n - 3 ∧
      telescoperNumerator n W = rootPolynomial n * H ∧
      ∀ t : ℚ, (∀ k < n, t + (k : ℚ) ≠ 0) →
        telescoper n W t = (rootPolynomial n).eval t * H.eval t / (polePolynomial (n - 1)).eval t ^ 9 := by
  obtain ⟨H, hH, hd⟩ := actual_polynomial_quotient_degree_bound n hn1 hn W hs hzero
  refine ⟨H, hd, hH, ?_⟩
  intro t ht
  rw [telescoper_actual_rational_representation n hn1 W t ht, hH, Polynomial.eval_mul]

theorem checked_actual_finite_boundary (n T : ℕ) (hn : Even n) (W : ℚ[X])
    (hs : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    (∑ t ∈ Icc 1 T, ZetaNine.CoefficientMap.weightedR n W (t : ℚ)) =
      telescoper n W 1 - telescoper n W ((T + 1 : ℕ) : ℚ) :=
  finite_sum_is_telescoper_boundary n T hn W hs hzero

run_meta do
  let emit (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let value ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString)),
      ("definitionValue", value)]).compress
  for name in [
'''
text += ',\n'.join('    `ZetaNine.CoefficientMapTelescoper.' + n for n in names)
text += ',\n' + ',\n'.join('    `' + n for n in checks) + '] do emit name\n'
(out / 'type-audit.lean').write_text(text, encoding='utf-8')
