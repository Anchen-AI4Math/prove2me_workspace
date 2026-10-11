import Solutions.Sol_ZetaNine_CoefficientMapTelescoper_actual_polynomial_quotient_degree_bound
import Lean
open Lean Meta Polynomial Finset Filter
open scoped BigOperators Topology
open ZetaNine.CoefficientMapTelescoper ZetaNine.CoefficientMapAggregate
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapInjectivity
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option pp.fullNames true
set_option linter.unusedVariables false
noncomputable section

namespace IndependentTelescoper

theorem cumulative_concrete_sign :
    (∑ j ∈ range 2, prefixSum (fun _ => (1 : ℚ)) j * ((j : ℚ) - ((j + 1 : ℕ) : ℚ))) = -3 := by
  norm_num [prefixSum, Finset.sum_range_succ]

theorem cumulative_raw_identity (n : ℕ) (c f : ℕ → ℚ) :
    (∑ j ∈ range n, (∑ i ∈ range (j + 1), c i) * (f j - f (j + 1))) =
      (∑ j ∈ range (n + 1), c j * f j) - (∑ i ∈ range (n + 1), c i) * f n :=
  finite_cumulative_difference n c f

theorem actual_telescoper_definition (n : ℕ) (W : ℚ[X]) (t : ℚ) :
    telescoper n W t = ∑ j ∈ range n, ∑ s ∈ Icc 1 9,
      (∑ i ∈ range (j + 1), weightedLocalCoefficient n i s W) / (t + (j : ℚ)) ^ s := rfl

theorem zero_multiplier_telescoper (n : ℕ) (t : ℚ) : telescoper n 0 t = 0 := by
  simp [telescoper, cumulativeCoefficient, prefixSum, weightedLocalCoefficient, weightedClearedSeries]

theorem zero_n_telescoper (W : ℚ[X]) (t : ℚ) : telescoper 0 W t = 0 := by
  simp [telescoper]

theorem zero_n_harmonic_value : ZetaNine.CoefficientMap.weightedR 0 (X ^ 4) 1 = 1 := by
  norm_num [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]

theorem zero_n_harmonic_difference_false :
    ZetaNine.CoefficientMap.weightedR 0 (X ^ 4) 1 ≠ telescoper 0 (X ^ 4) 1 - telescoper 0 (X ^ 4) 2 := by
  rw [zero_n_harmonic_value, zero_n_telescoper, zero_n_telescoper]
  norm_num

theorem zero_n_harmonic_not_strong :
    ProperMultiplier 0 (X ^ 4 : ℚ[X]) ∧ ¬StrongProperMultiplier 0 (X ^ 4 : ℚ[X]) := by
  norm_num [ProperMultiplier, StrongProperMultiplier]

theorem zero_n_harmonic_aggregate_zero : aggregate 0 (X ^ 4 : ℚ[X]) = 0 := by
  funext i
  fin_cases i <;> norm_num [aggregate, ZetaNine.CoefficientMapFiniteSum.constantTerm,
    ZetaNine.CoefficientMapFiniteSum.rho, ZetaNine.HarmonicStability.harmonicPower,
    weightedLocalCoefficient, weightedClearedSeries, clearedSeries, shiftedNumerator,
    shiftedClearedDenominator, localU, shiftedVariable,
    Polynomial.pow_comp, Polynomial.X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_X, ← pow_two, ← pow_mul]

theorem original_quartic_real_finite_boundary (n T : ℕ) (hn : Even n) (hn2 : 2 ≤ n)
    (W : ℚ[X]) (hd : W.natDegree ≤ 4) (hz : aggregate n W = 0) :
    (∑ t ∈ Icc 1 T, ZetaNine.CoefficientMap.weightedR n W (t : ℚ)) =
      telescoper n W 1 - telescoper n W ((T + 1 : ℕ) : ℚ) := by
  exact finite_sum_is_telescoper_boundary n T hn W (quartic_is_strong_proper n (by omega) W hd) hz

theorem original_quartic_actual_quotient (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n)
    (W : ℚ[X]) (hd : W.natDegree ≤ 4) (hz : aggregate n W = 0) :
    ∃ H : ℚ[X], H.natDegree ≤ 7 * n - 3 ∧
      ∀ t : ℚ, (∀ k < n, t + (k : ℚ) ≠ 0) →
        telescoper n W t = (rootPolynomial n).eval t * H.eval t /
          (polePolynomial (n - 1)).eval t ^ 9 := by
  obtain ⟨H, hH, hdegree⟩ := checked_actual_polynomial_quotient_degree_bound n (by omega) hn W
    (quartic_is_strong_proper n (by omega) W hd) hz
  refine ⟨H, hdegree, ?_⟩
  intro t ht
  rw [telescoper_actual_rational_representation n (by omega) W t ht, hH, Polynomial.eval_mul]

theorem actual_nodes_regular (n : ℕ) (hn1 : 1 ≤ n)
    (i : Fin (n + 1) ⊕ Fin (n + 1)) : ∀ k < n, rootNode n i + (k : ℚ) ≠ 0 := by
  intro k hk
  cases i with
  | inl l => simp only [rootNode]; exact ne_of_gt (by positivity)
  | inr l =>
    simp only [rootNode]
    have hk' : (k : ℚ) < (n : ℚ) := by exact_mod_cast hk
    have hl : (0 : ℚ) ≤ (l.val : ℚ) := Nat.cast_nonneg _
    exact ne_of_lt (by linarith)

theorem zero_n_nodes_formula : rootPolynomial 0 = (X - 1) * X := by
  rw [rootPolynomial_eq_explicit_products]
  norm_num [Finset.prod_range_succ]

theorem two_n_nodes_formula : rootPolynomial 2 =
    ((X - 1) * (X - 2) * (X - 3)) * ((X + 2) * (X + 3) * (X + 4)) := by
  rw [rootPolynomial_eq_explicit_products]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num only [Nat.cast_ofNat, map_zero, map_one, map_ofNat, zero_add, add_zero, mul_one, one_mul]
  ring

theorem numerator_degree_all_multipliers (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) :
    (telescoperNumerator n W).natDegree ≤ 9 * n - 1 := telescoperNumerator_natDegree_le n hn1 W

theorem zero_n_nodes_are_distinct : Function.Injective (rootNode 0) := rootNode_injective 0

end IndependentTelescoper

run_meta do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    if name.toString.startsWith "ZetaNine.CoefficientMapTelescoper." ||
        name.toString.startsWith "IndependentTelescoper." then
      let suffix := name.toString.splitOn "." |>.getLast!
      if suffix.startsWith "_" then continue
      match ci with
      | .defnInfo _ | .thmInfo _ =>
        if name.toString.contains '✝' || name.toString.endsWith "_sunfold" then continue
        let typ ← ppExpr ci.type
        let axs ← Lean.collectAxioms name
        let value ← match ci with
          | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
          | _ => pure Json.null
        IO.println (Json.mkObj [("declaration", Json.str name.toString),
          ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString)),
          ("definitionValue", value)]).compress
      | _ => pure ()
