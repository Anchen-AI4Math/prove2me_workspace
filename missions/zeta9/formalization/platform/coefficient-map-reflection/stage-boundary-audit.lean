import Solutions.Sol_ZetaNine_CoefficientMapReflection_rho_one_zero_of_strong_proper
import Lean

open Lean Meta Polynomial Finset
open scoped BigOperators
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapReflection
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

theorem refl_ind_reverse_endpoints (n : ℕ) : n - 0 = n ∧ n - n = 0 := by omega

theorem refl_ind_reflection_involution (n : ℕ) :
    (reflectionVariable n).comp (reflectionVariable n) = (X : ℚ[X]) := by
  simp only [reflectionVariable, Polynomial.sub_comp, Polynomial.neg_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  ring

theorem refl_ind_closed_rational (n : ℕ) (hn : Even n) (W : ℚ[X]) (t : ℚ) :
    ZetaNine.CoefficientMap.weightedR n W (-(n : ℚ) - t) =
      -ZetaNine.CoefficientMap.weightedR n W t :=
  actual_weightedR_reflection n hn W t

theorem refl_ind_regular_domain (n : ℕ) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ∀ k ≤ n, (-(n : ℚ) - t) + (k : ℚ) ≠ 0 :=
  reflection_preserves_regular_points n t ht

theorem refl_ind_closed_series (n j : ℕ) (hn : Even n) (W : ℚ[X]) (hj : j ≤ n) :
    PowerSeries.rescale (-1 : ℚ) (ZetaNine.CoefficientMapJet.weightedClearedSeries n (n - j) W) =
      ZetaNine.CoefficientMapJet.weightedClearedSeries n j W :=
  actual_local_series_reflection n j hn W hj

theorem refl_ind_closed_local_sign (n j s : ℕ) (hn : Even n) (W : ℚ[X])
    (hj : j ≤ n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    ZetaNine.CoefficientMapJet.weightedLocalCoefficient n (n - j) s W =
      (-1 : ℚ) ^ (s + 1) * ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W :=
  local_coefficient_reflection n j s hn W hj hs1 hs9

theorem refl_ind_middle_even_local_zero (n j s : ℕ) (hn : Even n) (W : ℚ[X])
    (hj : j ≤ n) (hmiddle : n - j = j) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hs : Even s) :
    ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W = 0 := by
  have he := local_coefficient_reflection n j s hn W hj hs1 hs9
  rw [hmiddle, pow_succ, hs.neg_one_pow, one_mul, neg_one_mul] at he
  linarith

theorem refl_ind_closed_even_aggregate (n s : ℕ) (hn : Even n) (W : ℚ[X])
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hs : Even s) :
    (∑ j ∈ range (n + 1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) = 0 :=
  rho_even_order_zero n s hn W hs1 hs9 hs

theorem refl_ind_closed_top_coefficient (n : ℕ) (W : ℚ[X]) :
    (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      C (ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) *
        clearedPolePolynomial n j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)).coeff (9 * n + 8) =
      ∑ j ∈ range (n + 1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 1 W :=
  partialNumerator_top_coefficient_is_rho_one n W

theorem refl_ind_strong_bound_equivalent (n : ℕ) (W : ℚ[X]) :
    StrongProperMultiplier n W ↔ 2 * n + 2 * W.natDegree + 2 ≤ 9 * (n + 1) := by
  unfold StrongProperMultiplier
  omega

theorem refl_ind_closed_simple_aggregate (n : ℕ) (W : ℚ[X])
    (hstrong : 2 * n + 2 * W.natDegree + 2 ≤ 9 * (n + 1)) :
    (∑ j ∈ range (n + 1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 1 W) = 0 :=
  checked_rho_one_zero_of_strong_proper n W ((refl_ind_strong_bound_equivalent n W).mpr hstrong)

theorem refl_ind_quartic_positive_n_simple_zero (n : ℕ) (hn : 1 ≤ n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) : rho n 1 W = 0 :=
  checked_rho_one_zero_of_strong_proper n W (quartic_is_strong_proper n hn W hW)

theorem refl_ind_odd_n_one_simple_zero (W : ℚ[X]) (hW : W.natDegree ≤ 4) : rho 1 1 W = 0 :=
  refl_ind_quartic_positive_n_simple_zero 1 (by omega) W hW

theorem refl_ind_original_integer_quartic_all_five (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) :
    rho n 1 (W.map (Int.castRingHom ℚ)) = 0 ∧
    rho n 2 (W.map (Int.castRingHom ℚ)) = 0 ∧
    rho n 4 (W.map (Int.castRingHom ℚ)) = 0 ∧
    rho n 6 (W.map (Int.castRingHom ℚ)) = 0 ∧
    rho n 8 (W.map (Int.castRingHom ℚ)) = 0 := by
  refine ⟨original_integer_quartic_rho_one_zero n hn2 hn W hW, ?_, ?_, ?_, ?_⟩
  all_goals apply rho_even_order_zero n _ hn _ <;> norm_num

theorem refl_ind_rho_is_actual_finite_total (n s : ℕ) (W : ℚ[X]) :
    rho n s W = ∑ j ∈ range (n + 1),
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W := rfl

theorem refl_ind_n_zero_series (W : ℚ[X]) :
    ZetaNine.CoefficientMapJet.weightedClearedSeries 0 0 W =
      (W.comp ((X : ℚ[X]) ^ 2) : PowerSeries ℚ) := by
  have hs : ZetaNine.CoefficientMapJet.clearedSeries 0 0 = 1 := by
    simp [ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator,
      ZetaNine.CoefficientMapJet.shiftedClearedDenominator]
  have hu : ZetaNine.CoefficientMapJet.localU 0 0 = (X : ℚ[X]) ^ 2 := by
    simp [ZetaNine.CoefficientMapJet.localU,
      ZetaNine.CoefficientMapJet.shiftedVariable, pow_two]
  simp only [ZetaNine.CoefficientMapJet.weightedClearedSeries, hs, hu, one_mul]

theorem refl_ind_n_zero_X_four_simple_coefficient :
    ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 0 1 ((X : ℚ[X]) ^ 4) = 1 := by
  rw [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, refl_ind_n_zero_series]
  simp only [Polynomial.pow_comp, Polynomial.X_comp, map_pow, Polynomial.coe_X]
  rw [← pow_mul]
  norm_num

theorem refl_ind_n_zero_X_four_rho_one : rho 0 1 ((X : ℚ[X]) ^ 4) = 1 := by
  simpa [rho] using refl_ind_n_zero_X_four_simple_coefficient

theorem refl_ind_n_zero_X_four_proper_not_strong :
    ProperMultiplier 0 ((X : ℚ[X]) ^ 4) ∧ ¬ StrongProperMultiplier 0 ((X : ℚ[X]) ^ 4) := by
  norm_num [ProperMultiplier, StrongProperMultiplier, Polynomial.natDegree_pow]

theorem refl_ind_n_zero_X_four_actual_simple_pole (t : ℚ) (ht : t ≠ 0) :
    ZetaNine.CoefficientMap.weightedR 0 ((X : ℚ[X]) ^ 4) t = 1 / t := by
  simp [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]
  field_simp

theorem refl_ind_n_zero_X_four_even_cancellations :
    rho 0 2 ((X : ℚ[X]) ^ 4) = 0 ∧ rho 0 4 ((X : ℚ[X]) ^ 4) = 0 ∧
    rho 0 6 ((X : ℚ[X]) ^ 4) = 0 ∧ rho 0 8 ((X : ℚ[X]) ^ 4) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply rho_even_order_zero 0 _ (by norm_num) _ <;> norm_num

theorem refl_ind_n_zero_strong_lower_degrees (W : ℚ[X]) (hW : W.natDegree ≤ 3) :
    StrongProperMultiplier 0 W ∧ rho 0 1 W = 0 := by
  have hs : StrongProperMultiplier 0 W := by unfold StrongProperMultiplier; omega
  exact ⟨hs, checked_rho_one_zero_of_strong_proper 0 W hs⟩

theorem refl_ind_zero_multiplier_strong_every_n (n : ℕ) :
    StrongProperMultiplier n (0 : ℚ[X]) ∧ rho n 1 (0 : ℚ[X]) = 0 := by
  have hs : StrongProperMultiplier n (0 : ℚ[X]) := by
    simp only [StrongProperMultiplier, Polynomial.natDegree_zero]
    omega
  exact ⟨hs, checked_rho_one_zero_of_strong_proper n 0 hs⟩

theorem refl_ind_nonproper_still_even_zero :
    ¬ ProperMultiplier 0 ((X : ℚ[X]) ^ 5) ∧ rho 0 2 ((X : ℚ[X]) ^ 5) = 0 := by
  constructor
  · norm_num [ProperMultiplier, Polynomial.natDegree_pow]
  · exact rho_even_order_zero 0 2 (by norm_num) _ (by omega) (by omega) (by norm_num)

theorem refl_ind_odd_n_anti_reflection_fails :
    ZetaNine.CoefficientMap.weightedR 1 (1 : ℚ[X]) (-3) ≠
      -ZetaNine.CoefficientMap.weightedR 1 (1 : ℚ[X]) 2 := by
  norm_num [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct,
    Finset.prod_range_succ]

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
    `ZetaNine.CoefficientMapReflection.reflectionVariable,
    `ZetaNine.CoefficientMapReflection.rho,
    `ZetaNine.CoefficientMapReflection.StrongProperMultiplier,
    `ZetaNine.CoefficientMapReflection.partialBasis,
    `ZetaNine.CoefficientMapReflection.product_reverse_range,
    `ZetaNine.CoefficientMapReflection.product_reverse_erased_range,
    `ZetaNine.CoefficientMapReflection.sum_reverse_range,
    `ZetaNine.CoefficientMapReflection.baseNumerator_reflection,
    `ZetaNine.CoefficientMapReflection.baseU_reflection,
    `ZetaNine.CoefficientMapReflection.weightedNumerator_reflection,
    `ZetaNine.CoefficientMapReflection.polePolynomial_reflection,
    `ZetaNine.CoefficientMapReflection.clearedPolePolynomial_reflection,
    `ZetaNine.CoefficientMapReflection.reflectionVariable_eval,
    `ZetaNine.CoefficientMapReflection.actual_weightedR_reflection,
    `ZetaNine.CoefficientMapReflection.reflection_preserves_regular_points,
    `ZetaNine.CoefficientMapReflection.local_shift_reflection,
    `ZetaNine.CoefficientMapReflection.shiftedWeightedNumerator_reflection,
    `ZetaNine.CoefficientMapReflection.shiftedClearedDenominator_reflection,
    `ZetaNine.CoefficientMapReflection.rescale_neg_one_C,
    `ZetaNine.CoefficientMapReflection.rescale_neg_one_polynomial,
    `ZetaNine.CoefficientMapReflection.actual_local_series_reflection,
    `ZetaNine.CoefficientMapReflection.local_coefficient_reflection,
    `ZetaNine.CoefficientMapReflection.rho_even_order_zero,
    `ZetaNine.CoefficientMapReflection.strong_proper_implies_proper,
    `ZetaNine.CoefficientMapReflection.quartic_is_strong_proper,
    `ZetaNine.CoefficientMapReflection.clearedPolePolynomial_monic,
    `ZetaNine.CoefficientMapReflection.partialBasis_monic,
    `ZetaNine.CoefficientMapReflection.partialBasis_natDegree,
    `ZetaNine.CoefficientMapReflection.partialBasis_simple_pole_top_coefficient,
    `ZetaNine.CoefficientMapReflection.partialBasis_higher_pole_top_coefficient,
    `ZetaNine.CoefficientMapReflection.partialNumerator_top_coefficient_is_rho_one,
    `ZetaNine.CoefficientMapReflection.checked_rho_one_zero_of_strong_proper,
    `ZetaNine.CoefficientMapReflection.original_integer_quartic_strong_proper,
    `ZetaNine.CoefficientMapReflection.original_integer_quartic_rho_one_zero,
    `refl_ind_reverse_endpoints, `refl_ind_reflection_involution,
    `refl_ind_closed_rational, `refl_ind_regular_domain, `refl_ind_closed_series,
    `refl_ind_closed_local_sign, `refl_ind_middle_even_local_zero,
    `refl_ind_closed_even_aggregate, `refl_ind_closed_top_coefficient,
    `refl_ind_strong_bound_equivalent, `refl_ind_closed_simple_aggregate,
    `refl_ind_quartic_positive_n_simple_zero, `refl_ind_odd_n_one_simple_zero,
    `refl_ind_original_integer_quartic_all_five, `refl_ind_rho_is_actual_finite_total,
    `refl_ind_n_zero_series, `refl_ind_n_zero_X_four_simple_coefficient,
    `refl_ind_n_zero_X_four_rho_one, `refl_ind_n_zero_X_four_proper_not_strong,
    `refl_ind_n_zero_X_four_actual_simple_pole, `refl_ind_n_zero_X_four_even_cancellations,
    `refl_ind_n_zero_strong_lower_degrees, `refl_ind_zero_multiplier_strong_every_n,
    `refl_ind_nonproper_still_even_zero, `refl_ind_odd_n_anti_reflection_fails] do emit name
