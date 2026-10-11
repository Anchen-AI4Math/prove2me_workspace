import missions.zeta9.formalization.CoefficientMapReflection
import Lean

open Lean Meta Polynomial
open scoped BigOperators
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false

-- Original Eq(3), with its actual integer-quartic multiplier and all three conclusions.
theorem checked_original_Eq_three (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) :
    (∀ t : ℚ, ZetaNine.CoefficientMap.weightedR n (W.map (Int.castRingHom ℚ)) (-(n : ℚ) - t) =
      -ZetaNine.CoefficientMap.weightedR n (W.map (Int.castRingHom ℚ)) t) ∧
    (∀ j ≤ n, ∀ s, 1 ≤ s → s ≤ 9 →
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient n (n - j) s (W.map (Int.castRingHom ℚ)) =
        (-1 : ℚ) ^ (s + 1) * ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s (W.map (Int.castRingHom ℚ))) ∧
    (∀ s, 1 ≤ s → s ≤ 9 → Even s → rho n s (W.map (Int.castRingHom ℚ)) = 0) ∧
    rho n 1 (W.map (Int.castRingHom ℚ)) = 0 := by
  constructor
  · intro t
    exact actual_weightedR_reflection n hn _ t
  constructor
  · intro j hj s hs1 hs9
    exact local_coefficient_reflection n j s hn _ hj hs1 hs9
  constructor
  · intro s hs1 hs9 hs
    exact rho_even_order_zero n s hn _ hs1 hs9 hs
  · exact original_integer_quartic_rho_one_zero n hn2 hn W hW

theorem checked_regular_actual_reflection (n : ℕ) (hn : Even n) (W : ℚ[X]) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    (∀ k ≤ n, (-(n : ℚ) - t) + (k : ℚ) ≠ 0) ∧
      ZetaNine.CoefficientMap.weightedR n W (-(n : ℚ) - t) = -ZetaNine.CoefficientMap.weightedR n W t :=
  ⟨reflection_preserves_regular_points n t hregular, actual_weightedR_reflection n hn W t⟩

-- No parity assumption is needed for this strictly stronger degree argument.
theorem checked_rho_one_with_explicit_stronger_degree (n : ℕ) (W : ℚ[X])
    (h : 2 * n + 2 * W.natDegree ≤ 9 * (n + 1) - 2) :
    (∑ j ∈ Finset.range (n + 1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 1 W) = 0 :=
  rho_one_zero_of_strong_proper n W h

theorem checked_n_zero_X_four_rho_one : rho 0 1 (X ^ 4 : ℚ[X]) = 1 := by
  norm_num [rho, ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
    ZetaNine.CoefficientMapJet.weightedClearedSeries, ZetaNine.CoefficientMapJet.clearedSeries,
    ZetaNine.CoefficientMapJet.shiftedNumerator, ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    ZetaNine.CoefficientMapJet.localU, ZetaNine.CoefficientMapJet.shiftedVariable,
    Polynomial.pow_comp, Polynomial.X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_X, ← pow_two, ← pow_mul]

theorem checked_n_zero_X_four_proper_not_strong :
    ProperMultiplier 0 (X ^ 4 : ℚ[X]) ∧ ¬ StrongProperMultiplier 0 (X ^ 4 : ℚ[X]) := by
  norm_num [ProperMultiplier, StrongProperMultiplier]

theorem checked_n_zero_X_four_exact_rational (t : ℚ) (ht : t ≠ 0) :
    ZetaNine.CoefficientMap.weightedR 0 (X ^ 4 : ℚ[X]) t = 1 / t := by
  norm_num [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]
  field_simp

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
    `ZetaNine.CoefficientMapReflection.rho_one_zero_of_strong_proper,
    `ZetaNine.CoefficientMapReflection.original_integer_quartic_strong_proper,
    `ZetaNine.CoefficientMapReflection.original_integer_quartic_rho_one_zero,
    `checked_original_Eq_three, `checked_regular_actual_reflection,
    `checked_rho_one_with_explicit_stronger_degree, `checked_n_zero_X_four_rho_one,
    `checked_n_zero_X_four_proper_not_strong, `checked_n_zero_X_four_exact_rational] do emit name
