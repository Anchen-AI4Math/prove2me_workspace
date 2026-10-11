import missions.zeta9.formalization.CoefficientMapPartialFractions
import Lean

open Lean Meta Polynomial
open scoped BigOperators
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false

theorem checked_original_integer_quartic_partial_fractions (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ZetaNine.CoefficientMap.weightedR n (W.map (Int.castRingHom ℚ)) t =
      ∑ j ∈ Finset.range (n + 1), ∑ s ∈ Finset.Icc 1 9,
        ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s (W.map (Int.castRingHom ℚ)) /
          (t + (j : ℚ)) ^ s :=
  actual_global_partial_fractions n (W.map (Int.castRingHom ℚ))
    (quartic_is_proper n _ (le_trans Polynomial.natDegree_map_le hW)) t hregular

theorem checked_n_zero_quartic_partial_fractions (W : ℚ[X]) (hW : W.natDegree ≤ 4)
    (t : ℚ) (ht : t ≠ 0) :
    ZetaNine.CoefficientMap.weightedR 0 W t =
      ∑ j ∈ Finset.range 1, ∑ s ∈ Finset.Icc 1 9,
        ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 j s W / (t + (j : ℚ)) ^ s := by
  apply actual_global_partial_fractions 0 W (quartic_is_proper 0 W hW) t
  intro k hk
  have he : k = 0 := by omega
  simpa only [he, Nat.cast_zero, add_zero] using ht

-- Strict properness permits a nonzero total simple-pole coefficient.
theorem checked_n_zero_X_four_simple_pole :
    ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 0 1 (X ^ 4 : ℚ[X]) = 1 := by
  norm_num [ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
    ZetaNine.CoefficientMapJet.weightedClearedSeries, ZetaNine.CoefficientMapJet.clearedSeries,
    ZetaNine.CoefficientMapJet.shiftedNumerator, ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    ZetaNine.CoefficientMapJet.localU, ZetaNine.CoefficientMapJet.shiftedVariable,
    Polynomial.pow_comp, Polynomial.X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_X, ← pow_two, ← pow_mul]

theorem checked_n_zero_X_four_exact_rational (t : ℚ) (ht : t ≠ 0) :
    ZetaNine.CoefficientMap.weightedR 0 (X ^ 4 : ℚ[X]) t = 1 / t := by
  norm_num [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]
  field_simp

theorem checked_n_zero_X_four_proper_but_not_order_two :
    ProperMultiplier 0 (X ^ 4 : ℚ[X]) ∧
      ¬ (2 * 0 + 2 * (X ^ 4 : ℚ[X]).natDegree ≤ 9 * (0 + 1) - 2) := by
  norm_num [ProperMultiplier]

theorem checked_all_actual_local_coefficients (n j s : ℕ) (W : ℚ[X]) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    PowerSeries.coeff (9 - s) (candidateClearedSeries n j W) =
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W :=
  candidate_local_coefficients n j s W hj hs1 hs9

theorem checked_explicit_actual_polynomial_identity (n : ℕ) (W : ℚ[X])
    (hproper : 2 * n + 2 * W.natDegree < 9 * (n + 1)) :
    weightedNumerator n W = ∑ j ∈ Finset.range (n + 1), ∑ s ∈ Finset.Icc 1 9,
      C (ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) *
        clearedPolePolynomial n j ^ 9 * (X + C (j : ℚ)) ^ (9 - s) :=
  actual_global_polynomial_partial_fractions n W hproper

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
    `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial,
    `ZetaNine.CoefficientMapPartialFractions.localTruncation,
    `ZetaNine.CoefficientMapPartialFractions.partialBlock,
    `ZetaNine.CoefficientMapPartialFractions.partialNumerator,
    `ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries,
    `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_comp_shift,
    `ZetaNine.CoefficientMapPartialFractions.localTruncation_comp_eq_sum,
    `ZetaNine.CoefficientMapPartialFractions.partialNumerator_eq_sum_blocks,
    `ZetaNine.CoefficientMapPartialFractions.partialBlock_comp_own_shift,
    `ZetaNine.CoefficientMapPartialFractions.truncation_remainder_X_pow_dvd,
    `ZetaNine.CoefficientMapPartialFractions.polynomial_X_pow_dvd_of_series,
    `ZetaNine.CoefficientMapPartialFractions.own_block_matches_nine_jets,
    `ZetaNine.CoefficientMapPartialFractions.different_block_pole_divisibility,
    `ZetaNine.CoefficientMapPartialFractions.different_block_shift_X_pow_dvd,
    `ZetaNine.CoefficientMapPartialFractions.full_candidate_matches_nine_jets,
    `ZetaNine.CoefficientMapPartialFractions.shifted_divisibility_implies_pole_divisibility,
    `ZetaNine.CoefficientMapPartialFractions.denominator_divides_actual_candidate_difference,
    `ZetaNine.CoefficientMapPartialFractions.actual_series_from_shifted_numerator,
    `ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries_denominator_identity,
    `ZetaNine.CoefficientMapPartialFractions.candidate_first_nine_coefficients,
    `ZetaNine.CoefficientMapPartialFractions.candidate_local_coefficients,
    `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_natDegree,
    `ZetaNine.CoefficientMapPartialFractions.localTruncation_natDegree_le,
    `ZetaNine.CoefficientMapPartialFractions.partialBlock_natDegree_le,
    `ZetaNine.CoefficientMapPartialFractions.partialNumerator_natDegree_le,
    `ZetaNine.CoefficientMapPartialFractions.actual_global_polynomial_partial_fractions,
    `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval,
    `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero,
    `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor,
    `ZetaNine.CoefficientMapPartialFractions.actual_weighted_rational_representation,
    `ZetaNine.CoefficientMapPartialFractions.partial_term_division,
    `ZetaNine.CoefficientMapPartialFractions.actual_global_partial_fractions,
    `checked_original_integer_quartic_partial_fractions,
    `checked_n_zero_quartic_partial_fractions, `checked_n_zero_X_four_simple_pole,
    `checked_n_zero_X_four_exact_rational, `checked_n_zero_X_four_proper_but_not_order_two,
    `checked_all_actual_local_coefficients, `checked_explicit_actual_polynomial_identity] do emit name
