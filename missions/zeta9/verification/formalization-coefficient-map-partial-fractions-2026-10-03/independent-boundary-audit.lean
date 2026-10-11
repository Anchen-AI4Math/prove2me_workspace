import missions.zeta9.formalization.CoefficientMapPartialFractions
import Lean

open Lean Meta Polynomial Finset
open scoped BigOperators
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

theorem pf_ind_closed_polynomial (n : ℕ) (W : ℚ[X])
    (hp : 2 * n + 2 * W.natDegree < 9 * (n + 1)) :
    weightedNumerator n W = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      C (ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) *
        clearedPolePolynomial n j ^ 9 * (X + C (j : ℚ)) ^ (9 - s) :=
  actual_global_polynomial_partial_fractions n W hp

theorem pf_ind_closed_regular_rational (n : ℕ) (W : ℚ[X])
    (hp : 2 * n + 2 * W.natDegree < 9 * (n + 1)) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ZetaNine.CoefficientMap.weightedR n W t =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s :=
  actual_global_partial_fractions n W hp t ht

theorem pf_ind_candidate_nine_without_proper (n j s : ℕ) (W : ℚ[X])
    (hj : j ≤ n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    PowerSeries.coeff (9 - s) (candidateClearedSeries n j W) =
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W :=
  candidate_local_coefficients n j s W hj hs1 hs9

theorem pf_ind_quartic_every_n (n : ℕ) (W : ℚ[X]) (hW : W.natDegree ≤ 4)
    (t : ℚ) (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ZetaNine.CoefficientMap.weightedR n W t =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s :=
  actual_global_partial_fractions n W (quartic_is_proper n W hW) t ht

theorem pf_ind_original_integer_quartic (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ZetaNine.CoefficientMap.weightedR n (W.map (Int.castRingHom ℚ)) t =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s (W.map (Int.castRingHom ℚ)) /
          (t + (j : ℚ)) ^ s :=
  pf_ind_quartic_every_n n (W.map (Int.castRingHom ℚ))
    (le_trans Polynomial.natDegree_map_le hW) t ht

theorem pf_ind_n_zero_series (W : ℚ[X]) :
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

theorem pf_ind_n_zero_X_four_proper : ProperMultiplier 0 ((X : ℚ[X]) ^ 4) := by
  norm_num [ProperMultiplier, Polynomial.natDegree_pow]

theorem pf_ind_n_zero_X_four_simple_coefficient :
    ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 0 1 ((X : ℚ[X]) ^ 4) = 1 := by
  rw [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, pf_ind_n_zero_series]
  simp only [Polynomial.pow_comp, Polynomial.X_comp, map_pow, Polynomial.coe_X]
  rw [← pow_mul]
  norm_num

theorem pf_ind_n_zero_X_four_actual_simple_pole (t : ℚ) (ht : t ≠ 0) :
    ZetaNine.CoefficientMap.weightedR 0 ((X : ℚ[X]) ^ 4) t = 1 / t := by
  simp [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]
  field_simp

theorem pf_ind_n_zero_X_four_not_two_degree_gap :
    ¬ (2 * 0 + 2 * ((X : ℚ[X]) ^ 4).natDegree + 2 ≤ 9 * (0 + 1)) := by
  norm_num [Polynomial.natDegree_pow]

theorem pf_ind_n_zero_total_simple_coefficient :
    (∑ j ∈ range 1,
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 j 1 ((X : ℚ[X]) ^ 4)) = 1 := by
  simpa using pf_ind_n_zero_X_four_simple_coefficient

theorem pf_ind_n_zero_X_four_actual_global_sum (t : ℚ) (ht : t ≠ 0) :
    (∑ j ∈ range 1, ∑ s ∈ Icc 1 9,
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 j s ((X : ℚ[X]) ^ 4) /
        (t + (j : ℚ)) ^ s) = 1 / t := by
  have hregular : ∀ (k : ℕ), k ≤ 0 → t + (k : ℚ) ≠ 0 := by
    intro k hk
    have h : k = 0 := by omega
    simpa [h] using ht
  exact (actual_global_partial_fractions 0 _ pf_ind_n_zero_X_four_proper t hregular).symm.trans
    (pf_ind_n_zero_X_four_actual_simple_pole t ht)

-- Outside strict properness the finite candidate misses a genuine polynomial part.
theorem pf_ind_n_zero_X_five_coefficients_zero (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 0 s ((X : ℚ[X]) ^ 5) = 0 := by
  have hindex : 9 - s ≠ 10 := by omega
  rw [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, pf_ind_n_zero_series]
  simp only [Polynomial.pow_comp, Polynomial.X_comp, map_pow, Polynomial.coe_X]
  rw [← pow_mul]
  norm_num [PowerSeries.coeff_X_pow, hindex, Ne.symm hindex]

theorem pf_ind_n_zero_X_five_partialNumerator_zero :
    partialNumerator 0 ((X : ℚ[X]) ^ 5) = 0 := by
  simp only [partialNumerator, zero_add, sum_range_one]
  apply Finset.sum_eq_zero
  intro s hs
  rw [pf_ind_n_zero_X_five_coefficients_zero s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2]
  simp

theorem pf_ind_n_zero_X_five_not_proper : ¬ ProperMultiplier 0 ((X : ℚ[X]) ^ 5) := by
  norm_num [ProperMultiplier, Polynomial.natDegree_pow]

theorem pf_ind_n_zero_nonproper_polynomial_failure :
    weightedNumerator 0 ((X : ℚ[X]) ^ 5) ≠ partialNumerator 0 ((X : ℚ[X]) ^ 5) := by
  intro heq
  have hz := heq.trans pf_ind_n_zero_X_five_partialNumerator_zero
  have hW := weightedNumerator_zero_implies_multiplier_zero 0 ((X : ℚ[X]) ^ 5) hz
  exact pow_ne_zero 5 Polynomial.X_ne_zero hW

theorem pf_ind_n_zero_X_five_rational_sum_zero (t : ℚ) :
    (∑ j ∈ range 1, ∑ s ∈ Icc 1 9,
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 j s ((X : ℚ[X]) ^ 5) /
        (t + (j : ℚ)) ^ s) = 0 := by
  rw [Finset.sum_range_one]
  apply Finset.sum_eq_zero
  intro s hs
  rw [pf_ind_n_zero_X_five_coefficients_zero s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2]
  simp

theorem pf_ind_n_zero_X_five_actual_at_one :
    ZetaNine.CoefficientMap.weightedR 0 ((X : ℚ[X]) ^ 5) 1 = 1 := by
  norm_num [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]

theorem pf_ind_n_zero_nonproper_regular_point_failure :
    (∀ (k : ℕ), k ≤ 0 → (1 : ℚ) + (k : ℚ) ≠ 0) ∧
      ZetaNine.CoefficientMap.weightedR 0 ((X : ℚ[X]) ^ 5) 1 ≠
        ∑ j ∈ range 1, ∑ s ∈ Icc 1 9,
          ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 j s ((X : ℚ[X]) ^ 5) /
            ((1 : ℚ) + (j : ℚ)) ^ s := by
  constructor
  · intro k hk
    have h : k = 0 := by omega
    norm_num [h]
  · rw [pf_ind_n_zero_X_five_actual_at_one, pf_ind_n_zero_X_five_rational_sum_zero]
    norm_num

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
    `pf_ind_closed_polynomial, `pf_ind_closed_regular_rational,
    `pf_ind_candidate_nine_without_proper, `pf_ind_quartic_every_n,
    `pf_ind_original_integer_quartic, `pf_ind_n_zero_series,
    `pf_ind_n_zero_X_four_proper, `pf_ind_n_zero_X_four_simple_coefficient,
    `pf_ind_n_zero_X_four_actual_simple_pole, `pf_ind_n_zero_X_four_not_two_degree_gap,
    `pf_ind_n_zero_total_simple_coefficient, `pf_ind_n_zero_X_four_actual_global_sum,
    `pf_ind_n_zero_X_five_coefficients_zero, `pf_ind_n_zero_X_five_partialNumerator_zero,
    `pf_ind_n_zero_X_five_not_proper, `pf_ind_n_zero_nonproper_polynomial_failure,
    `pf_ind_n_zero_X_five_rational_sum_zero, `pf_ind_n_zero_X_five_actual_at_one,
    `pf_ind_n_zero_nonproper_regular_point_failure] do emit name
