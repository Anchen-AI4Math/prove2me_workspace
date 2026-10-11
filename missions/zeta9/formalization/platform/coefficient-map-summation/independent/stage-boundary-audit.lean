import Solutions.Sol_ZetaNine_CoefficientMapSummation_actualSeries_hasSum_exactL
import Lean

open Lean Meta Polynomial Finset Filter
open scoped BigOperators Topology
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection
open ZetaNine.CoefficientMapSummation
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2200000

theorem sum_ind_closed_HasSum (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hs : 2 * n + 2 * W.natDegree + 2 ≤ 9 * (n + 1)) :
    HasSum (fun k : ℕ => (ZetaNine.CoefficientMap.weightedR n W ((k + 1 : ℕ) : ℚ) : ℝ))
      ((ZetaNine.CoefficientMapFiniteSum.constantTerm n W : ℝ) +
       ((ZetaNine.CoefficientMapFiniteSum.rho n 3 W : ℝ) * (riemannZeta (3 : ℂ)).re +
        (ZetaNine.CoefficientMapFiniteSum.rho n 5 W : ℝ) * (riemannZeta (5 : ℂ)).re +
        (ZetaNine.CoefficientMapFiniteSum.rho n 7 W : ℝ) * (riemannZeta (7 : ℂ)).re +
        (ZetaNine.CoefficientMapFiniteSum.rho n 9 W : ℝ) * (riemannZeta (9 : ℂ)).re)) := by
  have hstrong : StrongProperMultiplier n W := by unfold StrongProperMultiplier; omega
  change HasSum (actualSeries n W) _
  simpa only [exactL, zetaReal, Nat.cast_ofNat] using
    checked_actualSeries_hasSum_exactL n hn W hstrong

theorem sum_ind_closed_original_HasSum (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (fun k : ℕ => (ZetaNine.CoefficientMap.weightedR n (W.map (Int.castRingHom ℚ))
      ((k + 1 : ℕ) : ℚ) : ℝ)) (exactL n (W.map (Int.castRingHom ℚ))) :=
  original_integer_quartic_exact_infinite_L n hn2 hn W hW

theorem sum_ind_absolute_without_even (n : ℕ) (W : ℚ[X])
    (hs : 2 * n + 2 * W.natDegree + 2 ≤ 9 * (n + 1)) :
    Summable (fun k : ℕ => ‖(ZetaNine.CoefficientMap.weightedR n W ((k + 1 : ℕ) : ℚ) : ℝ)‖) := by
  apply actualSeries_norm_summable n W
  unfold StrongProperMultiplier
  omega

theorem sum_ind_partial_range_Icc_exact (n T : ℕ) (W : ℚ[X]) :
    (∑ k ∈ range T, (ZetaNine.CoefficientMap.weightedR n W ((k + 1 : ℕ) : ℚ) : ℝ)) =
      (ZetaNine.CoefficientMapFiniteSum.finiteL n T W : ℝ) :=
  actualSeries_partial_sums n T W

theorem sum_ind_partial_T_zero (n : ℕ) (W : ℚ[X]) :
    (∑ k ∈ range 0, actualSeries n W k) = (ZetaNine.CoefficientMapFiniteSum.finiteL n 0 W : ℝ) :=
  actualSeries_partial_sums n 0 W

theorem sum_ind_partial_T_one (n : ℕ) (W : ℚ[X]) :
    (∑ k ∈ range 1, actualSeries n W k) = (ZetaNine.CoefficientMap.weightedR n W 1 : ℝ) := by
  simp [actualSeries]

theorem sum_ind_zeta_is_actual_real_tsum (s : ℕ) (hs : 1 < s) :
    (riemannZeta (s : ℂ)).re = ∑' k : ℕ, 1 / (k : ℝ) ^ s :=
  zetaReal_eq_tsum s hs

theorem sum_ind_tail_including_simple_zero (n : ℕ) (W : ℚ[X]) :
    Tendsto (fun T : ℕ => (ZetaNine.CoefficientMapFiniteSum.shiftedTail n T W : ℝ)) atTop (𝓝 0) :=
  actual_shiftedTail_tendsto_zero n W

theorem sum_ind_simple_difference_absolute_bound (t : ℝ) (ht : 0 < t) (j : ℕ) :
    ‖1 / (t + (j : ℝ)) - 1 / t‖ ≤ (j : ℝ) / t ^ 2 := by
  have hj : 0 < t + (j : ℝ) := add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg j)
  rw [simple_pole_difference_identity t ht j, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg j), abs_of_pos (mul_pos ht hj)]
  have hden : t ^ 2 ≤ t * (t + (j : ℝ)) := by
    have hjnonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg j) (pow_pos ht 2) hden

theorem sum_ind_simple_j_zero :
    (fun k : ℕ => 1 / ((k : ℝ) + 1 + (0 : ℝ)) - 1 / ((k : ℝ) + 1)) =
      (fun _ : ℕ => (0 : ℝ)) := by
  funext k
  simp

theorem sum_ind_shifted_pseries_two (j : ℕ) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1 + (j : ℝ)) ^ 2) :=
  shifted_high_order_summable j 2 (by omega)

theorem sum_ind_n_zero_series (W : ℚ[X]) :
    ZetaNine.CoefficientMapJet.weightedClearedSeries 0 0 W =
      (W.comp ((X : ℚ[X]) ^ 2) : PowerSeries ℚ) := by
  have hb : ZetaNine.CoefficientMapJet.clearedSeries 0 0 = 1 := by
    simp [ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator,
      ZetaNine.CoefficientMapJet.shiftedClearedDenominator]
  have hu : ZetaNine.CoefficientMapJet.localU 0 0 = (X : ℚ[X]) ^ 2 := by
    simp [ZetaNine.CoefficientMapJet.localU,
      ZetaNine.CoefficientMapJet.shiftedVariable, pow_two]
  simp only [ZetaNine.CoefficientMapJet.weightedClearedSeries, hb, hu, one_mul]

theorem sum_ind_n_zero_X_three_strong : StrongProperMultiplier 0 ((X : ℚ[X]) ^ 3) := by
  norm_num [StrongProperMultiplier, Polynomial.natDegree_pow]

theorem sum_ind_n_zero_X_three_actual_Q (t : ℚ) (ht : t ≠ 0) :
    ZetaNine.CoefficientMap.weightedR 0 ((X : ℚ[X]) ^ 3) t = 1 / t ^ 3 := by
  simp [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]
  field_simp

theorem sum_ind_n_zero_X_three_actual_series (k : ℕ) :
    actualSeries 0 ((X : ℚ[X]) ^ 3) k = 1 / ((k : ℝ) + 1) ^ 3 := by
  unfold actualSeries
  rw [sum_ind_n_zero_X_three_actual_Q _ (by positivity)]
  push_cast
  rfl

theorem sum_ind_n_zero_X_three_rho_three :
    ZetaNine.CoefficientMapFiniteSum.rho 0 3 ((X : ℚ[X]) ^ 3) = 1 := by
  unfold ZetaNine.CoefficientMapFiniteSum.rho
  rw [Finset.sum_range_one]
  rw [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, sum_ind_n_zero_series]
  simp only [Polynomial.pow_comp, Polynomial.X_comp, map_pow, Polynomial.coe_X]
  rw [← pow_mul]
  norm_num

theorem sum_ind_n_zero_X_three_other_rho (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hs3 : s ≠ 3) :
    ZetaNine.CoefficientMapFiniteSum.rho 0 s ((X : ℚ[X]) ^ 3) = 0 := by
  have hindex : 9 - s ≠ 6 := by omega
  unfold ZetaNine.CoefficientMapFiniteSum.rho
  rw [Finset.sum_range_one]
  rw [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, sum_ind_n_zero_series]
  simp only [Polynomial.pow_comp, Polynomial.X_comp, map_pow, Polynomial.coe_X]
  rw [← pow_mul]
  norm_num [PowerSeries.coeff_X_pow, hindex, Ne.symm hindex]

theorem sum_ind_n_zero_X_three_exactL : exactL 0 ((X : ℚ[X]) ^ 3) = (riemannZeta (3 : ℂ)).re := by
  have hB : ZetaNine.CoefficientMapFiniteSum.constantTerm 0 ((X : ℚ[X]) ^ 3) = 0 := by
    simp [ZetaNine.CoefficientMapFiniteSum.constantTerm, ZetaNine.HarmonicStability.harmonicPower]
  rw [exactL, hB, sum_ind_n_zero_X_three_rho_three,
    sum_ind_n_zero_X_three_other_rho 5 (by omega) (by omega) (by omega),
    sum_ind_n_zero_X_three_other_rho 7 (by omega) (by omega) (by omega),
    sum_ind_n_zero_X_three_other_rho 9 (by omega) (by omega) (by omega)]
  simp [zetaReal]

theorem sum_ind_n_zero_X_three_HasSum :
    HasSum (actualSeries 0 ((X : ℚ[X]) ^ 3)) (riemannZeta (3 : ℂ)).re := by
  simpa only [sum_ind_n_zero_X_three_exactL] using
    checked_actualSeries_hasSum_exactL 0 (by norm_num) _ sum_ind_n_zero_X_three_strong

theorem sum_ind_n_zero_X_four_proper_not_strong :
    ProperMultiplier 0 ((X : ℚ[X]) ^ 4) ∧ ¬ StrongProperMultiplier 0 ((X : ℚ[X]) ^ 4) := by
  norm_num [ProperMultiplier, StrongProperMultiplier, Polynomial.natDegree_pow]

theorem sum_ind_n_zero_X_four_actual_series (k : ℕ) :
    actualSeries 0 ((X : ℚ[X]) ^ 4) k = 1 / ((k : ℝ) + 1) := by
  have ht : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hQ : ZetaNine.CoefficientMap.weightedR 0 ((X : ℚ[X]) ^ 4) ((k + 1 : ℕ) : ℚ) =
      1 / ((k + 1 : ℕ) : ℚ) := by
    simp [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
      ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]
    field_simp
  unfold actualSeries
  rw [hQ]
  push_cast
  rfl

theorem sum_ind_n_zero_X_four_higher_rho (s : ℕ) (hs2 : 2 ≤ s) (hs9 : s ≤ 9) :
    ZetaNine.CoefficientMapFiniteSum.rho 0 s ((X : ℚ[X]) ^ 4) = 0 := by
  have hindex : 9 - s ≠ 8 := by omega
  unfold ZetaNine.CoefficientMapFiniteSum.rho
  rw [Finset.sum_range_one]
  rw [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, sum_ind_n_zero_series]
  simp only [Polynomial.pow_comp, Polynomial.X_comp, map_pow, Polynomial.coe_X]
  rw [← pow_mul]
  norm_num [PowerSeries.coeff_X_pow, hindex, Ne.symm hindex]

theorem sum_ind_n_zero_X_four_exactL_zero : exactL 0 ((X : ℚ[X]) ^ 4) = 0 := by
  have hB : ZetaNine.CoefficientMapFiniteSum.constantTerm 0 ((X : ℚ[X]) ^ 4) = 0 := by
    simp [ZetaNine.CoefficientMapFiniteSum.constantTerm, ZetaNine.HarmonicStability.harmonicPower]
  rw [exactL, hB,
    sum_ind_n_zero_X_four_higher_rho 3 (by omega) (by omega),
    sum_ind_n_zero_X_four_higher_rho 5 (by omega) (by omega),
    sum_ind_n_zero_X_four_higher_rho 7 (by omega) (by omega),
    sum_ind_n_zero_X_four_higher_rho 9 (by omega) (by omega)]
  norm_num

theorem sum_ind_n_zero_X_four_not_summable : ¬ Summable (actualSeries 0 ((X : ℚ[X]) ^ 4)) := by
  intro h
  have hshift : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) :=
    h.congr (fun k => by simpa only [Nat.cast_add, Nat.cast_one] using
      sum_ind_n_zero_X_four_actual_series k)
  have hall : Summable (fun k : ℕ => 1 / (k : ℝ)) :=
    (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ)) 1).mp hshift
  exact Real.not_summable_one_div_natCast hall

theorem sum_ind_n_zero_X_four_no_HasSum (L : ℝ) :
    ¬ HasSum (actualSeries 0 ((X : ℚ[X]) ^ 4)) L := by
  intro h
  exact sum_ind_n_zero_X_four_not_summable h.summable

-- A totalized tsum equality alone would not certify convergence outside the domain.
theorem sum_ind_n_zero_X_four_totalized_tsum_eq_exactL :
    (∑' k : ℕ, actualSeries 0 ((X : ℚ[X]) ^ 4) k) = exactL 0 ((X : ℚ[X]) ^ 4) := by
  rw [sum_ind_n_zero_X_four_exactL_zero]
  exact tsum_eq_zero_of_not_summable sum_ind_n_zero_X_four_not_summable

theorem sum_ind_n_zero_X_four_partial_diverges :
    Tendsto (fun T : ℕ => (ZetaNine.CoefficientMapFiniteSum.finiteL 0 T ((X : ℚ[X]) ^ 4) : ℝ))
      atTop atTop := by
  have he : (fun T : ℕ => (ZetaNine.CoefficientMapFiniteSum.finiteL 0 T ((X : ℚ[X]) ^ 4) : ℝ)) =
      (fun T : ℕ => ∑ k ∈ range T, 1 / ((k : ℝ) + 1)) := by
    funext T
    rw [← actualSeries_partial_sums]
    simp_rw [sum_ind_n_zero_X_four_actual_series]
  rw [he]
  simpa only [Nat.cast_add, Nat.cast_one] using Real.tendsto_sum_range_one_div_nat_succ_atTop

theorem sum_ind_zero_multiplier_strong (n : ℕ) : StrongProperMultiplier n (0 : ℚ[X]) := by
  simp only [StrongProperMultiplier, Polynomial.natDegree_zero]
  omega

theorem sum_ind_zero_actualSeries (n : ℕ) : actualSeries n (0 : ℚ[X]) = (fun _ : ℕ => (0 : ℝ)) := by
  funext k
  simp [actualSeries, ZetaNine.CoefficientMap.weightedR]

theorem sum_ind_zero_HasSum_every_n (n : ℕ) : HasSum (actualSeries n (0 : ℚ[X])) 0 := by
  rw [sum_ind_zero_actualSeries]
  exact hasSum_zero

theorem sum_ind_zero_exactL_even (n : ℕ) (hn : Even n) : exactL n (0 : ℚ[X]) = 0 := by
  exact (checked_actualSeries_hasSum_exactL n hn 0 (sum_ind_zero_multiplier_strong n)).unique
    (sum_ind_zero_HasSum_every_n n)

theorem sum_ind_odd_n_one_absolute (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    Summable (fun k : ℕ => ‖actualSeries 1 W k‖) :=
  actualSeries_norm_summable 1 W (quartic_is_strong_proper 1 (by omega) W hW)

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
    `ZetaNine.CoefficientMapSummation.zetaReal, `ZetaNine.CoefficientMapSummation.exactL,
    `ZetaNine.CoefficientMapSummation.actualSeries,
    `ZetaNine.CoefficientMapSummation.actual_finite_odd_identity,
    `ZetaNine.CoefficientMapSummation.sum_Icc_eq_sum_range_successor,
    `ZetaNine.CoefficientMapSummation.harmonicPower_cast,
    `ZetaNine.CoefficientMapSummation.harmonicPower_cast_eq_range,
    `ZetaNine.CoefficientMapSummation.zetaReal_eq_tsum,
    `ZetaNine.CoefficientMapSummation.harmonicPower_tendsto_zeta,
    `ZetaNine.CoefficientMapSummation.shifted_reciprocal_tendsto_zero,
    `ZetaNine.CoefficientMapSummation.harmonic_fixed_tail_tendsto_zero,
    `ZetaNine.CoefficientMapSummation.actual_shiftedTail_tendsto_zero,
    `ZetaNine.CoefficientMapSummation.actual_finiteL_tendsto_exactL,
    `ZetaNine.CoefficientMapSummation.simple_pole_difference_identity,
    `ZetaNine.CoefficientMapSummation.simple_pole_difference_summable,
    `ZetaNine.CoefficientMapSummation.shifted_high_order_summable,
    `ZetaNine.CoefficientMapSummation.actualSeries_eq_principal_parts,
    `ZetaNine.CoefficientMapSummation.actualSeries_eq_cancelled_principal_parts,
    `ZetaNine.CoefficientMapSummation.actualSeries_summable,
    `ZetaNine.CoefficientMapSummation.actualSeries_norm_summable,
    `ZetaNine.CoefficientMapSummation.actualSeries_partial_sums,
    `ZetaNine.CoefficientMapSummation.checked_actualSeries_hasSum_exactL,
    `ZetaNine.CoefficientMapSummation.actualSeries_tsum_exactL,
    `ZetaNine.CoefficientMapSummation.original_integer_quartic_exact_infinite_L,
    `sum_ind_closed_HasSum, `sum_ind_closed_original_HasSum, `sum_ind_absolute_without_even,
    `sum_ind_partial_range_Icc_exact, `sum_ind_partial_T_zero, `sum_ind_partial_T_one,
    `sum_ind_zeta_is_actual_real_tsum, `sum_ind_tail_including_simple_zero,
    `sum_ind_simple_difference_absolute_bound, `sum_ind_simple_j_zero, `sum_ind_shifted_pseries_two,
    `sum_ind_n_zero_series, `sum_ind_n_zero_X_three_strong, `sum_ind_n_zero_X_three_actual_Q,
    `sum_ind_n_zero_X_three_actual_series, `sum_ind_n_zero_X_three_rho_three,
    `sum_ind_n_zero_X_three_other_rho, `sum_ind_n_zero_X_three_exactL, `sum_ind_n_zero_X_three_HasSum,
    `sum_ind_n_zero_X_four_proper_not_strong, `sum_ind_n_zero_X_four_actual_series,
    `sum_ind_n_zero_X_four_higher_rho, `sum_ind_n_zero_X_four_exactL_zero,
    `sum_ind_n_zero_X_four_not_summable, `sum_ind_n_zero_X_four_no_HasSum,
    `sum_ind_n_zero_X_four_totalized_tsum_eq_exactL,
    `sum_ind_n_zero_X_four_partial_diverges,
    `sum_ind_zero_multiplier_strong, `sum_ind_zero_actualSeries,
    `sum_ind_zero_HasSum_every_n, `sum_ind_zero_exactL_even, `sum_ind_odd_n_one_absolute] do emit name
