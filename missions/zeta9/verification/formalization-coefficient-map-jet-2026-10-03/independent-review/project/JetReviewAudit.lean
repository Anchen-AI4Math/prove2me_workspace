import missions.zeta9.formalization.CoefficientMapJet

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace ZetaNine.CoefficientMapJetIndependentReview
open ZetaNine.CoefficientMapJet

theorem exists_unique_actual_series (n j : ℕ) :
    ∃! S : PowerSeries ℚ,
      S * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
        (shiftedNumerator n j : PowerSeries ℚ) := by
  refine ⟨clearedSeries n j, clearedSeries_denominator_identity n j, ?_⟩
  intro S hS
  exact clearedSeries_unique n j S hS

theorem weighted_series_is_actual_quotient (n j : ℕ) (W : ℚ[X]) :
    weightedClearedSeries n j W =
      ((shiftedNumerator n j * W.comp (localU n j) : ℚ[X]) : PowerSeries ℚ) *
        ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹ := by
  have h : PowerSeries.constantCoeff ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (shiftedClearedDenominator_constant_ne_zero n j)
  calc
    _ = weightedClearedSeries n j W *
        ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 *
          ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹) := by
      rw [PowerSeries.mul_inv_cancel _ h, mul_one]
    _ = (weightedClearedSeries n j W *
        (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) *
          ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹ := (mul_assoc _ _ _).symm
    _ = _ := by rw [weightedClearedSeries_denominator_identity]

theorem exists_unique_weighted_actual_series (n j : ℕ) (W : ℚ[X]) :
    ∃! S : PowerSeries ℚ,
      S * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
        ((shiftedNumerator n j * W.comp (localU n j) : ℚ[X]) : PowerSeries ℚ) := by
  have h : PowerSeries.constantCoeff ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (shiftedClearedDenominator_constant_ne_zero n j)
  refine ⟨weightedClearedSeries n j W, weightedClearedSeries_denominator_identity n j W, ?_⟩
  intro S hS
  rw [weighted_series_is_actual_quotient n j W]
  calc
    _ = S * ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 *
        ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹) := by
      rw [PowerSeries.mul_inv_cancel _ h, mul_one]
    _ = (S * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) *
        ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹ := (mul_assoc _ _ _).symm
    _ = _ := by rw [hS]

theorem actual_weighted_regular_bridge (n j : ℕ) (hj : j ≤ n)
    (W : ℚ[X]) (z : ℚ)
    (hregular : ∀ k ≤ n, -(j : ℚ) + z + (k : ℚ) ≠ 0) :
    ZetaNine.CoefficientMap.weightedR n W (-(j : ℚ) + z) * z ^ 9 =
      (shiftedNumerator n j * W.comp (localU n j)).eval z /
        (shiftedClearedDenominator n j).eval z ^ 9 := by
  rw [actual_weighted_local_rational_expression]
  have h := ZetaNine.CoefficientMap.clear_weighted_highest_pole n j hj W
    (-(j : ℚ) + z) hregular
  have he : -(j : ℚ) + z + j = z := by ring
  rw [he] at h
  exact h

theorem all_orders_actual_convolution (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℚ[X]) :
    PowerSeries.coeff (9 - s) (weightedClearedSeries n j W) =
      ∑ l ∈ Finset.Icc s 9, PowerSeries.coeff (9 - l) (clearedSeries n j) *
        (W.comp (C (-(j : ℚ) * (n - j : ℕ)) +
          C ((n : ℚ) - 2 * j) * X + X ^ 2)).coeff (l - s) := by
  exact coefficient_convolution_explicit n j s hj hs1 hs9 W

theorem all_orders_integer_W_convolution (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℤ[X]) :
    weightedLocalCoefficient n j s (W.map (Int.castRingHom ℚ)) =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l *
        ((W.comp (integerLocalU n j)).coeff (l - s) : ℚ) :=
  integer_coefficient_convolution n j s hj hs1 hs9 W

theorem integer_multiplier_coefficients (n j : ℕ) (hj : j ≤ n)
    (W : ℤ[X]) (k : ℕ) :
    ∃ a : ℤ, ((W.map (Int.castRingHom ℚ)).comp (localU n j)).coeff k = (a : ℚ) := by
  refine ⟨(W.comp (integerLocalU n j)).coeff k, ?_⟩
  rw [← integerLocalU_map n j hj, ← Polynomial.map_comp]
  simp

theorem zero_boundary_series : clearedSeries 0 0 = 1 := by
  apply (clearedSeries_unique 0 0 1 ?_).symm
  simp [shiftedClearedDenominator, shiftedNumerator, shiftedVariable, Finset.range_one]

theorem zero_boundary_lower_coefficients (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s < 9) :
    localCoefficient 0 0 s = 0 := by
  rw [localCoefficient, zero_boundary_series]
  have h : 9 - s ≠ 0 := by omega
  simp [PowerSeries.coeff_one, h]

theorem zero_boundary_top_coefficient : localCoefficient 0 0 9 = 1 := by
  rw [localCoefficient, zero_boundary_series]
  simp

#print shiftedNumerator
#print shiftedClearedDenominator
#print clearedSeries
#print weightedClearedSeries
#print localCoefficient
#print weightedLocalCoefficient
#check @actual_weighted_local_rational_expression
#check @clearedSeries_unique
#check @coefficient_convolution_explicit
#check @integer_coefficient_convolution
#print axioms exists_unique_actual_series
#print axioms weighted_series_is_actual_quotient
#print axioms exists_unique_weighted_actual_series
#print axioms actual_weighted_regular_bridge
#print axioms all_orders_actual_convolution
#print axioms all_orders_integer_W_convolution
#print axioms integer_multiplier_coefficients
#print axioms zero_boundary_series
#print axioms zero_boundary_lower_coefficients
#print axioms zero_boundary_top_coefficient
end ZetaNine.CoefficientMapJetIndependentReview
