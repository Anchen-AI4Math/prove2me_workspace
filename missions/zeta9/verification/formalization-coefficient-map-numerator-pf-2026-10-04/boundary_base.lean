import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapNumeratorPartialFractions

theorem checked_exact_generic_polynomial_endpoint (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) : A = numeratorPartialNumerator m A :=
  actual_numerator_polynomial_partial_fractions m A hproper

theorem checked_exact_generic_regular_point_endpoint (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) (t : ℚ)
    (hregular : ∀ k ≤ m, t + (k : ℚ) ≠ 0) :
    A.eval t / (polePolynomial m).eval t ^ 9 =
      ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s :=
  actual_numerator_global_partial_fractions m A hproper t hregular

theorem checked_exact_generic_actual_jet_injectivity (m : ℕ) (A B : ℚ[X])
    (hA : A.natDegree < 9 * (m + 1)) (hB : B.natDegree < 9 * (m + 1))
    (hjets : ∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) : A = B :=
  actual_numerator_local_coefficients_injective m A B hA hB hjets

theorem checked_zero_actual_jet (m j s : ℕ) : numeratorLocalCoefficient m j s (0 : ℚ[X]) = 0 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries]

theorem checked_zero_numerator_reconstruction (m : ℕ) :
    (0 : ℚ[X]) = numeratorPartialNumerator m 0 :=
  actual_numerator_polynomial_partial_fractions m 0 (by simp; omega)

theorem checked_m0_Aone_reconstruction : (1 : ℚ[X]) = numeratorPartialNumerator 0 1 :=
  actual_numerator_polynomial_partial_fractions 0 1 (by norm_num)

theorem checked_m0_critical_X8_reconstruction : (X ^ 8 : ℚ[X]) = numeratorPartialNumerator 0 (X ^ 8) :=
  actual_numerator_polynomial_partial_fractions 0 (X ^ 8) (by norm_num)

theorem checked_m0_X9_is_excluded : ¬ (X ^ 9 : ℚ[X]).natDegree < 9 * (0 + 1) := by norm_num

theorem checked_m0_highest_pole_of_one : numeratorLocalCoefficient 0 0 9 (1 : ℚ[X]) = 1 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    ZetaNine.CoefficientMapJet.shiftedVariable]

theorem checked_m0_simple_pole_of_X8 : numeratorLocalCoefficient 0 0 1 (X ^ 8 : ℚ[X]) = 1 := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    ZetaNine.CoefficientMapJet.shiftedVariable]

theorem checked_m0_simple_pole_regular_PF (t : ℚ) (ht : t ≠ 0) :
    (1 : ℚ) / t = ∑ j ∈ range (0 + 1), ∑ s ∈ Icc 1 9,
      numeratorLocalCoefficient 0 j s (X ^ 8 : ℚ[X]) / (t + (j : ℚ)) ^ s := by
  have h := actual_numerator_global_partial_fractions 0 (X ^ 8) (by norm_num) t
    (by intro k hk; have hk0 : k = 0 := by omega; simpa [hk0] using ht)
  have he : (X ^ 8 : ℚ[X]).eval t / (polePolynomial 0).eval t ^ 9 = (1 : ℚ) / t := by
    have hp : (polePolynomial 0).eval t = t := by simp [polePolynomial]
    rw [hp]
    simp only [eval_pow, eval_X]
    field_simp [ht] <;> ring
  rw [he] at h
  exact h

theorem checked_two_pole_constant_reconstruction : (1 : ℚ[X]) = numeratorPartialNumerator 1 1 :=
  actual_numerator_polynomial_partial_fractions 1 1 (by norm_num)

theorem checked_actual_weighted_jets_agree (m j s : ℕ) (W : ℚ[X]) :
    numeratorLocalCoefficient m j s (weightedNumerator m W) =
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient m j s W :=
  numerator_local_coefficient_weighted_agreement m j s W

theorem checked_n1_q1_actual_shifted_remainder :
    shiftedRemainderNumerator 1 (1 : ℚ[X]) = (X + 1) ^ 2 - 4 := by
  norm_num [shiftedRemainderNumerator, remainderNumerator, Finset.prod_range_succ,
    Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp] <;> ring

theorem checked_n1_q1_actual_remainder_reconstruction :
    shiftedRemainderNumerator 1 (1 : ℚ[X]) =
      numeratorPartialNumerator 2 (shiftedRemainderNumerator 1 (1 : ℚ[X])) := by
  apply actual_numerator_polynomial_partial_fractions
  rw [checked_n1_q1_actual_shifted_remainder]
  have hd := Polynomial.natDegree_sub_le ((X + 1) ^ 2 : ℚ[X]) (4 : ℚ[X])
  have hf : ((X + 1) ^ 2 : ℚ[X]).natDegree = 2 := by
    rw [Polynomial.natDegree_pow]
    have hx : (X + 1 : ℚ[X]).natDegree = 1 := by
      simpa using Polynomial.natDegree_X_add_C (1 : ℚ)
    rw [hx]
  have hc : (4 : ℚ[X]).natDegree = 0 := by norm_num
  rw [hf, hc] at hd
  omega
