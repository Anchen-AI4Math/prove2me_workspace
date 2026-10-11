import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions

/-!
UNCOMPILED OFFLINE CANDIDATE. No Lean process has been run for this file.
All proof scripts below are written out without admissions. They are proposed
proofs, not a verified theorem module. They do not modify the frozen 19-file
design package, native Numerators/PF source or any independent preparation.

Use full pole-polynomial identities and cancel the common X to avoid erased
finite-set reindexing. The actual-series uniqueness lemma then proves the
whole series, including arbitrary improper numerators. Only j and s need bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapJetInsertionCandidate

open CoefficientMapJet CoefficientMapInjectivity CoefficientMapPartialFractions
open CoefficientMapFormalTransportData CoefficientMapFormalTransportNumerators
open CoefficientMapNumeratorPartialFractions

theorem pole_factor_candidate (m j : ℕ) (hj : j ≤ m) :
    polePolynomial m = (X + C (j : ℚ)) * clearedPolePolynomial m j := by
  unfold polePolynomial clearedPolePolynomial
  exact (Finset.mul_prod_erase (range (m + 1)) (fun k : ℕ => (X : ℚ[X]) + C (k : ℚ))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).symm

theorem pole_comp_shift_factor_candidate (m j : ℕ) (hj : j ≤ m) :
    (polePolynomial m).comp (shiftedVariable j) = X * shiftedClearedDenominator m j := by
  rw [pole_factor_candidate m j hj, Polynomial.mul_comp, clearedPolePolynomial_comp_shift]
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
    shiftedVariable, sub_add_cancel]

theorem pole_upper_candidate (m : ℕ) :
    polePolynomial (m + 1) = polePolynomial m * (X + C ((m + 1 : ℕ) : ℚ)) := by
  simpa only [polePolynomial] using
    (Finset.prod_range_succ (fun k : ℕ => (X : ℚ[X]) + C (k : ℚ)) (m + 1))

theorem upper_cleared_denominator_candidate (m j : ℕ) (hj : j ≤ m) :
    shiftedClearedDenominator (m + 1) j =
      shiftedClearedDenominator m j * (shiftedVariable j + C ((m + 1 : ℕ) : ℚ)) := by
  have h := congrArg (fun A : ℚ[X] => A.comp (shiftedVariable j)) (pole_upper_candidate m)
  rw [pole_comp_shift_factor_candidate (m + 1) j (by omega), Polynomial.mul_comp,
    pole_comp_shift_factor_candidate m j hj, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp] at h
  apply mul_left_cancel₀ (show (X : ℚ[X]) ≠ 0 from Polynomial.X_ne_zero)
  calc
    X * shiftedClearedDenominator (m + 1) j =
      (X * shiftedClearedDenominator m j) * (shiftedVariable j + C ((m + 1 : ℕ) : ℚ)) := h
    _ = _ := by ring

theorem shift_successor_comp_candidate (j : ℕ) (hj : 1 ≤ j) :
    (X + 1 : ℚ[X]).comp (shiftedVariable j) = shiftedVariable (j - 1) := by
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp,
    shiftedVariable, Nat.cast_sub hj, Nat.cast_one, map_sub, map_one]
  ring

theorem lower_cleared_denominator_candidate (m j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ m + 1) :
    shiftedClearedDenominator (m + 1) j =
      shiftedVariable j * shiftedClearedDenominator m (j - 1) := by
  have h := congrArg (fun A : ℚ[X] => A.comp (shiftedVariable j))
    (polePolynomial_successor_shift m)
  rw [pole_comp_shift_factor_candidate (m + 1) j hj,
    Polynomial.mul_comp, Polynomial.X_comp, Polynomial.comp_assoc,
    shift_successor_comp_candidate j hj1,
    pole_comp_shift_factor_candidate m (j - 1) (by omega)] at h
  apply mul_left_cancel₀ (show (X : ℚ[X]) ≠ 0 from Polynomial.X_ne_zero)
  calc
    X * shiftedClearedDenominator (m + 1) j =
      shiftedVariable j * (X * shiftedClearedDenominator m (j - 1)) := h
    _ = _ := by ring

theorem upper_whole_actual_series_candidate (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    numeratorClearedSeries (m + 1) j ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
      numeratorClearedSeries m j A := by
  symm
  apply numeratorClearedSeries_unique
  rw [upper_cleared_denominator_candidate m j hj, Polynomial.coe_mul, mul_pow,
    ← mul_assoc, numeratorClearedSeries_denominator_identity]
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, Polynomial.coe_mul, Polynomial.coe_pow]
  ring

theorem lower_whole_actual_series_candidate (m j : ℕ) (A : ℚ[X])
    (hj1 : 1 ≤ j) (hj : j ≤ m + 1) :
    numeratorClearedSeries (m + 1) j (X ^ 9 * A.comp (X + 1)) =
      numeratorClearedSeries m (j - 1) A := by
  symm
  apply numeratorClearedSeries_unique
  rw [lower_cleared_denominator_candidate m j hj1 hj, Polynomial.coe_mul, mul_pow]
  calc
    numeratorClearedSeries m (j - 1) A *
        ((shiftedVariable j : PowerSeries ℚ) ^ 9 *
          (shiftedClearedDenominator m (j - 1) : PowerSeries ℚ) ^ 9) =
      (numeratorClearedSeries m (j - 1) A *
        (shiftedClearedDenominator m (j - 1) : PowerSeries ℚ) ^ 9) *
          (shiftedVariable j : PowerSeries ℚ) ^ 9 := by ring
    _ = (A.comp (shiftedVariable (j - 1)) : PowerSeries ℚ) *
          (shiftedVariable j : PowerSeries ℚ) ^ 9 := by
      rw [numeratorClearedSeries_denominator_identity]
    _ = _ := by
      simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
        Polynomial.comp_assoc, shift_successor_comp_candidate j hj1,
        Polynomial.coe_mul, Polynomial.coe_pow]
      ring

theorem local_zero_of_shift_X_nine_candidate (m j s : ℕ) (A : ℚ[X])
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9)
    (hA : (X : ℚ[X]) ^ 9 ∣ A.comp (shiftedVariable j)) :
    numeratorLocalCoefficient m j s A = 0 := by
  obtain ⟨B, hB⟩ := hA
  have hseries : PowerSeries.X ^ 9 ∣ numeratorClearedSeries m j A := by
    refine ⟨(B : PowerSeries ℚ) *
      ((shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹, ?_⟩
    simp only [numeratorClearedSeries, hB, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_X]
    ring
  exact PowerSeries.X_pow_dvd_iff.mp hseries (9 - s) (by omega)

theorem upper_all_actual_jets_candidate (m j s : ℕ) (A : ℚ[X])
    (hj : j ≤ m + 1) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient (m + 1) j s ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
      if j ≤ m then numeratorLocalCoefficient m j s A else 0 := by
  by_cases h : j ≤ m
  · rw [if_pos h, numeratorLocalCoefficient,
      upper_whole_actual_series_candidate m j A h]
    rfl
  · rw [if_neg h]
    have he : j = m + 1 := by omega
    subst j
    apply local_zero_of_shift_X_nine_candidate _ _ _ _ hs1 hs9
    refine ⟨A.comp (shiftedVariable (m + 1)), ?_⟩
    simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.add_comp,
      Polynomial.X_comp, Polynomial.C_comp, shiftedVariable, sub_add_cancel]

theorem lower_all_actual_jets_candidate (m j s : ℕ) (A : ℚ[X])
    (hj : j ≤ m + 1) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient (m + 1) j s (X ^ 9 * A.comp (X + 1)) =
      if j = 0 then 0 else numeratorLocalCoefficient m (j - 1) s A := by
  by_cases h : j = 0
  · rw [if_pos h]
    subst j
    apply local_zero_of_shift_X_nine_candidate _ _ _ _ hs1 hs9
    refine ⟨A.comp (X + 1), ?_⟩
    simp only [shiftedVariable, Nat.cast_zero, map_zero, sub_zero,
      Polynomial.comp_X]
  · rw [if_neg h, numeratorLocalCoefficient,
      lower_whole_actual_series_candidate m j A (by omega) hj]
    rfl

theorem double_all_actual_jets_candidate (n j s : ℕ) (A : ℚ[X])
    (hj : j ≤ n + 2) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient (n + 2) j s
      (X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 * A.comp (X + 1)) =
      if 1 ≤ j ∧ j ≤ n + 1 then numeratorLocalCoefficient n (j - 1) s A else 0 := by
  have hpoly : X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 * A.comp (X + 1) =
      (X + C ((n + 1 + 1 : ℕ) : ℚ)) ^ 9 * (X ^ 9 * A.comp (X + 1)) := by
    push_cast
    ring
  rw [hpoly]
  have hu := upper_all_actual_jets_candidate (n + 1) j s (X ^ 9 * A.comp (X + 1))
    (by omega) hs1 hs9
  simp only [Nat.add_assoc, Nat.reduceAdd] at hu
  rw [hu]
  by_cases hright : j ≤ n + 1
  · rw [if_pos hright, lower_all_actual_jets_candidate n j s A hright hs1 hs9]
    by_cases hzero : j = 0
    · simp [hzero]
    · have hpos : 1 ≤ j := by omega
      simp only [if_neg hzero, if_pos (And.intro hpos hright)]
  · rw [if_neg hright, if_neg (by omega : ¬ (1 ≤ j ∧ j ≤ n + 1))]

end ZetaNine.CoefficientMapJetInsertionCandidate
