import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
import missions.zeta9.formalization.CoefficientMapFiniteSum

/-!
UNCOMPILED COMPLETE WRITTEN CANDIDATE. No Lean/Lake invocation has been
performed for this module. These are proposed proof scripts, not verified facts.
The generic insertions retain arbitrary numerators and m=0. The actual chosen
transport retains n>=1, every actual pole and orders one through nine, including
the right boundary -c(n+1,s). Finite rho cancellation adds no parity or analytic
premise. The formal constant/matrix output bridge remains a later obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFormalTransportJets

open CoefficientMapJet CoefficientMapInjectivity CoefficientMapPartialFractions
open CoefficientMapFormalTransportData CoefficientMapFormalTransportNumerators
open CoefficientMapNumeratorPartialFractions

theorem pole_factor (m j : ℕ) (hj : j ≤ m) :
    polePolynomial m = (X + C (j : ℚ)) * clearedPolePolynomial m j := by
  unfold polePolynomial clearedPolePolynomial
  exact (Finset.mul_prod_erase (range (m + 1)) (fun k : ℕ => (X : ℚ[X]) + C (k : ℚ))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).symm

theorem pole_comp_shift_factor (m j : ℕ) (hj : j ≤ m) :
    (polePolynomial m).comp (shiftedVariable j) = X * shiftedClearedDenominator m j := by
  rw [pole_factor m j hj, Polynomial.mul_comp, clearedPolePolynomial_comp_shift]
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
    shiftedVariable, sub_add_cancel]

theorem pole_upper (m : ℕ) :
    polePolynomial (m + 1) = polePolynomial m * (X + C ((m + 1 : ℕ) : ℚ)) := by
  simpa only [polePolynomial] using
    (Finset.prod_range_succ (fun k : ℕ => (X : ℚ[X]) + C (k : ℚ)) (m + 1))

theorem upper_cleared_denominator (m j : ℕ) (hj : j ≤ m) :
    shiftedClearedDenominator (m + 1) j =
      shiftedClearedDenominator m j * (shiftedVariable j + C ((m + 1 : ℕ) : ℚ)) := by
  have h := congrArg (fun A : ℚ[X] => A.comp (shiftedVariable j)) (pole_upper m)
  rw [pole_comp_shift_factor (m + 1) j (by omega), Polynomial.mul_comp,
    pole_comp_shift_factor m j hj, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp] at h
  apply mul_left_cancel₀ (show (X : ℚ[X]) ≠ 0 from Polynomial.X_ne_zero)
  calc
    X * shiftedClearedDenominator (m + 1) j =
      (X * shiftedClearedDenominator m j) * (shiftedVariable j + C ((m + 1 : ℕ) : ℚ)) := h
    _ = _ := by ring

theorem shift_successor_comp (j : ℕ) (hj : 1 ≤ j) :
    (X + 1 : ℚ[X]).comp (shiftedVariable j) = shiftedVariable (j - 1) := by
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp,
    shiftedVariable, Nat.cast_sub hj, Nat.cast_one, map_sub, map_one]
  ring

theorem lower_cleared_denominator (m j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ m + 1) :
    shiftedClearedDenominator (m + 1) j =
      shiftedVariable j * shiftedClearedDenominator m (j - 1) := by
  have h := congrArg (fun A : ℚ[X] => A.comp (shiftedVariable j))
    (polePolynomial_successor_shift m)
  rw [pole_comp_shift_factor (m + 1) j hj,
    Polynomial.mul_comp, Polynomial.X_comp, Polynomial.comp_assoc,
    shift_successor_comp j hj1,
    pole_comp_shift_factor m (j - 1) (by omega)] at h
  apply mul_left_cancel₀ (show (X : ℚ[X]) ≠ 0 from Polynomial.X_ne_zero)
  calc
    X * shiftedClearedDenominator (m + 1) j =
      shiftedVariable j * (X * shiftedClearedDenominator m (j - 1)) := h
    _ = _ := by ring

theorem upper_whole_actual_series (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    numeratorClearedSeries (m + 1) j ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
      numeratorClearedSeries m j A := by
  symm
  apply numeratorClearedSeries_unique
  rw [upper_cleared_denominator m j hj, Polynomial.coe_mul, mul_pow,
    ← mul_assoc, numeratorClearedSeries_denominator_identity]
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, Polynomial.coe_mul, Polynomial.coe_pow]
  ring

theorem lower_whole_actual_series (m j : ℕ) (A : ℚ[X])
    (hj1 : 1 ≤ j) (hj : j ≤ m + 1) :
    numeratorClearedSeries (m + 1) j (X ^ 9 * A.comp (X + 1)) =
      numeratorClearedSeries m (j - 1) A := by
  symm
  apply numeratorClearedSeries_unique
  rw [lower_cleared_denominator m j hj1 hj, Polynomial.coe_mul, mul_pow]
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
        Polynomial.comp_assoc, shift_successor_comp j hj1,
        Polynomial.coe_mul, Polynomial.coe_pow]
      ring

theorem local_zero_of_shift_X_nine (m j s : ℕ) (A : ℚ[X])
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

theorem upper_all_actual_jets (m j s : ℕ) (A : ℚ[X])
    (hj : j ≤ m + 1) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient (m + 1) j s ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
      if j ≤ m then numeratorLocalCoefficient m j s A else 0 := by
  by_cases h : j ≤ m
  · rw [if_pos h, numeratorLocalCoefficient,
      upper_whole_actual_series m j A h]
    rfl
  · rw [if_neg h]
    have he : j = m + 1 := by omega
    subst j
    apply local_zero_of_shift_X_nine _ _ _ _ hs1 hs9
    refine ⟨A.comp (shiftedVariable (m + 1)), ?_⟩
    simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.add_comp,
      Polynomial.X_comp, Polynomial.C_comp, shiftedVariable, sub_add_cancel]

theorem lower_all_actual_jets (m j s : ℕ) (A : ℚ[X])
    (hj : j ≤ m + 1) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient (m + 1) j s (X ^ 9 * A.comp (X + 1)) =
      if j = 0 then 0 else numeratorLocalCoefficient m (j - 1) s A := by
  by_cases h : j = 0
  · rw [if_pos h]
    subst j
    apply local_zero_of_shift_X_nine _ _ _ _ hs1 hs9
    refine ⟨A.comp (X + 1), ?_⟩
    simp only [shiftedVariable, Nat.cast_zero, map_zero, sub_zero,
      Polynomial.comp_X]
  · rw [if_neg h, numeratorLocalCoefficient,
      lower_whole_actual_series m j A (by omega) hj]
    rfl

theorem double_all_actual_jets (n j s : ℕ) (A : ℚ[X])
    (hj : j ≤ n + 2) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient (n + 2) j s
      (X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 * A.comp (X + 1)) =
      if 1 ≤ j ∧ j ≤ n + 1 then numeratorLocalCoefficient n (j - 1) s A else 0 := by
  have hpoly : X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 * A.comp (X + 1) =
      (X + C ((n + 1 + 1 : ℕ) : ℚ)) ^ 9 * (X ^ 9 * A.comp (X + 1)) := by
    push_cast
    ring
  rw [hpoly]
  have hu := upper_all_actual_jets (n + 1) j s (X ^ 9 * A.comp (X + 1))
    (by omega) hs1 hs9
  simp only [Nat.add_assoc, Nat.reduceAdd] at hu
  rw [hu]
  by_cases hright : j ≤ n + 1
  · rw [if_pos hright, lower_all_actual_jets n j s A hright hs1 hs9]
    by_cases hzero : j = 0
    · simp [hzero]
    · have hpos : 1 ≤ j := by omega
      simp only [if_neg hzero, if_pos (And.intro hpos hright)]
  · rw [if_neg hright, if_neg (by omega : ¬ (1 ≤ j ∧ j ≤ n + 1))]

theorem numeratorClearedSeries_add (m j : ℕ) (A B : ℚ[X]) :
    numeratorClearedSeries m j (A + B) =
      numeratorClearedSeries m j A + numeratorClearedSeries m j B := by
  simp only [numeratorClearedSeries, Polynomial.add_comp, Polynomial.coe_add, add_mul]

theorem numeratorClearedSeries_sub (m j : ℕ) (A B : ℚ[X]) :
    numeratorClearedSeries m j (A - B) =
      numeratorClearedSeries m j A - numeratorClearedSeries m j B := by
  simp only [numeratorClearedSeries, Polynomial.sub_comp, Polynomial.coe_sub, sub_mul]

theorem numeratorClearedSeries_smul (m j : ℕ) (a : ℚ) (A : ℚ[X]) :
    numeratorClearedSeries m j (a • A) = a • numeratorClearedSeries m j A := by
  simp only [numeratorClearedSeries, Polynomial.smul_comp, Polynomial.coe_smul,
    smul_mul_assoc]

theorem numeratorLocalCoefficient_add (m j s : ℕ) (A B : ℚ[X]) :
    numeratorLocalCoefficient m j s (A + B) =
      numeratorLocalCoefficient m j s A + numeratorLocalCoefficient m j s B := by
  simp only [numeratorLocalCoefficient, numeratorClearedSeries_add, map_add]

theorem numeratorLocalCoefficient_smul (m j s : ℕ) (a : ℚ) (A : ℚ[X]) :
    numeratorLocalCoefficient m j s (a • A) = a * numeratorLocalCoefficient m j s A := by
  simp only [numeratorLocalCoefficient, numeratorClearedSeries_smul,
    PowerSeries.coeff_smul, smul_eq_mul]

/-- The actual chosen pair, every genuine pole and every order one through nine.
This is a complete written proof candidate and has not been compiled. -/
theorem actual_chosen_all_local_coefficients_transport (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (j s : ℕ) (hj : j ≤ n + 2) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    weightedLocalCoefficient (n + 2) j s (X ^ r.val) =
      extendedOldCoefficient n j s (connectionP n r) +
        extendedRemainderCoefficient n j s (connectionQ n r) -
        previousRemainderCoefficient n j s (connectionQ n r) := by
  have hd := double_all_actual_jets n j s
    (weightedNumerator n (connectionP n r)) hj hs1 hs9
  rw [numerator_local_coefficient_weighted_agreement] at hd
  change numeratorLocalCoefficient (n + 2) j s
      (X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 *
        (weightedNumerator n (connectionP n r)).comp (X + 1)) =
      extendedOldCoefficient n j s (connectionP n r) at hd
  have hcast : (X + C (((n + 1 + 1 : ℕ) : ℚ)) : ℚ[X]) =
      X + C ((n : ℚ) + 2) := by
    push_cast
    ring
  have hu := upper_all_actual_jets (n + 1) j s
    (shiftedRemainderNumerator n (connectionQ n r)) (by omega) hs1 hs9
  rw [hcast] at hu
  simp only [Nat.add_assoc, Nat.reduceAdd] at hu
  change numeratorLocalCoefficient (n + 2) j s
      ((X + C ((n : ℚ) + 2)) ^ 9 * shiftedRemainderNumerator n (connectionQ n r)) =
      extendedRemainderCoefficient n j s (connectionQ n r) at hu
  have hl : numeratorLocalCoefficient (n + 2) j s
      (X ^ 9 * (shiftedRemainderNumerator n (connectionQ n r)).comp (X + 1)) =
      previousRemainderCoefficient n j s (connectionQ n r) := by
    have h := lower_all_actual_jets (n + 1) j s
      (shiftedRemainderNumerator n (connectionQ n r)) (by omega) hs1 hs9
    simp only [Nat.add_assoc, Nat.reduceAdd] at h
    by_cases hz : j = 0
    · simpa only [previousRemainderCoefficient, if_pos hz] using h
    · have hp : j - 1 ≤ n + 1 := by omega
      simpa only [previousRemainderCoefficient, if_neg hz,
        extendedRemainderCoefficient, if_pos hp, remainderCoefficient] using h
  have h := congrArg (numeratorLocalCoefficient (n + 2) j s)
    (actual_chosen_cleared_numerator_transport n hn r)
  rw [numerator_local_coefficient_weighted_agreement,
    CoefficientMapNumeratorPartialFractions.numeratorLocalCoefficient_sub,
    numeratorLocalCoefficient_add, hd, hu, hl] at h
  exact h

theorem actual_chosen_left_boundary_coefficient (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    weightedLocalCoefficient (n + 2) 0 s (X ^ r.val) =
      remainderCoefficient n 0 s (connectionQ n r) := by
  simpa [extendedOldCoefficient, extendedRemainderCoefficient,
    previousRemainderCoefficient] using
      actual_chosen_all_local_coefficients_transport n hn r 0 s (by omega) hs1 hs9

theorem actual_chosen_right_boundary_coefficient (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    weightedLocalCoefficient (n + 2) (n + 2) s (X ^ r.val) =
      -remainderCoefficient n (n + 1) s (connectionQ n r) := by
  have hupper : ¬ n + 2 ≤ n + 1 := by omega
  have hband : ¬ (1 ≤ n + 2 ∧ n + 2 ≤ n + 1) := by omega
  have hnz : n + 2 ≠ 0 := by omega
  have hprev : (n + 2) - 1 = n + 1 := by omega
  simpa only [extendedOldCoefficient, if_neg hband,
    extendedRemainderCoefficient, if_neg hupper, previousRemainderCoefficient,
    if_neg hnz, hprev, if_pos (le_refl (n + 1)), zero_add, zero_sub] using
      actual_chosen_all_local_coefficients_transport n hn r (n + 2) s
        (le_refl _) hs1 hs9

/-- Pure finite padding identity, including the empty old range. -/
theorem sum_upper_zero_extension (N : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range (N + 2), if j ≤ N then f j else 0) =
      ∑ j ∈ range (N + 1), f j := by
  rw [Finset.sum_range_succ]
  have h : (∑ j ∈ range (N + 1), if j ≤ N then f j else 0) =
      ∑ j ∈ range (N + 1), f j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  rw [h, if_neg (by omega : ¬ N + 1 ≤ N), add_zero]

/-- The zero inserted at the left endpoint precedes the old finite array. -/
theorem sum_lower_zero_extension (N : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range (N + 2), if j = 0 then 0 else f (j - 1)) =
      ∑ j ∈ range (N + 1), f j := by
  have h : ∀ K : ℕ,
      (∑ j ∈ range (K + 1), if j = 0 then 0 else f (j - 1)) =
        ∑ j ∈ range K, f j := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        simp
  simpa only [Nat.add_assoc, Nat.reduceAdd] using h (N + 1)

theorem sum_extendedOldCoefficient (n s : ℕ) (P : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedOldCoefficient n j s P) =
      CoefficientMapFiniteSum.rho n s P := by
  rw [Finset.sum_range_succ]
  have hlast : extendedOldCoefficient n (n + 2) s P = 0 := by
    rw [extendedOldCoefficient, if_neg (by omega : ¬ (1 ≤ n + 2 ∧ n + 2 ≤ n + 1))]
  rw [hlast, add_zero]
  have h : (∑ j ∈ range (n + 2), extendedOldCoefficient n j s P) =
      ∑ j ∈ range (n + 2), if j = 0 then 0 else weightedLocalCoefficient n (j - 1) s P := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases hz : j = 0
    · simp [extendedOldCoefficient, hz]
    · have hb : 1 ≤ j ∧ j ≤ n + 1 := by omega
      simp only [extendedOldCoefficient, if_pos hb, if_neg hz]
  rw [h]
  exact sum_lower_zero_extension n (fun j => weightedLocalCoefficient n j s P)

theorem sum_extendedRemainderCoefficient (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedRemainderCoefficient n j s q) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q := by
  simpa only [Nat.add_assoc, Nat.reduceAdd, extendedRemainderCoefficient] using
    sum_upper_zero_extension (n + 1) (fun j => remainderCoefficient n j s q)

theorem sum_previousRemainderCoefficient (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), previousRemainderCoefficient n j s q) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q := by
  have h : (∑ j ∈ range (n + 3), previousRemainderCoefficient n j s q) =
      ∑ j ∈ range (n + 3), if j = 0 then 0 else remainderCoefficient n (j - 1) s q := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases hz : j = 0
    · simp only [previousRemainderCoefficient, if_pos hz]
    · have hp : j - 1 ≤ n + 1 := by omega
      simp only [previousRemainderCoefficient, if_neg hz,
        extendedRemainderCoefficient, if_pos hp]
  rw [h]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    sum_lower_zero_extension (n + 1) (fun j => remainderCoefficient n j s q)

/-- Every actual rho order is transported by finite cancellation, with no parity premise. -/
theorem actual_chosen_all_rho_transport (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    CoefficientMapFiniteSum.rho (n + 2) s (X ^ r.val) =
      CoefficientMapFiniteSum.rho n s (connectionP n r) := by
  change (∑ j ∈ range (n + 2 + 1), weightedLocalCoefficient (n + 2) j s (X ^ r.val)) = _
  have h : (∑ j ∈ range (n + 3), weightedLocalCoefficient (n + 2) j s (X ^ r.val)) =
      ∑ j ∈ range (n + 3),
        (extendedOldCoefficient n j s (connectionP n r) +
          extendedRemainderCoefficient n j s (connectionQ n r) -
          previousRemainderCoefficient n j s (connectionQ n r)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact actual_chosen_all_local_coefficients_transport n hn r j s (by omega) hs1 hs9
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_extendedOldCoefficient, sum_extendedRemainderCoefficient,
    sum_previousRemainderCoefficient]
  ring

end ZetaNine.CoefficientMapFormalTransportJets
