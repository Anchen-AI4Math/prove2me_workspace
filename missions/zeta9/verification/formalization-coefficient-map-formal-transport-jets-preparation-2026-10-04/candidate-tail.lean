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
  rw [h, sum_lower_zero_extension]
  rfl

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
