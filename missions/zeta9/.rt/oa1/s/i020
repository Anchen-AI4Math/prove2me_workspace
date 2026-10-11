import missions.zeta9.formalization.CoefficientMapFormalTransportJets
import missions.zeta9.formalization.CoefficientMapMatrix

/-!
UNCOMPILED PURE CANDIDATE: genuine finite B and all five formal outputs.
The private source-only preparation imports the actually compiled Jets export
ccef5eaf...4c02, not the unchanged shared initial Jets candidate b081ed2a...00d.
No coefficient transport, PF existence, zeta independence, matrix invertibility,
or infinite-summation identity is supplied as a premise. All identities are
finite rational identities of the genuine chosen Connection pair.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFormalTransportOutputs

open HarmonicStability CoefficientMap CoefficientMapJet CoefficientMapInjectivity
open CoefficientMapPartialFractions CoefficientMapNumeratorPartialFractions
open CoefficientMapFiniteSum CoefficientMapAggregate CoefficientMapMatrix
open CoefficientMapFormalTransportData CoefficientMapFormalTransportBounds
open CoefficientMapFormalTransportJets

theorem weightedR_eval_one_zero (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) :
    weightedR n W 1 = 0 := by
  have hprod : (∏ i ∈ range n, ((1 : ℚ) - ((i : ℚ) + 1))) = 0 := by
    apply Finset.prod_eq_zero (show 0 ∈ range n from mem_range.mpr (by omega))
    norm_num
  simp only [weightedR, actualR, numerator, hprod, mul_zero, zero_mul, zero_div]

theorem quartic_properMultiplier (n : ℕ) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    ProperMultiplier n W := by
  unfold ProperMultiplier
  omega

theorem weighted_boundary_sum_zero (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      weightedLocalCoefficient n j s W / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 := by
  have hregular : ∀ k ≤ n, (1 : ℚ) + (k : ℚ) ≠ 0 := by
    intro k hk
    positivity
  have h := actual_global_partial_fractions n W (quartic_properMultiplier n W hW) 1 hregular
  rw [weightedR_eval_one_zero n hn W] at h
  simpa only [Nat.cast_add, Nat.cast_one, add_comm] using h.symm

theorem remainder_boundary_sum_zero (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X])
    (hq : q.natDegree ≤ 9) :
    (∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
      remainderCoefficient n j s q / (((j + 1 : ℕ) : ℚ) ^ s)) = 0 := by
  have hproper : (shiftedRemainderNumerator n q).natDegree < 9 * (n + 1 + 1) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      shiftedRemainderNumerator_strict_proper n hn q hq
  have hregular : ∀ k ≤ n + 1, (1 : ℚ) + (k : ℚ) ≠ 0 := by
    intro k hk
    positivity
  have h := actual_numerator_global_partial_fractions (n + 1)
    (shiftedRemainderNumerator n q) hproper 1 hregular
  rw [shiftedRemainderNumerator_eval_one n hn q, zero_div] at h
  simpa only [remainderCoefficient, Nat.add_assoc, Nat.reduceAdd,
    Nat.cast_add, Nat.cast_one, add_comm] using h.symm

theorem sum_extendedOldCoefficient_harmonic (n s : ℕ) (P : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedOldCoefficient n j s P * harmonicPower s j) =
      ∑ j ∈ range (n + 1), weightedLocalCoefficient n j s P * harmonicPower s (j + 1) := by
  rw [Finset.sum_range_succ]
  have hlast : extendedOldCoefficient n (n + 2) s P = 0 := by
    rw [extendedOldCoefficient, if_neg (by omega : ¬ (1 ≤ n + 2 ∧ n + 2 ≤ n + 1))]
  rw [hlast, zero_mul, add_zero]
  have h : (∑ j ∈ range (n + 2), extendedOldCoefficient n j s P * harmonicPower s j) =
      ∑ j ∈ range (n + 2), if j = 0 then 0 else
        weightedLocalCoefficient n (j - 1) s P * harmonicPower s ((j - 1) + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases hz : j = 0
    · simp [extendedOldCoefficient, hz]
    · have hb : 1 ≤ j ∧ j ≤ n + 1 := by omega
      have hs : j - 1 + 1 = j := by omega
      simp only [extendedOldCoefficient, if_pos hb, if_neg hz, hs]
  rw [h]
  exact sum_lower_zero_extension n
    (fun j => weightedLocalCoefficient n j s P * harmonicPower s (j + 1))

theorem sum_extendedRemainderCoefficient_harmonic (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedRemainderCoefficient n j s q * harmonicPower s j) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q * harmonicPower s j := by
  have h : (∑ j ∈ range (n + 3), extendedRemainderCoefficient n j s q * harmonicPower s j) =
      ∑ j ∈ range (n + 3), if j ≤ n + 1 then
        remainderCoefficient n j s q * harmonicPower s j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hle : j ≤ n + 1
    · simp only [extendedRemainderCoefficient, if_pos hle]
    · simp only [extendedRemainderCoefficient, if_neg hle, zero_mul]
  rw [h]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    sum_upper_zero_extension (n + 1)
      (fun j => remainderCoefficient n j s q * harmonicPower s j)

theorem sum_previousRemainderCoefficient_harmonic (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), previousRemainderCoefficient n j s q * harmonicPower s j) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q * harmonicPower s (j + 1) := by
  have h : (∑ j ∈ range (n + 3), previousRemainderCoefficient n j s q * harmonicPower s j) =
      ∑ j ∈ range (n + 3), if j = 0 then 0 else
        remainderCoefficient n (j - 1) s q * harmonicPower s ((j - 1) + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases hz : j = 0
    · simp only [previousRemainderCoefficient, if_pos hz, zero_mul]
    · have hp : j - 1 ≤ n + 1 := by omega
      have hs : j - 1 + 1 = j := by omega
      simp only [previousRemainderCoefficient, if_neg hz,
        extendedRemainderCoefficient, if_pos hp, hs]
  rw [h]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    sum_lower_zero_extension (n + 1)
      (fun j => remainderCoefficient n j s q * harmonicPower s (j + 1))

theorem sum_harmonic_succ (N s : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range N, f j * harmonicPower s (j + 1)) =
      (∑ j ∈ range N, f j * harmonicPower s j) +
        ∑ j ∈ range N, f j / (((j + 1 : ℕ) : ℚ) ^ s) := by
  simp only [harmonicPower_succ, mul_add, mul_one_div, Finset.sum_add_distrib]

theorem actual_chosen_harmonic_order_transport (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    (∑ j ∈ range (n + 3), weightedLocalCoefficient (n + 2) j s (X ^ r.val) * harmonicPower s j) =
      (∑ j ∈ range (n + 1), weightedLocalCoefficient n j s (connectionP n r) * harmonicPower s j) +
      (∑ j ∈ range (n + 1), weightedLocalCoefficient n j s (connectionP n r) /
        (((j + 1 : ℕ) : ℚ) ^ s)) -
      (∑ j ∈ range (n + 2), remainderCoefficient n j s (connectionQ n r) /
        (((j + 1 : ℕ) : ℚ) ^ s)) := by
  have h : (∑ j ∈ range (n + 3), weightedLocalCoefficient (n + 2) j s (X ^ r.val) * harmonicPower s j) =
      ∑ j ∈ range (n + 3),
        (extendedOldCoefficient n j s (connectionP n r) +
          extendedRemainderCoefficient n j s (connectionQ n r) -
          previousRemainderCoefficient n j s (connectionQ n r)) * harmonicPower s j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [actual_chosen_all_local_coefficients_transport n hn r j s (by omega) hs1 hs9]
  rw [h]
  simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_extendedOldCoefficient_harmonic, sum_extendedRemainderCoefficient_harmonic,
    sum_previousRemainderCoefficient_harmonic,
    sum_harmonic_succ (n + 1) s (fun j => weightedLocalCoefficient n j s (connectionP n r)),
    sum_harmonic_succ (n + 2) s (fun j => remainderCoefficient n j s (connectionQ n r))]
  ring

theorem actual_chosen_constantTerm_correction (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r) -
      (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n j s (connectionP n r) / (((j + 1 : ℕ) : ℚ) ^ s)) +
      (∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
        remainderCoefficient n j s (connectionQ n r) / (((j + 1 : ℕ) : ℚ) ^ s)) := by
  have hOld : (∑ s ∈ Icc 1 9, ∑ j ∈ range (n + 1),
      weightedLocalCoefficient n j s (connectionP n r) * harmonicPower s j) =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n j s (connectionP n r) * harmonicPower s j := Finset.sum_comm
  have hOldPF : (∑ s ∈ Icc 1 9, ∑ j ∈ range (n + 1),
      weightedLocalCoefficient n j s (connectionP n r) / (((j + 1 : ℕ) : ℚ) ^ s)) =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n j s (connectionP n r) / (((j + 1 : ℕ) : ℚ) ^ s) := Finset.sum_comm
  have hQPF : (∑ s ∈ Icc 1 9, ∑ j ∈ range (n + 2),
      remainderCoefficient n j s (connectionQ n r) / (((j + 1 : ℕ) : ℚ) ^ s)) =
      ∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
        remainderCoefficient n j s (connectionQ n r) / (((j + 1 : ℕ) : ℚ) ^ s) := Finset.sum_comm
  have htotal : (∑ j ∈ range (n + 3), ∑ s ∈ Icc 1 9,
      weightedLocalCoefficient (n + 2) j s (X ^ r.val) * harmonicPower s j) =
      (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n j s (connectionP n r) * harmonicPower s j) +
      (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n j s (connectionP n r) / (((j + 1 : ℕ) : ℚ) ^ s)) -
      (∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
        remainderCoefficient n j s (connectionQ n r) / (((j + 1 : ℕ) : ℚ) ^ s)) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ s ∈ Icc 1 9,
          ((∑ j ∈ range (n + 1), weightedLocalCoefficient n j s (connectionP n r) * harmonicPower s j) +
          (∑ j ∈ range (n + 1), weightedLocalCoefficient n j s (connectionP n r) /
            (((j + 1 : ℕ) : ℚ) ^ s)) -
          (∑ j ∈ range (n + 2), remainderCoefficient n j s (connectionQ n r) /
            (((j + 1 : ℕ) : ℚ) ^ s))) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact actual_chosen_harmonic_order_transport n hn r s
          (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hOld, hOldPF, hQPF]
  unfold constantTerm
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [htotal]
  ring

theorem actual_chosen_constantTerm_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r) := by
  rw [actual_chosen_constantTerm_correction n hn r,
    weighted_boundary_sum_zero n hn (connectionP n r) (connectionP_natDegree_le n hn r),
    remainder_boundary_sum_zero n hn (connectionQ n r) (connectionQ_natDegree_le n hn r),
    sub_zero, add_zero]

theorem actual_chosen_five_output_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    aggregate (n + 2) (X ^ r.val) = aggregate n (connectionP n r) := by
  funext i
  fin_cases i
  · simpa only [aggregate] using actual_chosen_constantTerm_transport n hn r
  · simpa only [aggregate] using actual_chosen_all_rho_transport n hn r 3 (by decide) (by decide)
  · simpa only [aggregate] using actual_chosen_all_rho_transport n hn r 5 (by decide) (by decide)
  · simpa only [aggregate] using actual_chosen_all_rho_transport n hn r 7 (by decide) (by decide)
  · simpa only [aggregate] using actual_chosen_all_rho_transport n hn r 9 (by decide) (by decide)

theorem actual_chosen_Gamma_row_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    aggregate n (connectionP n r) = connectionGamma n r ᵥ* actualFMatrix n := by
  have h := quarticAggregate_eq_row_vector n (connectionGamma n r)
  rw [quartic_aggregate_is_actual, connectionGamma_restores_P n hn r] at h
  exact h

theorem actual_five_output_matrix_transport (n : ℕ) (hn : 1 ≤ n) :
    actualFMatrix (n + 2) = connectionGamma n * actualFMatrix n := by
  ext r i
  change aggregate (n + 2) (X ^ r.val) i = (connectionGamma n r ᵥ* actualFMatrix n) i
  exact congrFun ((actual_chosen_five_output_transport n hn r).trans
    (actual_chosen_Gamma_row_transport n hn r)) i

theorem n_one_five_output_transport (r : Fin 5) :
    aggregate 3 (X ^ r.val) = aggregate 1 (connectionP 1 r) :=
  actual_chosen_five_output_transport 1 (by decide) r

theorem n_one_matrix_transport :
    actualFMatrix 3 = connectionGamma 1 * actualFMatrix 1 :=
  actual_five_output_matrix_transport 1 (by decide)

end ZetaNine.CoefficientMapFormalTransportOutputs
