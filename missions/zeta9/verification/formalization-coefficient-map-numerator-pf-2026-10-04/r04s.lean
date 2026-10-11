import missions.zeta9.formalization.CoefficientMapFormalTransportData
import missions.zeta9.formalization.CoefficientMapPartialFractions

/-!
OFFLINE, UNCOMPILED CANDIDATE. No Lean invocation has validated this file.

Fixed-nine partial fractions for an arbitrary actual rational polynomial
numerator. The coefficients are exactly FormalTransportData's cleared
formal-series jets. Strict properness is a degree condition on this A;
no partial-fraction existence or abstract coefficient array is assumed.

The truncation, coprimality and pole-degree tools come from the already
proved special-numerator PF modules. This adds their numerator-independent
argument without changing any frozen source. It does not prove transport,
integer heights, a zeta-independence assertion or irrationality.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapNumeratorPartialFractions

open CoefficientMapInjectivity CoefficientMapPartialFractions
open CoefficientMapFormalTransportData

def numeratorLocalTruncation (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc 9 (numeratorClearedSeries m j A)

def numeratorPartialBlock (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  clearedPolePolynomial m j ^ 9 *
    (numeratorLocalTruncation m j A).comp (X + C (j : ℚ))

def numeratorPartialNumerator (m : ℕ) (A : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
    C (numeratorLocalCoefficient m j s A) *
      clearedPolePolynomial m j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)

def numeratorCandidateClearedSeries (m j : ℕ) (A : ℚ[X]) : PowerSeries ℚ :=
  numeratorClearedSeries m j (numeratorPartialNumerator m A)

theorem numeratorClearedSeries_denominator_identity (m j : ℕ) (A : ℚ[X]) :
    numeratorClearedSeries m j A *
      (CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9 =
        (A.comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) := by
  have h : PowerSeries.constantCoeff
      ((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero m j)
  unfold numeratorClearedSeries
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

theorem numeratorClearedSeries_unique (m j : ℕ) (A : ℚ[X]) (S : PowerSeries ℚ)
    (hS : S * (CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9 =
      (A.comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ)) :
    S = numeratorClearedSeries m j A := by
  have h : PowerSeries.constantCoeff
      ((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero m j)
  have hi := PowerSeries.inv_mul_cancel
    ((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9) h
  calc
    S = S * ((((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹) *
        (CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9) := by
          rw [hi, mul_one]
    _ = (S * (CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9) *
        (((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹) := by ring
    _ = numeratorClearedSeries m j A := by rw [hS]; rfl

theorem numeratorLocalTruncation_comp_eq_sum (m j : ℕ) (A : ℚ[X]) :
    (numeratorLocalTruncation m j A).comp (X + C (j : ℚ)) =
      ∑ s ∈ Icc 1 9, C (numeratorLocalCoefficient m j s A) *
        (X + C (j : ℚ)) ^ (9 - s) := by
  unfold numeratorLocalTruncation Polynomial.comp
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_nbij' (fun k : ℕ => 9 - k) (fun s : ℕ => 9 - s)
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [Finset.mem_Icc]
    omega
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    rw [Finset.mem_range]
    omega
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    omega
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    omega
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : 9 - (9 - k) = k := by omega
    simp only [numeratorLocalCoefficient, he]

theorem numeratorPartialNumerator_eq_sum_blocks (m : ℕ) (A : ℚ[X]) :
    numeratorPartialNumerator m A = ∑ j ∈ range (m + 1), numeratorPartialBlock m j A := by
  unfold numeratorPartialNumerator numeratorPartialBlock
  apply Finset.sum_congr rfl
  intro j hj
  rw [numeratorLocalTruncation_comp_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem numeratorPartialBlock_comp_own_shift (m j : ℕ) (A : ℚ[X]) :
    (numeratorPartialBlock m j A).comp (CoefficientMapJet.shiftedVariable j) =
      CoefficientMapJet.shiftedClearedDenominator m j ^ 9 * numeratorLocalTruncation m j A := by
  rw [numeratorPartialBlock, Polynomial.mul_comp, Polynomial.pow_comp,
    clearedPolePolynomial_comp_shift]
  simp only [Polynomial.comp_assoc, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, CoefficientMapJet.shiftedVariable,
    sub_add_cancel, Polynomial.comp_X]

theorem numerator_own_block_matches_nine_jets (m j : ℕ) (A : ℚ[X]) :
    (X : ℚ[X]) ^ 9 ∣ A.comp (CoefficientMapJet.shiftedVariable j) -
      (numeratorPartialBlock m j A).comp (CoefficientMapJet.shiftedVariable j) := by
  apply polynomial_X_pow_dvd_of_series
  have h := dvd_mul_of_dvd_left
    (truncation_remainder_X_pow_dvd (numeratorClearedSeries m j A))
    ((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)
  rw [numeratorPartialBlock_comp_own_shift]
  convert h using 1
  rw [sub_mul, numeratorClearedSeries_denominator_identity]
  simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow,
    numeratorLocalTruncation]
  ring

theorem numerator_different_block_pole_divisibility (m i j : ℕ) (A : ℚ[X])
    (hj : j ≤ m) (hji : j ≠ i) :
    (X + C (j : ℚ)) ^ 9 ∣ numeratorPartialBlock m i A := by
  have hjmem : j ∈ (range (m + 1)).erase i := by
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨hji, Nat.lt_succ_of_le hj⟩
  have hbase : X + C (j : ℚ) ∣ clearedPolePolynomial m i :=
    Finset.dvd_prod_of_mem (fun k : ℕ => X + C (k : ℚ)) hjmem
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hbase 9) _

theorem numerator_different_block_shift_X_pow_dvd (m i j : ℕ) (A : ℚ[X])
    (hj : j ≤ m) (hji : j ≠ i) :
    (X : ℚ[X]) ^ 9 ∣ (numeratorPartialBlock m i A).comp (CoefficientMapJet.shiftedVariable j) := by
  obtain ⟨q, hq⟩ := numerator_different_block_pole_divisibility m i j A hj hji
  refine ⟨q.comp (CoefficientMapJet.shiftedVariable j), ?_⟩
  have he := congrArg (fun p : ℚ[X] => p.comp (CoefficientMapJet.shiftedVariable j)) hq
  simpa only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, CoefficientMapJet.shiftedVariable,
    sub_add_cancel] using he

theorem numerator_full_candidate_matches_nine_jets (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    (X : ℚ[X]) ^ 9 ∣
      (A - numeratorPartialNumerator m A).comp (CoefficientMapJet.shiftedVariable j) := by
  have hjmem : j ∈ range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hsplit : (numeratorPartialNumerator m A).comp (CoefficientMapJet.shiftedVariable j) =
      (numeratorPartialBlock m j A).comp (CoefficientMapJet.shiftedVariable j) +
        ∑ i ∈ (range (m + 1)).erase j,
          (numeratorPartialBlock m i A).comp (CoefficientMapJet.shiftedVariable j) := by
    rw [numeratorPartialNumerator_eq_sum_blocks, Polynomial.sum_comp]
    exact (Finset.add_sum_erase (range (m + 1))
      (fun i => (numeratorPartialBlock m i A).comp (CoefficientMapJet.shiftedVariable j)) hjmem).symm
  have hoff : (X : ℚ[X]) ^ 9 ∣ ∑ i ∈ (range (m + 1)).erase j,
      (numeratorPartialBlock m i A).comp (CoefficientMapJet.shiftedVariable j) := by
    apply Finset.dvd_sum
    intro i hi
    exact numerator_different_block_shift_X_pow_dvd m i j A hj (Finset.ne_of_mem_erase hi).symm
  rw [Polynomial.sub_comp, hsplit, sub_add_eq_sub_sub]
  exact dvd_sub (numerator_own_block_matches_nine_jets m j A) hoff

theorem numerator_denominator_divides_actual_candidate_difference (m : ℕ) (A : ℚ[X]) :
    polePolynomial m ^ 9 ∣ A - numeratorPartialNumerator m A := by
  unfold polePolynomial
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact pole_factors_coprime a b hab
  · intro j hj
    apply shifted_divisibility_implies_pole_divisibility
    exact numerator_full_candidate_matches_nine_jets m j A
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem numeratorCandidateClearedSeries_denominator_identity (m j : ℕ) (A : ℚ[X]) :
    numeratorCandidateClearedSeries m j A *
      (CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9 =
        ((numeratorPartialNumerator m A).comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) := by
  exact numeratorClearedSeries_denominator_identity m j (numeratorPartialNumerator m A)

theorem numerator_candidate_first_nine_coefficients (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m)
    (k : ℕ) (hk : k < 9) :
    PowerSeries.coeff k (numeratorCandidateClearedSeries m j A) =
      PowerSeries.coeff k (numeratorClearedSeries m j A) := by
  obtain ⟨q, hq⟩ := numerator_full_candidate_matches_nine_jets m j A hj
  have hs : (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣
      ((A - numeratorPartialNumerator m A).comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) := by
    refine ⟨(q : PowerSeries ℚ), ?_⟩
    have he := congrArg (fun p : ℚ[X] => (p : PowerSeries ℚ)) hq
    simpa only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X] using he
  have hm := dvd_mul_of_dvd_left hs
    (((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹)
  have he : (((A - numeratorPartialNumerator m A).comp
      (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) *
        ((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹) =
      numeratorClearedSeries m j A - numeratorCandidateClearedSeries m j A := by
    rw [Polynomial.sub_comp, Polynomial.coe_sub, sub_mul]
    rfl
  rw [he] at hm
  have hz := PowerSeries.X_pow_dvd_iff.mp hm k hk
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

theorem numerator_candidate_local_coefficients (m j s : ℕ) (A : ℚ[X]) (hj : j ≤ m)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    PowerSeries.coeff (9 - s) (numeratorCandidateClearedSeries m j A) =
      numeratorLocalCoefficient m j s A := by
  exact numerator_candidate_first_nine_coefficients m j A hj (9 - s) (by omega)

theorem numeratorLocalTruncation_natDegree_le (m j : ℕ) (A : ℚ[X]) :
    (numeratorLocalTruncation m j A).natDegree ≤ 8 := by
  have h := PowerSeries.natDegree_trunc_lt (numeratorClearedSeries m j A) 8
  exact Nat.le_of_lt_succ h

theorem numeratorPartialBlock_natDegree_le (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    (numeratorPartialBlock m j A).natDegree ≤ 9 * m + 8 := by
  have hm := Polynomial.natDegree_mul_le (p := clearedPolePolynomial m j ^ 9)
    (q := (numeratorLocalTruncation m j A).comp (X + C (j : ℚ)))
  have hc := Polynomial.natDegree_comp_le
    (p := numeratorLocalTruncation m j A) (q := X + C (j : ℚ))
  rw [Polynomial.natDegree_X_add_C, mul_one] at hc
  rw [Polynomial.natDegree_pow, clearedPolePolynomial_natDegree m j hj] at hm
  have ht := numeratorLocalTruncation_natDegree_le m j A
  unfold numeratorPartialBlock
  omega

theorem numeratorPartialNumerator_natDegree_le (m : ℕ) (A : ℚ[X]) :
    (numeratorPartialNumerator m A).natDegree ≤ 9 * m + 8 := by
  rw [numeratorPartialNumerator_eq_sum_blocks]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact numeratorPartialBlock_natDegree_le m j A
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem actual_numerator_polynomial_partial_fractions (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) : A = numeratorPartialNumerator m A := by
  have hdvd := numerator_denominator_divides_actual_candidate_difference m A
  have hzero : A - numeratorPartialNumerator m A = 0 := by
    by_contra hne
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [polePolynomial_pow_natDegree] at hdeg
    have hp := numeratorPartialNumerator_natDegree_le m A
    have hdiff := Polynomial.natDegree_sub_le A (numeratorPartialNumerator m A)
    rcases le_total A.natDegree (numeratorPartialNumerator m A).natDegree with h | h
    · rw [max_eq_right h] at hdiff
      omega
    · rw [max_eq_left h] at hdiff
      omega
  exact sub_eq_zero.mp hzero

theorem numerator_partial_term_division (m j s : ℕ) (A : ℚ[X]) (t : ℚ) (hj : j ≤ m)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hregular : ∀ k ≤ m, t + (k : ℚ) ≠ 0) :
    (numeratorLocalCoefficient m j s A * (clearedPolePolynomial m j).eval t ^ 9 *
      (t + (j : ℚ)) ^ (9 - s)) / (polePolynomial m).eval t ^ 9 =
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s := by
  apply (div_eq_div_iff (pow_ne_zero _ (polePolynomial_eval_ne_zero m t hregular))
    (pow_ne_zero _ (hregular j hj))).mpr
  rw [polePolynomial_eval_factor m j t hj, mul_pow]
  have he : (t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s = (t + (j : ℚ)) ^ 9 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = numeratorLocalCoefficient m j s A * (clearedPolePolynomial m j).eval t ^ 9 *
        ((t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s) := by ring
    _ = _ := by rw [he]; ring

theorem actual_numerator_global_partial_fractions (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) (t : ℚ)
    (hregular : ∀ k ≤ m, t + (k : ℚ) ≠ 0) :
    A.eval t / (polePolynomial m).eval t ^ 9 =
      ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s := by
  conv_lhs => rw [actual_numerator_polynomial_partial_fractions m A hproper]
  simp only [numeratorPartialNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  exact numerator_partial_term_division m j s A t
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2 hregular

theorem numerator_local_coefficient_weighted_agreement (m j s : ℕ) (W : ℚ[X]) :
    numeratorLocalCoefficient m j s (weightedNumerator m W) =
      CoefficientMapJet.weightedLocalCoefficient m j s W := by
  unfold numeratorLocalCoefficient numeratorClearedSeries
  rw [← actual_series_from_shifted_numerator]
  rfl

theorem numeratorLocalCoefficient_sub (m j s : ℕ) (A B : ℚ[X]) :
    numeratorLocalCoefficient m j s (A - B) =
      numeratorLocalCoefficient m j s A - numeratorLocalCoefficient m j s B := by
  simp only [numeratorLocalCoefficient, numeratorClearedSeries,
    Polynomial.sub_comp, Polynomial.coe_sub, sub_mul, map_sub]

theorem actual_numerator_all_local_coefficients_zero_implies_zero (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1))
    (hzero : ∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 → numeratorLocalCoefficient m j s A = 0) :
    A = 0 := by
  have hp : numeratorPartialNumerator m A = 0 := by
    unfold numeratorPartialNumerator
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro s hs
    rw [hzero j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) s
      (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2]
    simp
  exact (actual_numerator_polynomial_partial_fractions m A hproper).trans hp

theorem actual_numerator_local_coefficients_injective (m : ℕ) (A B : ℚ[X])
    (hA : A.natDegree < 9 * (m + 1)) (hB : B.natDegree < 9 * (m + 1))
    (heq : ∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) : A = B := by
  have hdiff : (A - B).natDegree < 9 * (m + 1) := by
    have hdeg := Polynomial.natDegree_sub_le A B
    rcases le_total A.natDegree B.natDegree with h | h
    · rw [max_eq_right h] at hdeg
      omega
    · rw [max_eq_left h] at hdeg
      omega
  have hzero : ∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s (A - B) = 0 := by
    intro j hj s hs1 hs9
    rw [numeratorLocalCoefficient_sub, heq j hj s hs1 hs9, sub_self]
  exact sub_eq_zero.mp (actual_numerator_all_local_coefficients_zero_implies_zero m (A - B) hdiff hzero)

end ZetaNine.CoefficientMapNumeratorPartialFractions

#print axioms ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_denominator_identity
#print axioms ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_unique
#print axioms ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_own_block_matches_nine_jets
#print axioms ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_denominator_divides_actual_candidate_difference
#print axioms ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_candidate_local_coefficients
#print axioms ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions
#print axioms ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions
#print axioms ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_local_coefficient_weighted_agreement
#print axioms ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_all_local_coefficients_zero_implies_zero
#print axioms ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective
