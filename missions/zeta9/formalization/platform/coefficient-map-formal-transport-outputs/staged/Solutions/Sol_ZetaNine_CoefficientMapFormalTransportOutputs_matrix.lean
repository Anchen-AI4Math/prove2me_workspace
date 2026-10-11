import Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs
import Mathlib


/- SOURCE module missions.zeta9.formalization.CoefficientMap; full proof bodies preserved. -/

/-!
Finite entry to route Z9.F, specialized to p = 9, q = 1, m = n.
The rational expression is defined by its actual numerator and pole product.
The cleared expression agrees with (t+j)^9 R_n(t) at every regular point,
has nonzero denominator at -j, and its value there is computed from the
products. No coefficient closed formula is used as its definition.

This file does not establish lower partial fractions, the full formal map,
invertibility, the exact infinite sum, or irrationality.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Finset
open Polynomial

namespace ZetaNine.CoefficientMap

theorem poleProduct_factor (n j : ℕ) (hj : j ≤ n) (t : ℚ) :
    poleProduct n t = (t + j) * clearedPoleProduct n j t := by
  exact (Finset.mul_prod_erase (range (n + 1)) (fun k => t + (k : ℚ))
    (by simpa using Nat.lt_succ_iff.mpr hj)).symm

theorem poleProduct_ne_zero (n : ℕ) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) : poleProduct n t ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact ht k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem clearedPoleProduct_ne_zero (n j : ℕ) :
    clearedPoleProduct n j (-(j : ℚ)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  intro hz
  have he : (k : ℚ) = (j : ℚ) := by linarith
  exact hkj (Nat.cast_inj.mp he)

theorem clear_highest_pole (n j : ℕ) (hj : j ≤ n) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    actualR n t * (t + j) ^ 9 = clearedR n j t := by
  have hfactor := ht j hj
  have hclear : clearedPoleProduct n j t ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact ht k (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_erase.mp hk).2))
  unfold actualR clearedR
  rw [poleProduct_factor n j hj t, mul_pow]
  field_simp

theorem clear_weighted_highest_pole (n j : ℕ) (hj : j ≤ n)
    (W : ℚ[X]) (t : ℚ) (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    weightedR n W t * (t + j) ^ 9 = clearedWeightedR n j W t := by
  unfold weightedR clearedWeightedR
  rw [mul_right_comm, clear_highest_pole n j hj t ht]

theorem rising_product (a n : ℕ) :
    (∏ i ∈ range n, ((a : ℚ) + ((i : ℚ) + 1))) =
      (n.factorial : ℚ) * ((a + n).choose n : ℚ) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose a n
  rw [Nat.ascFactorial_eq_prod_range] at h
  have hc := congrArg (fun x : ℕ => (x : ℚ)) h
  simp only [Nat.cast_prod, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hc
  calc
    _ = ∏ i ∈ range n, ((a : ℚ) + 1 + i) := by
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ = _ := hc

theorem falling_product (n : ℕ) :
    (∏ k ∈ range n, ((k : ℚ) - n)) =
      (-1 : ℚ) ^ n * (n.factorial : ℚ) := by
  calc
    (∏ k ∈ range n, ((k : ℚ) - n)) =
        ∏ k ∈ range n, (-((n : ℚ) - k)) := by
      apply Finset.prod_congr rfl
      intro k hk
      ring
    _ = (-1 : ℚ) ^ n * (∏ k ∈ range n, ((n : ℚ) - k)) := by
      rw [Finset.prod_neg, Finset.card_range]
    _ = (-1 : ℚ) ^ n * (n.factorial : ℚ) := by
      rw [Finset.prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range,
        Nat.descFactorial_self]

theorem clearedPoleProduct_eval (n j : ℕ) (hj : j ≤ n) :
    clearedPoleProduct n j (-(j : ℚ)) =
      (-1 : ℚ) ^ j * (j.factorial : ℚ) * ((n - j).factorial : ℚ) := by
  induction n with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp [clearedPoleProduct]
  | succ n ih =>
    by_cases hlast : j = n + 1
    · subst j
      rw [clearedPoleProduct, Finset.range_add_one, Finset.erase_insert (by simp)]
      have hprod := falling_product (n + 1)
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one]
      convert hprod using 1
      apply Finset.prod_congr rfl
      intro k hk
      ring
    · have hjn : j ≤ n := by omega
      have hnmem : n + 1 ∉ (range (n + 1)).erase j := by simp
      unfold clearedPoleProduct
      rw [Finset.range_add_one, Finset.erase_insert_of_ne (Ne.symm hlast), Finset.prod_insert hnmem]
      change (-(j : ℚ) + (n + 1 : ℕ)) * clearedPoleProduct n j (-(j : ℚ)) = _
      rw [ih hjn]
      have hsub : n + 1 - j = (n - j) + 1 := by omega
      rw [hsub, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hcast : ((n - j : ℕ) : ℚ) = (n : ℚ) - j := Nat.cast_sub hjn
      simp only [Nat.cast_add, Nat.cast_one, hcast]
      ring

theorem numerator_eval (n j : ℕ) (hj : j ≤ n) :
    numerator n (-(j : ℚ)) =
      (-1 : ℚ) ^ n * (n.factorial : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := by
  have hleft : (∏ i ∈ range n, (-(j : ℚ) - ((i : ℚ) + 1))) =
      (-1 : ℚ) ^ n * (n.factorial : ℚ) * ((n + j).choose n : ℚ) := by
    calc
      _ = ∏ i ∈ range n, (-((j : ℚ) + ((i : ℚ) + 1))) := by
        apply Finset.prod_congr rfl
        intro i hi
        ring
      _ = (-1 : ℚ) ^ n * (n.factorial : ℚ) * ((n + j).choose n : ℚ) := by
        rw [Finset.prod_neg, Finset.card_range, rising_product, Nat.add_comm j n]
        ring
  have hright : (∏ i ∈ range n, (-(j : ℚ) + n + ((i : ℚ) + 1))) =
      (n.factorial : ℚ) * ((2 * n - j).choose n : ℚ) := by
    have hsum : n - j + n = 2 * n - j := by omega
    rw [← hsum, ← rising_product (n - j) n]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub hj]
    ring
  unfold numerator
  rw [hleft, hright]
  ring

theorem leadingPoleCoefficient_eq (n j : ℕ) (hj : j ≤ n) :
    leadingPoleCoefficient n j =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := by
  unfold leadingPoleCoefficient clearedR
  rw [numerator_eval n j hj, clearedPoleProduct_eval n j hj, Nat.cast_choose ℚ hj,
    pow_add]
  have hjfac : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hdfac : ((n - j).factorial : ℚ) ≠ 0 := by exact_mod_cast (n - j).factorial_ne_zero
  rcases Nat.even_or_odd j with h | h
  · rw [h.neg_one_pow]
    field_simp
  · rw [h.neg_one_pow]
    field_simp

theorem leadingPoleCoefficient_eq_even (n j : ℕ) (hn : Even n) (hj : j ≤ n) :
    leadingPoleCoefficient n j =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := by
  rw [leadingPoleCoefficient_eq n j hj, pow_add, hn.neg_one_pow, one_mul]

theorem leadingPoleCoefficient_ne_zero (n j : ℕ) (hj : j ≤ n) :
    leadingPoleCoefficient n j ≠ 0 := by
  rw [leadingPoleCoefficient_eq n j hj]
  have h1 : 0 < n.choose j := Nat.choose_pos hj
  have h2 : 0 < (n + j).choose n := Nat.choose_pos (by omega)
  have h3 : 0 < (2 * n - j).choose n := Nat.choose_pos (by omega)
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by exact_mod_cast h1.ne'))
    · exact_mod_cast h2.ne'
  · exact_mod_cast h3.ne'

theorem leadingPoleCoefficient_is_integer (n j : ℕ) (hj : j ≤ n) :
    ∃ z : ℤ, leadingPoleCoefficient n j = (z : ℚ) := by
  refine ⟨(-1 : ℤ) ^ (n + j) * (n.choose j : ℤ) ^ 9 *
    ((n + j).choose n : ℤ) * ((2 * n - j).choose n : ℤ), ?_⟩
  rw [leadingPoleCoefficient_eq n j hj]
  push_cast
  rfl

theorem signed_leadingPoleCoefficient_pos_even (n j : ℕ) (hn : Even n) (hj : j ≤ n) :
    (-1 : ℚ) ^ j * leadingPoleCoefficient n j > 0 := by
  have hs : ((-1 : ℚ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
    norm_num
  have h1 : 0 < n.choose j := Nat.choose_pos hj
  have h2 : 0 < (n + j).choose n := Nat.choose_pos (by omega)
  have h3 : 0 < (2 * n - j).choose n := Nat.choose_pos (by omega)
  rw [leadingPoleCoefficient_eq_even n j hn hj]
  have he : (-1 : ℚ) ^ j * ((-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
      ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ)) =
      ((-1 : ℚ) ^ j) ^ 2 * ((n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ)) := by ring
  rw [he, hs, one_mul]
  positivity

theorem local_coordinate_identity (n j : ℕ) (hj : j ≤ n) (z : ℚ) :
    (-(j : ℚ) + z) * (-(j : ℚ) + z + n) =
      -(j : ℚ) * (n - j : ℕ) + ((n : ℚ) - 2 * j) * z + z ^ 2 := by
  rw [Nat.cast_sub hj]
  ring

theorem clearedWeightedR_local_coordinate (n j : ℕ) (hj : j ≤ n)
    (W : ℚ[X]) (z : ℚ) :
    clearedWeightedR n j W (-(j : ℚ) + z) =
      clearedR n j (-(j : ℚ) + z) *
        W.eval (-(j : ℚ) * (n - j : ℕ) + ((n : ℚ) - 2 * j) * z + z ^ 2) := by
  unfold clearedWeightedR
  rw [local_coordinate_identity n j hj z]

theorem weightedLeadingPoleCoefficient_eq (n j : ℕ) (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := by
  unfold weightedLeadingPoleCoefficient clearedWeightedR
  change leadingPoleCoefficient n j * W.eval (-(j : ℚ) * (-(j : ℚ) + n)) = _
  rw [leadingPoleCoefficient_eq n j hj, Nat.cast_sub hj]
  congr 2
  ring

theorem weightedLeadingPoleCoefficient_eq_even (n j : ℕ) (hn : Even n)
    (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := by
  rw [weightedLeadingPoleCoefficient_eq n j hj W, pow_add, hn.neg_one_pow, one_mul]

end ZetaNine.CoefficientMap

/- SOURCE module missions.zeta9.formalization.CoefficientMapJet; full proof bodies preserved. -/

/-!
Actual local formal jets of the p=9, q=1, m=n rational function.
The coefficients are extracted from the genuine shifted numerator divided
by the genuine cleared denominator, in formal power series with nonzero
constant denominator. They are not abstract coefficient inputs.

This proves the all-order local multiplier convolution, not a global
partial-fraction decomposition, the full five-dimensional map or its inverse.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapJet


theorem shiftedVariable_eval (j : ℕ) (z : ℚ) :
    (shiftedVariable j).eval z = -(j : ℚ) + z := by
  simp [shiftedVariable]
  ring

theorem shiftedNumerator_eval (n j : ℕ) (z : ℚ) :
    (shiftedNumerator n j).eval z = ZetaNine.CoefficientMap.numerator n (-(j : ℚ) + z) := by
  simp only [shiftedNumerator, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_add, shiftedVariable_eval]
  rfl

theorem shiftedClearedDenominator_eval (n j : ℕ) (z : ℚ) :
    (shiftedClearedDenominator n j).eval z = ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ) + z) := by
  simp only [shiftedClearedDenominator, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_C, shiftedVariable_eval]
  rfl

theorem actual_local_rational_expression (n j : ℕ) (z : ℚ) :
    (shiftedNumerator n j).eval z / (shiftedClearedDenominator n j).eval z ^ 9 =
      ZetaNine.CoefficientMap.clearedR n j (-(j : ℚ) + z) := by
  rw [shiftedNumerator_eval, shiftedClearedDenominator_eval]
  rfl

theorem localU_eval (n j : ℕ) (z : ℚ) :
    (localU n j).eval z = (-(j : ℚ) + z) * (-(j : ℚ) + z + n) := by
  simp [localU, shiftedVariable_eval]

theorem localU_eq (n j : ℕ) (hj : j ≤ n) :
    localU n j = C (-(j : ℚ) * (n - j : ℕ)) +
      C ((n : ℚ) - 2 * j) * X + X ^ 2 := by
  simp only [localU, shiftedVariable, Nat.cast_sub hj, map_mul, map_sub, map_neg, map_ofNat]
  ring

theorem integerLocalU_map (n j : ℕ) (hj : j ≤ n) :
    (integerLocalU n j).map (Int.castRingHom ℚ) = localU n j := by
  rw [localU_eq n j hj]
  simp [integerLocalU, map_ofNat]

theorem actual_weighted_local_rational_expression (n j : ℕ) (W : ℚ[X]) (z : ℚ) :
    (shiftedNumerator n j * W.comp (localU n j)).eval z /
        (shiftedClearedDenominator n j).eval z ^ 9 =
      ZetaNine.CoefficientMap.clearedWeightedR n j W (-(j : ℚ) + z) := by
  rw [Polynomial.eval_mul, Polynomial.eval_comp, shiftedNumerator_eval,
    shiftedClearedDenominator_eval, localU_eval]
  unfold ZetaNine.CoefficientMap.clearedWeightedR ZetaNine.CoefficientMap.clearedR
  simp only [div_eq_mul_inv]
  ring

theorem shiftedClearedDenominator_constant (n j : ℕ) :
    PowerSeries.constantCoeff (shiftedClearedDenominator n j : PowerSeries ℚ) =
      ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ)) := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    shiftedClearedDenominator_eval]
  simp

theorem shiftedClearedDenominator_constant_ne_zero (n j : ℕ) :
    PowerSeries.constantCoeff (shiftedClearedDenominator n j : PowerSeries ℚ) ≠ 0 := by
  rw [shiftedClearedDenominator_constant]
  exact ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero n j

theorem clearedSeries_denominator_identity (n j : ℕ) :
    clearedSeries n j * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      (shiftedNumerator n j : PowerSeries ℚ) := by
  have h : PowerSeries.constantCoeff ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (shiftedClearedDenominator_constant_ne_zero n j)
  unfold clearedSeries
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

theorem clearedSeries_unique (n j : ℕ) (S : PowerSeries ℚ)
    (hS : S * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      (shiftedNumerator n j : PowerSeries ℚ)) : S = clearedSeries n j := by
  have h : PowerSeries.constantCoeff ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (shiftedClearedDenominator_constant_ne_zero n j)
  unfold clearedSeries
  calc
    S = S * ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 *
        ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹) := by
      rw [PowerSeries.mul_inv_cancel _ h, mul_one]
    _ = (S * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) *
        ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹ := (mul_assoc _ _ _).symm
    _ = _ := by rw [hS]

theorem weightedClearedSeries_denominator_identity (n j : ℕ) (W : ℚ[X]) :
    weightedClearedSeries n j W * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      (shiftedNumerator n j * W.comp (localU n j) : ℚ[X]) := by
  unfold weightedClearedSeries
  rw [mul_right_comm, clearedSeries_denominator_identity, Polynomial.coe_mul]

theorem clearedSeries_constant (n j : ℕ) :
    PowerSeries.constantCoeff (clearedSeries n j) = ZetaNine.CoefficientMap.leadingPoleCoefficient n j := by
  simp only [clearedSeries, map_mul, PowerSeries.constantCoeff_inv, map_pow,
    Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    shiftedNumerator_eval, shiftedClearedDenominator_eval, add_zero]
  rfl

theorem localCoefficient_nine (n j : ℕ) :
    localCoefficient n j 9 = ZetaNine.CoefficientMap.leadingPoleCoefficient n j := by
  simp only [localCoefficient, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact clearedSeries_constant n j

theorem weightedLocalCoefficient_nine (n j : ℕ) (W : ℚ[X]) :
    weightedLocalCoefficient n j 9 W = ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient n j W := by
  simp only [weightedLocalCoefficient, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, weightedClearedSeries, map_mul,
    clearedSeries_constant, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp, localU_eval, add_zero]
  rfl

theorem coefficient_convolution (n j s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℚ[X]) :
    weightedLocalCoefficient n j s W =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l * (W.comp (localU n j)).coeff (l - s) := by
  unfold weightedLocalCoefficient weightedClearedSeries
  rw [PowerSeries.coeff_mul]
  simp only [Polynomial.coeff_coe]
  apply Finset.sum_nbij' (fun d : ℕ × ℕ => 9 - d.1) (fun l : ℕ => (9 - l, l - s))
  · intro d hd
    have hd' := Finset.mem_antidiagonal.mp hd
    rw [Finset.mem_Icc]
    omega
  · intro l hl
    have hl' := Finset.mem_Icc.mp hl
    rw [Finset.mem_antidiagonal]
    omega
  · intro d hd
    have hd' := Finset.mem_antidiagonal.mp hd
    apply Prod.ext <;> dsimp <;> omega
  · intro l hl
    have hl' := Finset.mem_Icc.mp hl
    omega
  · intro d hd
    have hd' := Finset.mem_antidiagonal.mp hd
    unfold localCoefficient
    have hfirst : 9 - (9 - d.1) = d.1 := by omega
    have hsecond : 9 - d.1 - s = d.2 := by omega
    rw [hfirst, hsecond]

theorem coefficient_convolution_explicit (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℚ[X]) :
    weightedLocalCoefficient n j s W =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l *
        (W.comp (C (-(j : ℚ) * (n - j : ℕ)) +
          C ((n : ℚ) - 2 * j) * X + X ^ 2)).coeff (l - s) := by
  rw [coefficient_convolution n j s hs1 hs9 W, localU_eq n j hj]

theorem integer_coefficient_convolution (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℤ[X]) :
    weightedLocalCoefficient n j s (W.map (Int.castRingHom ℚ)) =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l *
        ((W.comp (integerLocalU n j)).coeff (l - s) : ℚ) := by
  rw [coefficient_convolution n j s hs1 hs9]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← integerLocalU_map n j hj, ← Polynomial.map_comp]
  simp

end ZetaNine.CoefficientMapJet

/- SOURCE module missions.zeta9.formalization.CoefficientMapInjectivity; full proof bodies preserved. -/

/-!
Injectivity of the complete (n+1) by 9 actual local coefficient array in
the strict proper-degree domain. This is a bridge for route Z9.F, not
injectivity/invertibility of its five aggregated zeta/constant outputs.
The genuine numerator and the frozen formal jets are used throughout.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapInjectivity

theorem baseNumerator_eval (n : ℕ) (t : ℚ) :
    (baseNumerator n).eval t = CoefficientMap.numerator n t := by
  simp only [baseNumerator, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rfl

theorem weightedNumerator_shift (n j : ℕ) (W : ℚ[X]) :
    (weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable j) =
      CoefficientMapJet.shiftedNumerator n j * W.comp (CoefficientMapJet.localU n j) := by
  simp only [weightedNumerator, baseNumerator, baseU, CoefficientMapJet.shiftedNumerator,
    CoefficientMapJet.localU, Polynomial.mul_comp, Polynomial.prod_comp,
    Polynomial.sub_comp, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.comp_assoc]

theorem zero_local_jet_implies_shifted_numerator_divisibility (n j : ℕ) (W : ℚ[X])
    (hzero : ∀ s, 1 ≤ s → s ≤ 9 → CoefficientMapJet.weightedLocalCoefficient n j s W = 0) :
    (X : ℚ[X]) ^ 9 ∣ CoefficientMapJet.shiftedNumerator n j *
      W.comp (CoefficientMapJet.localU n j) := by
  have hseries : (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣
      CoefficientMapJet.weightedClearedSeries n j W := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro k hk
    have h := hzero (9 - k) (by omega) (by omega)
    have hindex : 9 - (9 - k) = k := by omega
    simpa only [CoefficientMapJet.weightedLocalCoefficient, hindex] using h
  have hproduct := dvd_mul_of_dvd_left hseries
    ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)
  rw [CoefficientMapJet.weightedClearedSeries_denominator_identity] at hproduct
  apply Polynomial.X_pow_dvd_iff.mpr
  intro k hk
  have h := PowerSeries.X_pow_dvd_iff.mp hproduct k hk
  simpa only [Polynomial.coeff_coe] using h

theorem zero_local_jet_implies_pole_divisibility (n j : ℕ) (W : ℚ[X])
    (hzero : ∀ s, 1 ≤ s → s ≤ 9 → CoefficientMapJet.weightedLocalCoefficient n j s W = 0) :
    (X + C (j : ℚ)) ^ 9 ∣ weightedNumerator n W := by
  have h := zero_local_jet_implies_shifted_numerator_divisibility n j W hzero
  rw [← weightedNumerator_shift n j W] at h
  obtain ⟨q, hq⟩ := h
  refine ⟨q.comp (X + C (j : ℚ)), ?_⟩
  have he := congrArg (fun p : ℚ[X] => p.comp (X + C (j : ℚ))) hq
  simpa only [Polynomial.comp_assoc, CoefficientMapJet.shiftedVariable,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right,
    Polynomial.comp_X, Polynomial.mul_comp, Polynomial.pow_comp] using he

theorem pole_factors_coprime (a b : ℕ) (hab : a ≠ b) :
    IsCoprime ((X + C (a : ℚ)) ^ 9) ((X + C (b : ℚ)) ^ 9) := by
  have hneq : (-(a : ℚ)) ≠ -(b : ℚ) := by
    intro h
    exact hab (Nat.cast_inj.mp (neg_inj.mp h))
  have hc := Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (sub_ne_zero_of_ne hneq).isUnit
  have hp := hc.pow (m := 9) (n := 9)
  simpa only [map_neg, sub_neg_eq_add] using hp

theorem all_zero_jets_imply_full_denominator_divisibility (n : ℕ) (W : ℚ[X])
    (hzero : AllLocalCoefficientsZero n W) : polePolynomial n ^ 9 ∣ weightedNumerator n W := by
  unfold polePolynomial
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact pole_factors_coprime a b hab
  · intro j hj
    exact zero_local_jet_implies_pole_divisibility n j W
      (hzero j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

theorem polePolynomial_natDegree (n : ℕ) : (polePolynomial n).natDegree = n + 1 := by
  unfold polePolynomial
  rw [Polynomial.natDegree_prod_of_monic (range (n + 1))
    (fun j : ℕ => X + C (j : ℚ)) (fun j hj => Polynomial.monic_X_add_C (j : ℚ))]
  simp only [Polynomial.natDegree_X_add_C]
  simp

theorem polePolynomial_pow_natDegree (n : ℕ) : (polePolynomial n ^ 9).natDegree = 9 * (n + 1) := by
  rw [Polynomial.natDegree_pow, polePolynomial_natDegree]

theorem baseU_natDegree (n : ℕ) : (baseU n).natDegree = 2 := by
  unfold baseU
  rw [Polynomial.natDegree_mul (Polynomial.X_ne_zero) (Polynomial.X_add_C_ne_zero _)]
  simp only [Polynomial.natDegree_X, Polynomial.natDegree_X_add_C]

theorem baseNumerator_ne_zero (n : ℕ) : baseNumerator n ≠ 0 := by
  unfold baseNumerator
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply Polynomial.C_ne_zero.mpr
      apply pow_ne_zero
      exact_mod_cast n.factorial_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact Polynomial.X_sub_C_ne_zero _
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [add_assoc, ← map_add]
    exact Polynomial.X_add_C_ne_zero _

theorem baseNumerator_natDegree_le (n : ℕ) : (baseNumerator n).natDegree ≤ 2 * n := by
  have hL : (∏ i ∈ range n, (X - C ((i : ℚ) + 1))).natDegree ≤ n := by
    calc
      _ ≤ ∑ i ∈ range n, (X - C ((i : ℚ) + 1)).natDegree := Polynomial.natDegree_prod_le _ _
      _ = n := by
        simp only [Polynomial.natDegree_X_sub_C]
        simp
  have hR : (∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1))).natDegree ≤ n := by
    calc
      _ ≤ ∑ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)).natDegree := Polynomial.natDegree_prod_le _ _
      _ = n := by
        simp only [add_assoc, ← map_add, Polynomial.natDegree_X_add_C]
        simp
  have h1 := Polynomial.natDegree_mul_le (p := C ((n.factorial : ℚ) ^ 7))
    (q := ∏ i ∈ range n, (X - C ((i : ℚ) + 1)))
  have h2 := Polynomial.natDegree_mul_le
    (p := C ((n.factorial : ℚ) ^ 7) * (∏ i ∈ range n, (X - C ((i : ℚ) + 1))))
    (q := ∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)))
  simp only [Polynomial.natDegree_C, zero_add] at h1
  unfold baseNumerator
  omega

theorem weightedNumerator_natDegree_le (n : ℕ) (W : ℚ[X]) :
    (weightedNumerator n W).natDegree ≤ 2 * n + 2 * W.natDegree := by
  have hmul := Polynomial.natDegree_mul_le (p := baseNumerator n) (q := W.comp (baseU n))
  have hcomp := Polynomial.natDegree_comp_le (p := W) (q := baseU n)
  rw [baseU_natDegree] at hcomp
  have hbase := baseNumerator_natDegree_le n
  unfold weightedNumerator
  omega

theorem weightedNumerator_zero_implies_multiplier_zero (n : ℕ) (W : ℚ[X])
    (h : weightedNumerator n W = 0) : W = 0 := by
  have hcomp : W.comp (baseU n) = 0 :=
    (mul_eq_zero.mp h).resolve_left (baseNumerator_ne_zero n)
  rcases Polynomial.comp_eq_zero_iff.mp hcomp with hW | hconstant
  · exact hW
  · have hdeg := congrArg Polynomial.natDegree hconstant.2
    rw [baseU_natDegree, Polynomial.natDegree_C] at hdeg
    omega

theorem all_local_coefficients_zero_implies_zero (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (hzero : AllLocalCoefficientsZero n W) : W = 0 := by
  have hdvd := all_zero_jets_imply_full_denominator_divisibility n W hzero
  have hnumzero : weightedNumerator n W = 0 := by
    by_contra hnum
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd hnum
    rw [polePolynomial_pow_natDegree] at hdeg
    have hbound := weightedNumerator_natDegree_le n W
    unfold ProperMultiplier at hproper
    omega
  exact weightedNumerator_zero_implies_multiplier_zero n W hnumzero

theorem weightedLocalCoefficient_sub (n j s : ℕ) (W V : ℚ[X]) :
    CoefficientMapJet.weightedLocalCoefficient n j s (W - V) =
      CoefficientMapJet.weightedLocalCoefficient n j s W -
        CoefficientMapJet.weightedLocalCoefficient n j s V := by
  simp only [CoefficientMapJet.weightedLocalCoefficient, CoefficientMapJet.weightedClearedSeries,
    Polynomial.sub_comp, Polynomial.coe_sub, mul_sub, map_sub]

theorem local_coefficients_injective (n : ℕ) (W V : ℚ[X])
    (hW : ProperMultiplier n W) (hV : ProperMultiplier n V)
    (heq : ∀ j ≤ n, ∀ s, 1 ≤ s → s ≤ 9 →
      CoefficientMapJet.weightedLocalCoefficient n j s W =
        CoefficientMapJet.weightedLocalCoefficient n j s V) : W = V := by
  have hdiff : ProperMultiplier n (W - V) := by
    have hdeg := Polynomial.natDegree_sub_le W V
    unfold ProperMultiplier at *
    rcases le_total W.natDegree V.natDegree with h | h
    · rw [max_eq_right h] at hdeg
      omega
    · rw [max_eq_left h] at hdeg
      omega
  have hzero : AllLocalCoefficientsZero n (W - V) := by
    intro j hj s hs1 hs9
    rw [weightedLocalCoefficient_sub, heq j hj s hs1 hs9, sub_self]
  exact sub_eq_zero.mp (all_local_coefficients_zero_implies_zero n (W - V) hdiff hzero)

theorem fullLocalCoefficientMap_injective (n : ℕ) :
    Function.Injective (fun W : {W : ℚ[X] // ProperMultiplier n W} => fullLocalCoefficientMap n W.val) := by
  intro W V heq
  apply Subtype.ext
  apply local_coefficients_injective n W.val V.val W.property V.property
  intro j hj s hs1 hs9
  have hfin : s - 1 < 9 := by omega
  have hindex : s - 1 + 1 = s := by omega
  have h := congrFun (congrFun heq ⟨j, Nat.lt_succ_of_le hj⟩) ⟨s - 1, hfin⟩
  simpa only [fullLocalCoefficientMap, hindex] using h

theorem quartic_is_proper (n : ℕ) (W : ℚ[X]) (hW : W.natDegree ≤ 4) : ProperMultiplier n W := by
  unfold ProperMultiplier
  omega

end ZetaNine.CoefficientMapInjectivity

/- SOURCE module missions.zeta9.formalization.CoefficientMapPartialFractions; full proof bodies preserved. -/

/-!
Global partial fractions for the actual finite p=9, q=1, m=n rational
function, with coefficients from the frozen actual local formal series.
This does not assert vanishing of the simple-pole total, an infinite-sum
identity, or invertibility of the original five aggregated outputs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapPartialFractions

open CoefficientMapInjectivity

theorem clearedPolePolynomial_comp_shift (n j : ℕ) :
    (clearedPolePolynomial n j).comp (CoefficientMapJet.shiftedVariable j) =
      CoefficientMapJet.shiftedClearedDenominator n j := by
  simp only [clearedPolePolynomial, CoefficientMapJet.shiftedClearedDenominator,
    Polynomial.prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]

theorem localTruncation_comp_eq_sum (n j : ℕ) (W : ℚ[X]) :
    (localTruncation n j W).comp (X + C (j : ℚ)) =
      ∑ s ∈ Icc 1 9, C (CoefficientMapJet.weightedLocalCoefficient n j s W) *
        (X + C (j : ℚ)) ^ (9 - s) := by
  unfold localTruncation Polynomial.comp
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
    simp only [CoefficientMapJet.weightedLocalCoefficient, he]

theorem partialNumerator_eq_sum_blocks (n : ℕ) (W : ℚ[X]) :
    partialNumerator n W = ∑ j ∈ range (n + 1), partialBlock n j W := by
  unfold partialNumerator partialBlock
  apply Finset.sum_congr rfl
  intro j hj
  rw [localTruncation_comp_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem partialBlock_comp_own_shift (n j : ℕ) (W : ℚ[X]) :
    (partialBlock n j W).comp (CoefficientMapJet.shiftedVariable j) =
      CoefficientMapJet.shiftedClearedDenominator n j ^ 9 * localTruncation n j W := by
  rw [partialBlock, Polynomial.mul_comp, Polynomial.pow_comp, clearedPolePolynomial_comp_shift]
  simp only [Polynomial.comp_assoc, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, CoefficientMapJet.shiftedVariable,
    sub_add_cancel, Polynomial.comp_X]

theorem truncation_remainder_X_pow_dvd (S : PowerSeries ℚ) :
    (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣ S - (PowerSeries.trunc 9 S : PowerSeries ℚ) := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro k hk
  simp only [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hk, sub_self]

theorem polynomial_X_pow_dvd_of_series (P : ℚ[X])
    (h : (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣ (P : PowerSeries ℚ)) :
    (X : ℚ[X]) ^ 9 ∣ P := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro k hk
  simpa only [Polynomial.coeff_coe] using PowerSeries.X_pow_dvd_iff.mp h k hk

theorem own_block_matches_nine_jets (n j : ℕ) (W : ℚ[X]) :
    (X : ℚ[X]) ^ 9 ∣
      (weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable j) -
        (partialBlock n j W).comp (CoefficientMapJet.shiftedVariable j) := by
  apply polynomial_X_pow_dvd_of_series
  have h := dvd_mul_of_dvd_left
    (truncation_remainder_X_pow_dvd (CoefficientMapJet.weightedClearedSeries n j W))
    ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)
  have he : ((weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable j) -
      (partialBlock n j W).comp (CoefficientMapJet.shiftedVariable j) : ℚ[X]) =
      CoefficientMapJet.shiftedNumerator n j * W.comp (CoefficientMapJet.localU n j) -
        CoefficientMapJet.shiftedClearedDenominator n j ^ 9 * localTruncation n j W := by
    rw [weightedNumerator_shift, partialBlock_comp_own_shift]
  rw [he]
  convert h using 1
  rw [sub_mul, CoefficientMapJet.weightedClearedSeries_denominator_identity]
  simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, localTruncation]
  ring

theorem different_block_pole_divisibility (n i j : ℕ) (W : ℚ[X])
    (hj : j ≤ n) (hji : j ≠ i) :
    (X + C (j : ℚ)) ^ 9 ∣ partialBlock n i W := by
  have hjmem : j ∈ (range (n + 1)).erase i := by
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨hji, Nat.lt_succ_of_le hj⟩
  have hbase : X + C (j : ℚ) ∣ clearedPolePolynomial n i :=
    Finset.dvd_prod_of_mem (fun k : ℕ => X + C (k : ℚ)) hjmem
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hbase 9) _

theorem different_block_shift_X_pow_dvd (n i j : ℕ) (W : ℚ[X])
    (hj : j ≤ n) (hji : j ≠ i) :
    (X : ℚ[X]) ^ 9 ∣ (partialBlock n i W).comp (CoefficientMapJet.shiftedVariable j) := by
  obtain ⟨q, hq⟩ := different_block_pole_divisibility n i j W hj hji
  refine ⟨q.comp (CoefficientMapJet.shiftedVariable j), ?_⟩
  have he := congrArg (fun p : ℚ[X] => p.comp (CoefficientMapJet.shiftedVariable j)) hq
  simpa only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, CoefficientMapJet.shiftedVariable, sub_add_cancel] using he

theorem full_candidate_matches_nine_jets (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n) :
    (X : ℚ[X]) ^ 9 ∣
      (weightedNumerator n W - partialNumerator n W).comp (CoefficientMapJet.shiftedVariable j) := by
  have hjmem : j ∈ range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hsplit : (partialNumerator n W).comp (CoefficientMapJet.shiftedVariable j) =
      (partialBlock n j W).comp (CoefficientMapJet.shiftedVariable j) +
        ∑ i ∈ (range (n + 1)).erase j,
          (partialBlock n i W).comp (CoefficientMapJet.shiftedVariable j) := by
    rw [partialNumerator_eq_sum_blocks, Polynomial.sum_comp]
    exact (Finset.add_sum_erase (range (n + 1))
      (fun i => (partialBlock n i W).comp (CoefficientMapJet.shiftedVariable j)) hjmem).symm
  have hoff : (X : ℚ[X]) ^ 9 ∣
      ∑ i ∈ (range (n + 1)).erase j,
        (partialBlock n i W).comp (CoefficientMapJet.shiftedVariable j) := by
    apply Finset.dvd_sum
    intro i hi
    exact different_block_shift_X_pow_dvd n i j W hj (Finset.ne_of_mem_erase hi).symm
  rw [Polynomial.sub_comp, hsplit, sub_add_eq_sub_sub]
  exact dvd_sub (own_block_matches_nine_jets n j W) hoff

theorem shifted_divisibility_implies_pole_divisibility (P : ℚ[X]) (j : ℕ)
    (h : (X : ℚ[X]) ^ 9 ∣ P.comp (CoefficientMapJet.shiftedVariable j)) :
    (X + C (j : ℚ)) ^ 9 ∣ P := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.comp (X + C (j : ℚ)), ?_⟩
  have he := congrArg (fun p : ℚ[X] => p.comp (X + C (j : ℚ))) hq
  simpa only [Polynomial.comp_assoc, CoefficientMapJet.shiftedVariable,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right,
    Polynomial.comp_X, Polynomial.mul_comp, Polynomial.pow_comp] using he

theorem denominator_divides_actual_candidate_difference (n : ℕ) (W : ℚ[X]) :
    polePolynomial n ^ 9 ∣ weightedNumerator n W - partialNumerator n W := by
  unfold polePolynomial
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact pole_factors_coprime a b hab
  · intro j hj
    apply shifted_divisibility_implies_pole_divisibility
    exact full_candidate_matches_nine_jets n j W (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem actual_series_from_shifted_numerator (n j : ℕ) (W : ℚ[X]) :
    CoefficientMapJet.weightedClearedSeries n j W =
      ((weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) *
        ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹ := by
  rw [weightedNumerator_shift]
  simp only [CoefficientMapJet.weightedClearedSeries, CoefficientMapJet.clearedSeries,
    Polynomial.coe_mul]
  ring

theorem candidateClearedSeries_denominator_identity (n j : ℕ) (W : ℚ[X]) :
    candidateClearedSeries n j W *
        (CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      ((partialNumerator n W).comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) := by
  have h : PowerSeries.constantCoeff
      ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero n j)
  unfold candidateClearedSeries
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

-- This uses the local truncation/divisibility result, without global PF or properness.
theorem candidate_first_nine_coefficients (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n)
    (k : ℕ) (hk : k < 9) :
    PowerSeries.coeff k (candidateClearedSeries n j W) =
      PowerSeries.coeff k (CoefficientMapJet.weightedClearedSeries n j W) := by
  obtain ⟨q, hq⟩ := full_candidate_matches_nine_jets n j W hj
  have hs : (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣
      ((weightedNumerator n W - partialNumerator n W).comp
        (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) := by
    refine ⟨(q : PowerSeries ℚ), ?_⟩
    have he := congrArg (fun p : ℚ[X] => (p : PowerSeries ℚ)) hq
    simpa only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X] using he
  have hm := dvd_mul_of_dvd_left hs
    (((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹)
  have he : (((weightedNumerator n W - partialNumerator n W).comp
      (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) *
        ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹) =
      CoefficientMapJet.weightedClearedSeries n j W - candidateClearedSeries n j W := by
    rw [Polynomial.sub_comp, Polynomial.coe_sub, sub_mul, ← actual_series_from_shifted_numerator]
    rfl
  rw [he] at hm
  have hz := PowerSeries.X_pow_dvd_iff.mp hm k hk
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

theorem candidate_local_coefficients (n j s : ℕ) (W : ℚ[X]) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    PowerSeries.coeff (9 - s) (candidateClearedSeries n j W) =
      CoefficientMapJet.weightedLocalCoefficient n j s W := by
  exact candidate_first_nine_coefficients n j W hj (9 - s) (by omega)

theorem clearedPolePolynomial_natDegree (n j : ℕ) (hj : j ≤ n) :
    (clearedPolePolynomial n j).natDegree = n := by
  unfold clearedPolePolynomial
  rw [Polynomial.natDegree_prod_of_monic ((range (n + 1)).erase j)
    (fun k : ℕ => X + C (k : ℚ)) (fun k hk => Polynomial.monic_X_add_C (k : ℚ))]
  simp only [Polynomial.natDegree_X_add_C]
  simp [Nat.lt_succ_of_le hj]

theorem localTruncation_natDegree_le (n j : ℕ) (W : ℚ[X]) :
    (localTruncation n j W).natDegree ≤ 8 := by
  have h := PowerSeries.natDegree_trunc_lt (CoefficientMapJet.weightedClearedSeries n j W) 8
  exact Nat.le_of_lt_succ h

theorem partialBlock_natDegree_le (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n) :
    (partialBlock n j W).natDegree ≤ 9 * n + 8 := by
  have hm := Polynomial.natDegree_mul_le (p := clearedPolePolynomial n j ^ 9)
    (q := (localTruncation n j W).comp (X + C (j : ℚ)))
  have hc := Polynomial.natDegree_comp_le (p := localTruncation n j W) (q := X + C (j : ℚ))
  rw [Polynomial.natDegree_X_add_C, mul_one] at hc
  rw [Polynomial.natDegree_pow, clearedPolePolynomial_natDegree n j hj] at hm
  have ht := localTruncation_natDegree_le n j W
  unfold partialBlock
  omega

theorem partialNumerator_natDegree_le (n : ℕ) (W : ℚ[X]) :
    (partialNumerator n W).natDegree ≤ 9 * n + 8 := by
  rw [partialNumerator_eq_sum_blocks]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact partialBlock_natDegree_le n j W (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem actual_global_polynomial_partial_fractions (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) : weightedNumerator n W = partialNumerator n W := by
  have hdvd := denominator_divides_actual_candidate_difference n W
  have hzero : weightedNumerator n W - partialNumerator n W = 0 := by
    by_contra hne
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [polePolynomial_pow_natDegree] at hdeg
    have hw := weightedNumerator_natDegree_le n W
    have hp := partialNumerator_natDegree_le n W
    have hdiff := Polynomial.natDegree_sub_le (weightedNumerator n W) (partialNumerator n W)
    unfold ProperMultiplier at hproper
    rcases le_total (weightedNumerator n W).natDegree (partialNumerator n W).natDegree with h | h
    · rw [max_eq_right h] at hdiff
      omega
    · rw [max_eq_left h] at hdiff
      omega
  exact sub_eq_zero.mp hzero

theorem polePolynomial_eval (n : ℕ) (t : ℚ) :
    (polePolynomial n).eval t = CoefficientMap.poleProduct n t := by
  simp only [polePolynomial, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  rfl

theorem polePolynomial_eval_ne_zero (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) : (polePolynomial n).eval t ≠ 0 := by
  rw [polePolynomial_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact hregular k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem polePolynomial_eval_factor (n j : ℕ) (t : ℚ) (hj : j ≤ n) :
    (polePolynomial n).eval t = (t + (j : ℚ)) * (clearedPolePolynomial n j).eval t := by
  simp only [polePolynomial, clearedPolePolynomial, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  exact (Finset.mul_prod_erase (range (n + 1)) (fun k => t + (k : ℚ))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).symm

theorem actual_weighted_rational_representation (n : ℕ) (W : ℚ[X]) (t : ℚ) :
    CoefficientMap.weightedR n W t =
      (weightedNumerator n W).eval t / ((polePolynomial n).eval t) ^ 9 := by
  simp only [weightedNumerator, Polynomial.eval_mul, Polynomial.eval_comp,
    baseNumerator_eval, baseU, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C,
    polePolynomial_eval, CoefficientMap.weightedR, CoefficientMap.actualR]
  ring

theorem partial_term_division (n j s : ℕ) (W : ℚ[X]) (t : ℚ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    (CoefficientMapJet.weightedLocalCoefficient n j s W *
      (clearedPolePolynomial n j).eval t ^ 9 * (t + (j : ℚ)) ^ (9 - s)) /
        (polePolynomial n).eval t ^ 9 =
      CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
  apply (div_eq_div_iff (pow_ne_zero _ (polePolynomial_eval_ne_zero n t hregular))
    (pow_ne_zero _ (hregular j hj))).mpr
  rw [polePolynomial_eval_factor n j t hj, mul_pow]
  have he : (t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s = (t + (j : ℚ)) ^ 9 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = CoefficientMapJet.weightedLocalCoefficient n j s W *
        (clearedPolePolynomial n j).eval t ^ 9 *
        ((t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s) := by ring
    _ = _ := by rw [he]; ring

theorem actual_global_partial_fractions (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    CoefficientMap.weightedR n W t =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
  rw [actual_weighted_rational_representation, actual_global_polynomial_partial_fractions n W hproper]
  simp only [partialNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  exact partial_term_division n j s W t (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2 hregular

end ZetaNine.CoefficientMapPartialFractions

/- SOURCE module missions.zeta9.formalization.CoefficientMapReflection; full proof bodies preserved. -/

/-!
Actual reflection and coefficient totals for the frozen finite rational function.
Simple-pole cancellation uses the stronger degree bound, not strict properness.
No infinite sum or five-dimensional inverse map is asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapReflection

open CoefficientMapInjectivity CoefficientMapPartialFractions

theorem product_reverse_range (n : ℕ) (f : ℕ → ℚ[X]) :
    ∏ k ∈ range (n + 1), f (n - k) = ∏ k ∈ range (n + 1), f k := by
  apply Finset.prod_nbij' (fun k : ℕ => n - k) (fun k : ℕ => n - k)
  · intro k hk
    have h := Finset.mem_range.mp hk
    rw [Finset.mem_range]
    omega
  · intro k hk
    have h := Finset.mem_range.mp hk
    rw [Finset.mem_range]
    omega
  · intro k hk
    have h := Finset.mem_range.mp hk
    omega
  · intro k hk
    have h := Finset.mem_range.mp hk
    omega
  · intro k hk
    rfl

theorem product_reverse_erased_range (n j : ℕ) (hj : j ≤ n) (f : ℕ → ℚ[X]) :
    ∏ k ∈ (range (n + 1)).erase (n - j), f (n - k) =
      ∏ k ∈ (range (n + 1)).erase j, f k := by
  apply Finset.prod_nbij' (fun k : ℕ => n - k) (fun k : ℕ => n - k)
  · intro k hk
    have h := Finset.mem_erase.mp hk
    have hr := Finset.mem_range.mp h.2
    rw [Finset.mem_erase, Finset.mem_range]
    constructor <;> omega
  · intro k hk
    have h := Finset.mem_erase.mp hk
    have hr := Finset.mem_range.mp h.2
    rw [Finset.mem_erase, Finset.mem_range]
    constructor <;> omega
  · intro k hk
    have h := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
    omega
  · intro k hk
    have h := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
    omega
  · intro k hk
    rfl

theorem sum_reverse_range (n : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ range (n + 1), f (n - k) = ∑ k ∈ range (n + 1), f k := by
  apply Finset.sum_nbij' (fun k : ℕ => n - k) (fun k : ℕ => n - k)
  · intro k hk
    have h := Finset.mem_range.mp hk
    rw [Finset.mem_range]
    omega
  · intro k hk
    have h := Finset.mem_range.mp hk
    rw [Finset.mem_range]
    omega
  · intro k hk
    have h := Finset.mem_range.mp hk
    omega
  · intro k hk
    have h := Finset.mem_range.mp hk
    omega
  · intro k hk
    rfl

theorem baseNumerator_reflection (n : ℕ) :
    (baseNumerator n).comp (reflectionVariable n) = baseNumerator n := by
  have hleft : (∏ i ∈ range n, (reflectionVariable n - C ((i : ℚ) + 1))) =
      (-1 : ℚ[X]) ^ n * ∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)) := by
    calc
      _ = ∏ i ∈ range n, -(X + C (n : ℚ) + C ((i : ℚ) + 1)) := by
        apply Finset.prod_congr rfl
        intro i hi
        unfold reflectionVariable
        ring
      _ = _ := by rw [Finset.prod_neg, Finset.card_range]
  have hright : (∏ i ∈ range n, (reflectionVariable n + C (n : ℚ) + C ((i : ℚ) + 1))) =
      (-1 : ℚ[X]) ^ n * ∏ i ∈ range n, (X - C ((i : ℚ) + 1)) := by
    calc
      _ = ∏ i ∈ range n, -(X - C ((i : ℚ) + 1)) := by
        apply Finset.prod_congr rfl
        intro i hi
        unfold reflectionVariable
        ring
      _ = _ := by rw [Finset.prod_neg, Finset.card_range]
  simp only [baseNumerator, Polynomial.mul_comp, Polynomial.prod_comp, Polynomial.C_comp,
    Polynomial.sub_comp, Polynomial.add_comp, Polynomial.X_comp]
  rw [hleft, hright]
  have hsign : (-1 : ℚ[X]) ^ n * (-1 : ℚ[X]) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = C ((n.factorial : ℚ) ^ 7) * ((-1 : ℚ[X]) ^ n * (-1 : ℚ[X]) ^ n) *
        (∏ i ∈ range n, (X - C ((i : ℚ) + 1))) *
        (∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1))) := by ring
    _ = _ := by rw [hsign, mul_one]

theorem baseU_reflection (n : ℕ) : (baseU n).comp (reflectionVariable n) = baseU n := by
  simp only [baseU, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
    reflectionVariable]
  ring

theorem weightedNumerator_reflection (n : ℕ) (W : ℚ[X]) :
    (weightedNumerator n W).comp (reflectionVariable n) = weightedNumerator n W := by
  simp only [weightedNumerator, Polynomial.mul_comp, baseNumerator_reflection,
    Polynomial.comp_assoc, baseU_reflection]

theorem polePolynomial_reflection (n : ℕ) :
    (polePolynomial n).comp (reflectionVariable n) = C ((-1 : ℚ) ^ (n + 1)) * polePolynomial n := by
  simp only [polePolynomial, Polynomial.prod_comp, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.C_comp]
  calc
    _ = ∏ k ∈ range (n + 1), -(X + C ((n - k : ℕ) : ℚ)) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hk' := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [Nat.cast_sub hk', map_sub]
      unfold reflectionVariable
      ring
    _ = (-1 : ℚ[X]) ^ (n + 1) * ∏ k ∈ range (n + 1), (X + C (k : ℚ)) := by
      rw [Finset.prod_neg, Finset.card_range,
        product_reverse_range n (fun k : ℕ => (X : ℚ[X]) + C (k : ℚ))]
    _ = _ := by simp only [map_pow, map_neg, map_one]

theorem clearedPolePolynomial_reflection (n j : ℕ) (hj : j ≤ n) :
    (clearedPolePolynomial n (n - j)).comp (reflectionVariable n) =
      C ((-1 : ℚ) ^ n) * clearedPolePolynomial n j := by
  simp only [clearedPolePolynomial, Polynomial.prod_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  calc
    _ = ∏ k ∈ (range (n + 1)).erase (n - j), -(X + C ((n - k : ℕ) : ℚ)) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hk' := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_erase.mp hk).2)
      rw [Nat.cast_sub hk', map_sub]
      unfold reflectionVariable
      ring
    _ = (-1 : ℚ[X]) ^ n * ∏ k ∈ (range (n + 1)).erase j, (X + C (k : ℚ)) := by
      rw [Finset.prod_neg,
        product_reverse_erased_range n j hj (fun k : ℕ => (X : ℚ[X]) + C (k : ℚ))]
      congr 1
      simp [Nat.lt_succ_of_le (Nat.sub_le n j)]
    _ = _ := by simp only [map_pow, map_neg, map_one]

theorem reflectionVariable_eval (n : ℕ) (t : ℚ) :
    (reflectionVariable n).eval t = -(n : ℚ) - t := by
  simp [reflectionVariable]
  ring

theorem actual_weightedR_reflection (n : ℕ) (hn : Even n) (W : ℚ[X]) (t : ℚ) :
    CoefficientMap.weightedR n W (-(n : ℚ) - t) = -CoefficientMap.weightedR n W t := by
  have hn1 : (-1 : ℚ) ^ (n + 1) = -1 := by rw [pow_succ, hn.neg_one_pow, one_mul]
  rw [actual_weighted_rational_representation, actual_weighted_rational_representation,
    ← reflectionVariable_eval n t, ← Polynomial.eval_comp, ← Polynomial.eval_comp,
    weightedNumerator_reflection, polePolynomial_reflection, hn1]
  norm_num [neg_pow, div_neg]

theorem reflection_preserves_regular_points (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ∀ k ≤ n, (-(n : ℚ) - t) + (k : ℚ) ≠ 0 := by
  intro k hk
  have h := hregular (n - k) (Nat.sub_le n k)
  rw [Nat.cast_sub hk] at h
  intro hz
  apply h
  linarith

theorem local_shift_reflection (n j : ℕ) (hj : j ≤ n) :
    (CoefficientMapJet.shiftedVariable (n - j)).comp (-X) =
      (reflectionVariable n).comp (CoefficientMapJet.shiftedVariable j) := by
  simp only [CoefficientMapJet.shiftedVariable, reflectionVariable, Polynomial.sub_comp,
    Polynomial.neg_comp, Polynomial.X_comp, Polynomial.C_comp, Nat.cast_sub hj, map_sub]
  ring

theorem shiftedWeightedNumerator_reflection (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n) :
    ((weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable (n - j))).comp (-X) =
      (weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable j) := by
  rw [Polynomial.comp_assoc, local_shift_reflection n j hj, ← Polynomial.comp_assoc,
    weightedNumerator_reflection]

theorem shiftedClearedDenominator_reflection (n j : ℕ) (hj : j ≤ n) :
    (CoefficientMapJet.shiftedClearedDenominator n (n - j)).comp (-X) =
      C ((-1 : ℚ) ^ n) * CoefficientMapJet.shiftedClearedDenominator n j := by
  rw [← clearedPolePolynomial_comp_shift, Polynomial.comp_assoc, local_shift_reflection n j hj,
    ← Polynomial.comp_assoc, clearedPolePolynomial_reflection n j hj,
    Polynomial.mul_comp, Polynomial.C_comp, clearedPolePolynomial_comp_shift]

theorem rescale_neg_one_C (a : ℚ) :
    PowerSeries.rescale (-1 : ℚ) (PowerSeries.C a) = PowerSeries.C a := by
  ext k
  by_cases hk : k = 0 <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C, hk]

theorem rescale_neg_one_polynomial (P : ℚ[X]) :
    PowerSeries.rescale (-1 : ℚ) (P : PowerSeries ℚ) = (P.comp (-X) : PowerSeries ℚ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [Polynomial.coe_add, map_add, hP, hQ, Polynomial.add_comp]
  | monomial k a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X,
        map_mul, map_pow, rescale_neg_one_C, PowerSeries.rescale_neg_one_X,
        Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp,
        Polynomial.coe_neg]

theorem actual_local_series_reflection (n j : ℕ) (hn : Even n) (W : ℚ[X]) (hj : j ≤ n) :
    PowerSeries.rescale (-1 : ℚ) (CoefficientMapJet.weightedClearedSeries n (n - j) W) =
      CoefficientMapJet.weightedClearedSeries n j W := by
  have hD : PowerSeries.rescale (-1 : ℚ)
      (CoefficientMapJet.shiftedClearedDenominator n (n - j) : PowerSeries ℚ) =
      (CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) := by
    rw [rescale_neg_one_polynomial, shiftedClearedDenominator_reflection n j hj, hn.neg_one_pow]
    simp
  have hP : PowerSeries.rescale (-1 : ℚ)
      ((CoefficientMapJet.shiftedNumerator n (n - j) *
        W.comp (CoefficientMapJet.localU n (n - j)) : ℚ[X]) : PowerSeries ℚ) =
      ((CoefficientMapJet.shiftedNumerator n j * W.comp (CoefficientMapJet.localU n j) : ℚ[X]) : PowerSeries ℚ) := by
    rw [rescale_neg_one_polynomial, ← weightedNumerator_shift, shiftedWeightedNumerator_reflection n j W hj,
      weightedNumerator_shift]
  have he := congrArg (PowerSeries.rescale (-1 : ℚ))
    (CoefficientMapJet.weightedClearedSeries_denominator_identity n (n - j) W)
  rw [map_mul, map_pow, hD, hP] at he
  have hnonzero : (CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 ≠ 0 := by
    intro hz
    have hc := pow_ne_zero 9 (CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero n j)
    apply hc
    rw [← map_pow, hz, map_zero]
  apply mul_right_cancel₀ hnonzero
  exact he.trans (CoefficientMapJet.weightedClearedSeries_denominator_identity n j W).symm

theorem local_coefficient_reflection (n j s : ℕ) (hn : Even n) (W : ℚ[X])
    (hj : j ≤ n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    CoefficientMapJet.weightedLocalCoefficient n (n - j) s W =
      (-1 : ℚ) ^ (s + 1) * CoefficientMapJet.weightedLocalCoefficient n j s W := by
  have he := congrArg (PowerSeries.coeff (9 - s)) (actual_local_series_reflection n j hn W hj)
  rw [PowerSeries.coeff_rescale] at he
  have hsign : (-1 : ℚ) ^ (9 - s) * (-1 : ℚ) ^ (9 - s) = 1 := by
    rw [← mul_pow]
    norm_num
  have hparity : (-1 : ℚ) ^ (9 - s) = (-1 : ℚ) ^ (s + 1) := by
    interval_cases s <;> norm_num
  unfold CoefficientMapJet.weightedLocalCoefficient
  calc
    _ = ((-1 : ℚ) ^ (9 - s) * (-1 : ℚ) ^ (9 - s)) *
        PowerSeries.coeff (9 - s) (CoefficientMapJet.weightedClearedSeries n (n - j) W) := by rw [hsign, one_mul]
    _ = (-1 : ℚ) ^ (9 - s) *
        (((-1 : ℚ) ^ (9 - s)) *
          PowerSeries.coeff (9 - s) (CoefficientMapJet.weightedClearedSeries n (n - j) W)) := by ring
    _ = _ := by rw [he, hparity]

theorem rho_even_order_zero (n s : ℕ) (hn : Even n) (W : ℚ[X])
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hs : Even s) : rho n s W = 0 := by
  have he : rho n s W = (-1 : ℚ) ^ (s + 1) * rho n s W := by
    calc
      _ = ∑ j ∈ range (n + 1), CoefficientMapJet.weightedLocalCoefficient n (n - j) s W :=
        (sum_reverse_range n _).symm
      _ = ∑ j ∈ range (n + 1), (-1 : ℚ) ^ (s + 1) *
          CoefficientMapJet.weightedLocalCoefficient n j s W := by
        apply Finset.sum_congr rfl
        intro j hj
        exact local_coefficient_reflection n j s hn W (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hs1 hs9
      _ = _ := by rw [← Finset.mul_sum]; rfl
  rw [pow_succ, hs.neg_one_pow, one_mul, neg_one_mul] at he
  linarith

theorem strong_proper_implies_proper (n : ℕ) (W : ℚ[X])
    (h : StrongProperMultiplier n W) : ProperMultiplier n W := by
  unfold StrongProperMultiplier at h
  unfold ProperMultiplier
  omega

theorem quartic_is_strong_proper (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    StrongProperMultiplier n W := by
  unfold StrongProperMultiplier
  omega

theorem clearedPolePolynomial_monic (n j : ℕ) : (clearedPolePolynomial n j).Monic := by
  unfold clearedPolePolynomial
  apply Polynomial.monic_prod_of_monic
  intro k hk
  exact Polynomial.monic_X_add_C _

theorem partialBasis_monic (n j s : ℕ) : (partialBasis n j s).Monic := by
  exact ((clearedPolePolynomial_monic n j).pow 9).mul ((Polynomial.monic_X_add_C (j : ℚ)).pow (9 - s))

theorem partialBasis_natDegree (n j s : ℕ) (hj : j ≤ n) :
    (partialBasis n j s).natDegree = 9 * n + (9 - s) := by
  unfold partialBasis
  rw [Polynomial.natDegree_mul ((clearedPolePolynomial_monic n j).pow 9).ne_zero
    ((Polynomial.monic_X_add_C (j : ℚ)).pow (9 - s)).ne_zero,
    Polynomial.natDegree_pow, Polynomial.natDegree_pow,
    clearedPolePolynomial_natDegree n j hj, Polynomial.natDegree_X_add_C]
  omega

theorem partialBasis_simple_pole_top_coefficient (n j : ℕ) (hj : j ≤ n) :
    (partialBasis n j 1).coeff (9 * n + 8) = 1 := by
  have h := (partialBasis_monic n j 1).coeff_natDegree
  simpa only [partialBasis_natDegree n j 1 hj, Nat.reduceSub] using h

theorem partialBasis_higher_pole_top_coefficient (n j s : ℕ) (hj : j ≤ n)
    (hs : 2 ≤ s) (hs9 : s ≤ 9) : (partialBasis n j s).coeff (9 * n + 8) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [partialBasis_natDegree n j s hj]
  omega

theorem partialNumerator_top_coefficient_is_rho_one (n : ℕ) (W : ℚ[X]) :
    (partialNumerator n W).coeff (9 * n + 8) = rho n 1 W := by
  simp only [partialNumerator, Polynomial.finsetSum_coeff, rho]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [Finset.sum_eq_single_of_mem 1 (by simp)]
  · rw [mul_assoc, Polynomial.coeff_C_mul]
    change CoefficientMapJet.weightedLocalCoefficient n j 1 W *
      (partialBasis n j 1).coeff (9 * n + 8) = _
    rw [partialBasis_simple_pole_top_coefficient n j hj', mul_one]
  · intro s hs hsne
    have hs' := Finset.mem_Icc.mp hs
    have hs2 : 2 ≤ s := by omega
    rw [mul_assoc, Polynomial.coeff_C_mul]
    change CoefficientMapJet.weightedLocalCoefficient n j s W *
      (partialBasis n j s).coeff (9 * n + 8) = 0
    rw [partialBasis_higher_pole_top_coefficient n j s hj' hs2 hs'.2, mul_zero]

theorem rho_one_zero_of_strong_proper (n : ℕ) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) : rho n 1 W = 0 := by
  have hpoly := actual_global_polynomial_partial_fractions n W (strong_proper_implies_proper n W hstrong)
  have hcoeff := congrArg (fun P : ℚ[X] => P.coeff (9 * n + 8)) hpoly
  rw [partialNumerator_top_coefficient_is_rho_one] at hcoeff
  have hzero : (weightedNumerator n W).coeff (9 * n + 8) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hbound := weightedNumerator_natDegree_le n W
    unfold StrongProperMultiplier at hstrong
    omega
  rw [hzero] at hcoeff
  exact hcoeff.symm

theorem original_integer_quartic_strong_proper (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) : StrongProperMultiplier n (W.map (Int.castRingHom ℚ)) := by
  exact quartic_is_strong_proper n (by omega) _ (le_trans Polynomial.natDegree_map_le hW)

theorem original_integer_quartic_rho_one_zero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) : rho n 1 (W.map (Int.castRingHom ℚ)) = 0 :=
  rho_one_zero_of_strong_proper n _ (original_integer_quartic_strong_proper n hn2 hn W hW)

end ZetaNine.CoefficientMapReflection

/- SOURCE module missions.zeta9.formalization.CoefficientMapFiniteSum; full proof bodies preserved. -/

/-!
The actual finite summation bridge for the p=9, m=n family.
All coefficients come from the genuine local series. The simple-pole
harmonic term is retained. No infinite sum or irrationality is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFiniteSum

open HarmonicStability CoefficientMapInjectivity CoefficientMapPartialFractions

theorem harmonicPower_succ (s T : ℕ) :
    harmonicPower s (T + 1) = harmonicPower s T + 1 / ((T + 1 : ℕ) : ℚ) ^ s := by
  unfold harmonicPower
  exact Finset.sum_Icc_succ_top (by omega) _

theorem shifted_harmonic_sum (s T j : ℕ) :
    (∑ t ∈ Icc 1 T, 1 / ((t : ℚ) + (j : ℚ)) ^ s) =
      harmonicPower s (T + j) - harmonicPower s j := by
  induction T with
  | zero => simp [harmonicPower]
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have he : T + 1 + j = (T + j) + 1 := by omega
    rw [he, harmonicPower_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem actual_finite_harmonic_identity (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) :
    finiteL n T W = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      CoefficientMapJet.weightedLocalCoefficient n j s W *
        (harmonicPower s (T + j) - harmonicPower s j) := by
  unfold finiteL
  calc
    _ = ∑ t ∈ Icc 1 T, ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s := by
      apply Finset.sum_congr rfl
      intro t ht
      apply actual_global_partial_fractions n W hproper
      intro k hk
      have htpos : (0 : ℚ) < (t : ℚ) := by exact_mod_cast (Finset.mem_Icc.mp ht).1
      exact ne_of_gt (add_pos_of_pos_of_nonneg htpos (Nat.cast_nonneg k))
    _ = ∑ j ∈ range (n + 1), ∑ t ∈ Icc 1 T, ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s :=
      Finset.sum_comm
    _ = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9, ∑ t ∈ Icc 1 T,
        CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro s hs
      have hterm : (∑ t ∈ Icc 1 T,
          CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s) =
          ∑ t ∈ Icc 1 T,
          CoefficientMapJet.weightedLocalCoefficient n j s W * (1 / ((t : ℚ) + (j : ℚ)) ^ s) := by
        apply Finset.sum_congr rfl
        intro t ht
        ring
      rw [hterm]
      rw [← Finset.mul_sum, shifted_harmonic_sum]

theorem actual_grouped_finite_identity (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) :
    finiteL n T W = constantTerm n W +
      (∑ s ∈ Icc 1 9, rho n s W * harmonicPower s T) + shiftedTail n T W := by
  rw [actual_finite_harmonic_identity n T W hproper]
  have hmain : (∑ s ∈ Icc 1 9, rho n s W * harmonicPower s T) =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W * harmonicPower s T := by
    unfold rho
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  rw [hmain]
  unfold constantTerm shiftedTail
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  ring

-- Cancellation is an explicit input here; the reflection development proves it.
-- In particular, properness alone does not supply the simple-pole cancellation.
theorem actual_grouped_finite_identity_no_simple_pole (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (hcancel : rho n 1 W = 0) :
    finiteL n T W = constantTerm n W +
      (∑ s ∈ Icc 2 9, rho n s W * harmonicPower s T) + shiftedTail n T W := by
  rw [actual_grouped_finite_identity n T W hproper]
  have hsplit : (∑ s ∈ Icc 1 9, rho n s W * harmonicPower s T) =
      rho n 1 W * harmonicPower 1 T + ∑ s ∈ Icc 2 9, rho n s W * harmonicPower s T := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    rfl
  rw [hsplit, hcancel, zero_mul, zero_add]

theorem actual_grouped_finite_identity_odd (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (h1 : rho n 1 W = 0)
    (h2 : rho n 2 W = 0) (h4 : rho n 4 W = 0)
    (h6 : rho n 6 W = 0) (h8 : rho n 8 W = 0) :
    finiteL n T W = constantTerm n W +
      (rho n 3 W * harmonicPower 3 T + rho n 5 W * harmonicPower 5 T +
       rho n 7 W * harmonicPower 7 T + rho n 9 W * harmonicPower 9 T) +
      shiftedTail n T W := by
  rw [actual_grouped_finite_identity_no_simple_pole n T W hproper h1]
  have hs : (∑ s ∈ Icc 2 9, rho n s W * harmonicPower s T) =
      rho n 3 W * harmonicPower 3 T + rho n 5 W * harmonicPower 5 T +
      rho n 7 W * harmonicPower 7 T + rho n 9 W * harmonicPower 9 T := by
    norm_num [Finset.sum_Icc_succ_top, h2, h4, h6, h8]
  rw [hs]

theorem harmonic_difference_eq_shifted (s T j : ℕ) :
    harmonicPower s (T + j) - harmonicPower s T =
      ∑ k ∈ Icc 1 j, 1 / ((T : ℚ) + (k : ℚ)) ^ s := by
  simpa only [Nat.add_comm j T, add_comm] using (shifted_harmonic_sum s j T).symm

end ZetaNine.CoefficientMapFiniteSum

/- SOURCE module missions.zeta9.formalization.CoefficientMapSummation; full proof bodies preserved. -/

/-!
Actual finite/infinite summation for p=9, q=1, m=n.
All cancellations come from the actual reflection and stronger degree theorem.
Any HasSum assertion must additionally use a proved Summable statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Topology
open Finset Polynomial Filter

namespace ZetaNine.CoefficientMapSummation

open HarmonicStability CoefficientMapInjectivity CoefficientMapReflection

theorem actual_finite_odd_identity (n T : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) :
    CoefficientMapFiniteSum.finiteL n T W = CoefficientMapFiniteSum.constantTerm n W +
      (CoefficientMapFiniteSum.rho n 3 W * harmonicPower 3 T +
       CoefficientMapFiniteSum.rho n 5 W * harmonicPower 5 T +
       CoefficientMapFiniteSum.rho n 7 W * harmonicPower 7 T +
       CoefficientMapFiniteSum.rho n 9 W * harmonicPower 9 T) +
      CoefficientMapFiniteSum.shiftedTail n T W := by
  exact CoefficientMapFiniteSum.actual_grouped_finite_identity_odd n T W
    (strong_proper_implies_proper n W hstrong) (rho_one_zero_of_strong_proper n W hstrong)
    (rho_even_order_zero n 2 hn W (by norm_num) (by norm_num) (by norm_num))
    (rho_even_order_zero n 4 hn W (by norm_num) (by norm_num) (by norm_num))
    (rho_even_order_zero n 6 hn W (by norm_num) (by norm_num) (by norm_num))
    (rho_even_order_zero n 8 hn W (by norm_num) (by norm_num) (by norm_num))

theorem sum_Icc_eq_sum_range_successor (T : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ Icc 1 T, f t = ∑ t ∈ range T, f (t + 1) := by
  apply Finset.sum_nbij' (fun t : ℕ => t - 1) (fun t : ℕ => t + 1)
  · intro t ht
    have h := Finset.mem_Icc.mp ht
    rw [Finset.mem_range]
    omega
  · intro t ht
    have h := Finset.mem_range.mp ht
    rw [Finset.mem_Icc]
    omega
  · intro t ht
    have h := Finset.mem_Icc.mp ht
    omega
  · intro t ht
    omega
  · intro t ht
    have h := Finset.mem_Icc.mp ht
    have he : t - 1 + 1 = t := by omega
    rw [he]

theorem harmonicPower_cast (s T : ℕ) :
    (harmonicPower s T : ℝ) = ∑ t ∈ Icc 1 T, 1 / (t : ℝ) ^ s := by
  unfold harmonicPower
  push_cast
  rfl

theorem harmonicPower_cast_eq_range (s T : ℕ) (hs : 1 ≤ s) :
    (harmonicPower s T : ℝ) = ∑ t ∈ range (T + 1), 1 / (t : ℝ) ^ s := by
  rw [harmonicPower_cast, sum_Icc_eq_sum_range_successor, Finset.sum_range_succ']
  simp [show s ≠ 0 by omega]

theorem zetaReal_eq_tsum (s : ℕ) (hs : 1 < s) :
    zetaReal s = ∑' t : ℕ, 1 / (t : ℝ) ^ s := by
  have he : ((∑' t : ℕ, 1 / (t : ℝ) ^ s : ℝ) : ℂ) = riemannZeta (s : ℂ) := by
    rw [Complex.ofReal_tsum, zeta_nat_eq_tsum_of_gt_one hs]
    apply tsum_congr
    intro t
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_natCast]
  have hr := congrArg Complex.re he
  simpa only [Complex.ofReal_re, zetaReal] using hr.symm

theorem harmonicPower_tendsto_zeta (s : ℕ) (hs : 1 < s) :
    Tendsto (fun T : ℕ => (harmonicPower s T : ℝ)) atTop (𝓝 (zetaReal s)) := by
  have h := ((Real.summable_one_div_nat_pow.mpr hs).hasSum.tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  rw [← zetaReal_eq_tsum s hs] at h
  simpa only [Function.comp_def, ← harmonicPower_cast_eq_range s _ (by omega)] using h

theorem shifted_reciprocal_tendsto_zero (s k : ℕ) (hs : 1 ≤ s) :
    Tendsto (fun T : ℕ => 1 / ((T : ℝ) + (k : ℝ)) ^ s) atTop (𝓝 0) := by
  have hbase : Tendsto (fun T : ℕ => (((T + k : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat k))
  simpa only [one_div, inv_pow, Nat.cast_add, zero_pow (show s ≠ 0 by omega)] using hbase.pow s

theorem harmonic_fixed_tail_tendsto_zero (s j : ℕ) (hs : 1 ≤ s) :
    Tendsto (fun T : ℕ => ((harmonicPower s (T + j) - harmonicPower s T : ℚ) : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Icc 1 j) (fun k hk => shifted_reciprocal_tendsto_zero s k hs)
  have he : (fun T : ℕ => ((harmonicPower s (T + j) - harmonicPower s T : ℚ) : ℝ)) =
      (fun T : ℕ => ∑ k ∈ Icc 1 j, 1 / ((T : ℝ) + (k : ℝ)) ^ s) := by
    funext T
    rw [CoefficientMapFiniteSum.harmonic_difference_eq_shifted]
    push_cast
    rfl
  rw [he]
  simpa only [Finset.sum_const_zero] using h

theorem actual_shiftedTail_tendsto_zero (n : ℕ) (W : ℚ[X]) :
    Tendsto (fun T : ℕ => (CoefficientMapFiniteSum.shiftedTail n T W : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (range (n + 1)) (fun j hj =>
    tendsto_finsetSum (Icc 1 9) (fun s hs =>
      (harmonic_fixed_tail_tendsto_zero s j (Finset.mem_Icc.mp hs).1).const_mul
        (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ)))
  have he : (fun T : ℕ => (CoefficientMapFiniteSum.shiftedTail n T W : ℝ)) =
      (fun T : ℕ => ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) *
          ((harmonicPower s (T + j) - harmonicPower s T : ℚ) : ℝ)) := by
    funext T
    unfold CoefficientMapFiniteSum.shiftedTail
    push_cast
    rfl
  rw [he]
  simpa only [mul_zero, Finset.sum_const_zero] using h

theorem actual_finiteL_tendsto_exactL (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) :
    Tendsto (fun T : ℕ => (CoefficientMapFiniteSum.finiteL n T W : ℝ)) atTop (𝓝 (exactL n W)) := by
  have hB : Tendsto (fun _ : ℕ => (CoefficientMapFiniteSum.constantTerm n W : ℝ)) atTop
      (𝓝 (CoefficientMapFiniteSum.constantTerm n W : ℝ)) := tendsto_const_nhds
  have hmain := (((harmonicPower_tendsto_zeta 3 (by omega)).const_mul (CoefficientMapFiniteSum.rho n 3 W : ℝ)).add
    ((harmonicPower_tendsto_zeta 5 (by omega)).const_mul (CoefficientMapFiniteSum.rho n 5 W : ℝ))).add
    ((harmonicPower_tendsto_zeta 7 (by omega)).const_mul (CoefficientMapFiniteSum.rho n 7 W : ℝ))
  have hmain' := hmain.add ((harmonicPower_tendsto_zeta 9 (by omega)).const_mul
    (CoefficientMapFiniteSum.rho n 9 W : ℝ))
  have h := (hB.add hmain').add (actual_shiftedTail_tendsto_zero n W)
  convert h using 1
  · funext T
    rw [actual_finite_odd_identity n T hn W hstrong]
    push_cast
    rfl
  · simp only [exactL, add_zero]

theorem simple_pole_difference_identity (t : ℝ) (ht : 0 < t) (j : ℕ) :
    1 / (t + (j : ℝ)) - 1 / t = -(j : ℝ) / (t * (t + (j : ℝ))) := by
  have hj : 0 < t + (j : ℝ) := add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg j)
  field_simp [ne_of_gt ht, ne_of_gt hj]
  ring

theorem simple_pole_difference_summable (j : ℕ) :
    Summable (fun t : ℕ => 1 / ((t : ℝ) + 1 + (j : ℝ)) - 1 / ((t : ℝ) + 1)) := by
  have hp := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)).comp_injective
    (show Function.Injective (fun t : ℕ => t + 1) from fun a b h => by dsimp at h; omega)
  have hmajorant : Summable (fun t : ℕ => (j : ℝ) * (1 / ((t : ℝ) + 1) ^ 2)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hp.mul_left (j : ℝ)
  apply Summable.of_norm_bounded hmajorant
  intro t
  have ht : 0 < (t : ℝ) + 1 := by positivity
  have hj : 0 < (t : ℝ) + 1 + (j : ℝ) := by positivity
  rw [simple_pole_difference_identity _ ht j, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg j), abs_of_pos (mul_pos ht hj)]
  have hden : ((t : ℝ) + 1) ^ 2 ≤ ((t : ℝ) + 1) * ((t : ℝ) + 1 + (j : ℝ)) := by
    have hjnonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  calc
    _ ≤ (j : ℝ) / ((t : ℝ) + 1) ^ 2 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg j) (pow_pos ht 2) hden
    _ = _ := by ring

theorem shifted_high_order_summable (j s : ℕ) (hs : 2 ≤ s) :
    Summable (fun t : ℕ => 1 / ((t : ℝ) + 1 + (j : ℝ)) ^ s) := by
  have hp := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < s)).comp_injective
    (show Function.Injective (fun t : ℕ => t + 1 + j) from fun a b h => by dsimp at h; omega)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hp

theorem actualSeries_eq_principal_parts (n : ℕ) (W : ℚ[X]) (hproper : ProperMultiplier n W) (t : ℕ) :
    actualSeries n W t = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) / ((t : ℝ) + 1 + (j : ℝ)) ^ s := by
  unfold actualSeries
  rw [CoefficientMapPartialFractions.actual_global_partial_fractions n W hproper]
  · push_cast
    rfl
  · intro k hk
    have ht : (0 : ℚ) < ((t + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos t
    exact ne_of_gt (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg k))

theorem actualSeries_eq_cancelled_principal_parts (n : ℕ) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (t : ℕ) :
    actualSeries n W t =
      (∑ j ∈ range (n + 1), (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) *
        (1 / ((t : ℝ) + 1 + (j : ℝ)) - 1 / ((t : ℝ) + 1))) +
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 2 9,
        (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) / ((t : ℝ) + 1 + (j : ℝ)) ^ s := by
  have hzero : (∑ j ∈ range (n + 1), (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ)) = 0 := by
    have h := rho_one_zero_of_strong_proper n W hstrong
    unfold rho at h
    exact_mod_cast h
  have hcorrection : (∑ j ∈ range (n + 1), (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) *
      (1 / ((t : ℝ) + 1 + (j : ℝ)) - 1 / ((t : ℝ) + 1))) =
      ∑ j ∈ range (n + 1), (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) /
        ((t : ℝ) + 1 + (j : ℝ)) := by
    calc
      _ = ∑ j ∈ range (n + 1), ((CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) /
          ((t : ℝ) + 1 + (j : ℝ)) - (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) /
          ((t : ℝ) + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_div, hzero, zero_div, sub_zero]
  rw [actualSeries_eq_principal_parts n W (strong_proper_implies_proper n W hstrong) t, hcorrection]
  have hsplit (j : ℕ) : (∑ s ∈ Icc 1 9, (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) /
      ((t : ℝ) + 1 + (j : ℝ)) ^ s) =
      (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) / ((t : ℝ) + 1 + (j : ℝ)) +
        ∑ s ∈ Icc 2 9, (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) /
          ((t : ℝ) + 1 + (j : ℝ)) ^ s := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [pow_one, Nat.reduceAdd]
    rw [show (Ico 2 10 : Finset ℕ) = Icc 2 9 by decide]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]

theorem actualSeries_summable (n : ℕ) (W : ℚ[X]) (hstrong : StrongProperMultiplier n W) :
    Summable (actualSeries n W) := by
  have hsimple : Summable (fun t : ℕ => ∑ j ∈ range (n + 1),
      (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) *
        (1 / ((t : ℝ) + 1 + (j : ℝ)) - 1 / ((t : ℝ) + 1))) :=
    summable_sum (fun j hj => (simple_pole_difference_summable j).mul_left
      (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ))
  have hhigher : Summable (fun t : ℕ => ∑ j ∈ range (n + 1), ∑ s ∈ Icc 2 9,
      (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) / ((t : ℝ) + 1 + (j : ℝ)) ^ s) := by
    apply summable_sum
    intro j hj
    apply summable_sum
    intro s hs
    simpa only [mul_one_div] using (shifted_high_order_summable j s (Finset.mem_Icc.mp hs).1).mul_left
      (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ)
  exact (hsimple.add hhigher).congr (fun t => (actualSeries_eq_cancelled_principal_parts n W hstrong t).symm)

theorem actualSeries_norm_summable (n : ℕ) (W : ℚ[X]) (hstrong : StrongProperMultiplier n W) :
    Summable (fun t : ℕ => ‖actualSeries n W t‖) := (actualSeries_summable n W hstrong).norm

theorem actualSeries_partial_sums (n T : ℕ) (W : ℚ[X]) :
    (∑ t ∈ range T, actualSeries n W t) = (CoefficientMapFiniteSum.finiteL n T W : ℝ) := by
  symm
  unfold CoefficientMapFiniteSum.finiteL
  push_cast
  exact sum_Icc_eq_sum_range_successor T (fun t : ℕ => (CoefficientMap.weightedR n W (t : ℚ) : ℝ))

theorem actualSeries_hasSum_exactL (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) : HasSum (actualSeries n W) (exactL n W) := by
  have hsum := actualSeries_summable n W hstrong
  have hlimit : Tendsto (fun T : ℕ => ∑ t ∈ range T, actualSeries n W t) atTop (𝓝 (exactL n W)) := by
    simpa only [actualSeries_partial_sums] using actual_finiteL_tendsto_exactL n hn W hstrong
  have he : (∑' t : ℕ, actualSeries n W t) = exactL n W :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlimit
  simpa only [he] using hsum.hasSum

theorem actualSeries_tsum_exactL (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) : (∑' t : ℕ, actualSeries n W t) = exactL n W :=
  (actualSeries_hasSum_exactL n hn W hstrong).tsum_eq

theorem original_integer_quartic_exact_infinite_L (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (actualSeries n (W.map (Int.castRingHom ℚ))) (exactL n (W.map (Int.castRingHom ℚ))) :=
  actualSeries_hasSum_exactL n hn _ (original_integer_quartic_strong_proper n hn2 hn W hW)

end ZetaNine.CoefficientMapSummation

/- SOURCE module missions.zeta9.formalization.CoefficientMapAggregate; full proof bodies preserved. -/

/-!
The genuine five-dimensional formal map, separate from the full local array.
Its entries use the actual finite harmonic constant and actual local series.
No determinant, rank, kernel triviality or inverse-map conclusion is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapAggregate

open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection

theorem actual_local_coefficient_add (n j s : ℕ) (W V : ℚ[X]) :
    weightedLocalCoefficient n j s (W + V) =
      weightedLocalCoefficient n j s W + weightedLocalCoefficient n j s V := by
  simp [weightedLocalCoefficient, weightedClearedSeries, add_comp, mul_add]

theorem actual_local_coefficient_smul (n j s : ℕ) (a : ℚ) (W : ℚ[X]) :
    weightedLocalCoefficient n j s (a • W) = a * weightedLocalCoefficient n j s W := by
  simp [weightedLocalCoefficient, weightedClearedSeries, smul_comp, smul_eq_mul]

theorem actual_rho_add (n s : ℕ) (W V : ℚ[X]) :
    CoefficientMapFiniteSum.rho n s (W + V) =
      CoefficientMapFiniteSum.rho n s W + CoefficientMapFiniteSum.rho n s V := by
  simp [CoefficientMapFiniteSum.rho, actual_local_coefficient_add, Finset.sum_add_distrib]

theorem actual_rho_smul (n s : ℕ) (a : ℚ) (W : ℚ[X]) :
    CoefficientMapFiniteSum.rho n s (a • W) = a * CoefficientMapFiniteSum.rho n s W := by
  simp [CoefficientMapFiniteSum.rho, actual_local_coefficient_smul, Finset.mul_sum]

theorem actual_constant_add (n : ℕ) (W V : ℚ[X]) :
    CoefficientMapFiniteSum.constantTerm n (W + V) =
      CoefficientMapFiniteSum.constantTerm n W + CoefficientMapFiniteSum.constantTerm n V := by
  simp only [CoefficientMapFiniteSum.constantTerm, actual_local_coefficient_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem actual_constant_smul (n : ℕ) (a : ℚ) (W : ℚ[X]) :
    CoefficientMapFiniteSum.constantTerm n (a • W) = a * CoefficientMapFiniteSum.constantTerm n W := by
  simp [CoefficientMapFiniteSum.constantTerm, actual_local_coefficient_smul, mul_assoc,
    Finset.mul_sum]

theorem aggregate_add (n : ℕ) (W V : ℚ[X]) :
    aggregate n (W + V) = aggregate n W + aggregate n V := by
  funext i
  fin_cases i <;> simp [aggregate, actual_constant_add, actual_rho_add]

theorem aggregate_smul (n : ℕ) (a : ℚ) (W : ℚ[X]) :
    aggregate n (a • W) = a • aggregate n W := by
  funext i
  fin_cases i <;> simp [aggregate, actual_constant_smul, actual_rho_smul, smul_eq_mul]

theorem coordinatePolynomial_add (a b : Fin 5 → ℚ) :
    coordinatePolynomial (a + b) = coordinatePolynomial a + coordinatePolynomial b := by
  simp [coordinatePolynomial, C_add, add_mul, Finset.sum_add_distrib]

theorem coordinatePolynomial_smul (c : ℚ) (a : Fin 5 → ℚ) :
    coordinatePolynomial (c • a) = c • coordinatePolynomial a := by
  simp [coordinatePolynomial, smul_eq_mul, C_mul, mul_assoc, smul_eq_C_mul,
    Finset.mul_sum]

theorem coordinatePolynomial_coeff (a : Fin 5 → ℚ) (i : Fin 5) :
    (coordinatePolynomial a).coeff i.val = a i := by
  classical
  simp only [coordinatePolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have h : i.val ≠ j.val := by intro he; exact hji (Fin.ext he.symm)
    simp [h]
  · simp

theorem coordinatePolynomial_coeff_above (a : Fin 5 → ℚ) (k : ℕ) (hk : 5 ≤ k) :
    (coordinatePolynomial a).coeff k = 0 := by
  classical
  simp only [coordinatePolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro i hi
  have h : k ≠ i.val := by have := i.isLt; omega
  simp [h]

theorem coordinatePolynomial_natDegree_le (a : Fin 5 → ℚ) :
    (coordinatePolynomial a).natDegree ≤ 4 := by
  unfold coordinatePolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have h : (C (a i) * X ^ i.val : ℚ[X]).natDegree ≤
      (C (a i) : ℚ[X]).natDegree + (X ^ i.val : ℚ[X]).natDegree := natDegree_mul_le
  simp only [natDegree_C, natDegree_X_pow, zero_add] at h
  exact h.trans (by have := i.isLt; omega)

theorem coordinates_restore (a : Fin 5 → ℚ) :
    polynomialCoordinates (coordinatePolynomial a) = a := by
  funext i
  exact coordinatePolynomial_coeff a i

theorem polynomial_restore (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    coordinatePolynomial (polynomialCoordinates W) = W := by
  ext k
  by_cases hk : k < 5
  · exact coordinatePolynomial_coeff (polynomialCoordinates W) ⟨k, hk⟩
  · rw [coordinatePolynomial_coeff_above _ k (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem coordinatePolynomial_injective : Function.Injective coordinatePolynomial := by
  intro a b hab
  simpa only [coordinates_restore] using congrArg polynomialCoordinates hab

theorem quartic_aggregate_is_actual (n : ℕ) (a : Fin 5 → ℚ) :
    quarticAggregateLinearMap n a = aggregate n (coordinatePolynomial a) := rfl

theorem aggregate_zero_iff (n : ℕ) (W : ℚ[X]) :
    aggregate n W = 0 ↔ CoefficientMapFiniteSum.constantTerm n W = 0 ∧
      CoefficientMapFiniteSum.rho n 3 W = 0 ∧ CoefficientMapFiniteSum.rho n 5 W = 0 ∧
      CoefficientMapFiniteSum.rho n 7 W = 0 ∧ CoefficientMapFiniteSum.rho n 9 W = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3, congrFun h 4⟩
  · rintro ⟨hB, h3, h5, h7, h9⟩
    funext i
    fin_cases i <;> simp [aggregate, hB, h3, h5, h7, h9]

theorem aggregate_zero_all_rho (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) : CoefficientMapFiniteSum.rho n s W = 0 := by
  obtain ⟨hB, h3, h5, h7, h9⟩ := (aggregate_zero_iff n W).mp hzero
  have h1 : CoefficientMapFiniteSum.rho n 1 W = 0 := rho_one_zero_of_strong_proper n W hstrong
  have h2 : CoefficientMapFiniteSum.rho n 2 W = 0 := rho_even_order_zero n 2 hn W (by omega) (by omega) (by norm_num)
  have h4 : CoefficientMapFiniteSum.rho n 4 W = 0 := rho_even_order_zero n 4 hn W (by omega) (by omega) (by norm_num)
  have h6 : CoefficientMapFiniteSum.rho n 6 W = 0 := rho_even_order_zero n 6 hn W (by omega) (by omega) (by norm_num)
  have h8 : CoefficientMapFiniteSum.rho n 8 W = 0 := rho_even_order_zero n 8 hn W (by omega) (by omega) (by norm_num)
  interval_cases s <;> assumption

theorem aggregate_zero_exactL (n : ℕ) (W : ℚ[X]) (hzero : aggregate n W = 0) :
    CoefficientMapSummation.exactL n W = 0 := by
  obtain ⟨hB, h3, h5, h7, h9⟩ := (aggregate_zero_iff n W).mp hzero
  simp [CoefficientMapSummation.exactL, hB, h3, h5, h7, h9]

end ZetaNine.CoefficientMapAggregate

/- SOURCE module missions.zeta9.formalization.CoefficientMapTelescoper; full proof bodies preserved. -/

/-!
Actual cumulative partial fractions for a zero vector of the five-dimensional map.
The telescoper is built from the true local coefficients, not assumed to exist.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Topology
open Finset Polynomial Filter

namespace ZetaNine.CoefficientMapTelescoper

open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate

theorem prefixSum_succ (c : ℕ → ℚ) (j : ℕ) :
    prefixSum c (j + 1) = prefixSum c j + c (j + 1) := by
  unfold prefixSum
  exact Finset.sum_range_succ _ _

theorem finite_cumulative_difference (n : ℕ) (c f : ℕ → ℚ) :
    (∑ j ∈ range n, prefixSum c j * (f j - f (j + 1))) =
      (∑ j ∈ range (n + 1), c j * f j) - prefixSum c n * f n := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    rw [Finset.sum_range_succ (fun j => prefixSum c j * (f j - f (j + 1))) n, ih,
      Finset.sum_range_succ (fun j => c j * f j) (n + 1), prefixSum_succ]
    ring

theorem cumulativeCoefficient_succ (n j s : ℕ) (W : ℚ[X]) :
    cumulativeCoefficient n (j + 1) s W = cumulativeCoefficient n j s W +
      weightedLocalCoefficient n (j + 1) s W := prefixSum_succ _ j

theorem cumulativeCoefficient_last_zero (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) : cumulativeCoefficient n n s W = 0 :=
  aggregate_zero_all_rho n hn W hstrong hzero s hs1 hs9

theorem telescoper_as_sum_over_orders (n : ℕ) (W : ℚ[X]) (t : ℚ) :
    telescoper n W t = ∑ s ∈ Icc 1 9, ∑ j ∈ range n,
      cumulativeCoefficient n j s W / (t + (j : ℚ)) ^ s := Finset.sum_comm

theorem telescoper_difference_principal_parts (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (t : ℚ) :
    telescoper n W t - telescoper n W (t + 1) =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
  rw [telescoper_as_sum_over_orders, telescoper_as_sum_over_orders, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ s ∈ Icc 1 9, ∑ j ∈ range n, cumulativeCoefficient n j s W *
        (1 / (t + (j : ℚ)) ^ s - 1 / (t + ((j + 1 : ℕ) : ℚ)) ^ s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hshift : (t + 1) + (j : ℚ) = t + ((j + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [hshift]
      ring
    _ = ∑ s ∈ Icc 1 9, ∑ j ∈ range (n + 1),
        weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
      apply Finset.sum_congr rfl
      intro s hs
      have h := finite_cumulative_difference n (fun j => weightedLocalCoefficient n j s W)
        (fun j => 1 / (t + (j : ℚ)) ^ s)
      change (∑ j ∈ range n, prefixSum (fun j => weightedLocalCoefficient n j s W) j *
        (1 / (t + (j : ℚ)) ^ s - 1 / (t + ((j + 1 : ℕ) : ℚ)) ^ s)) = _
      rw [h]
      have htotal : prefixSum (fun j => weightedLocalCoefficient n j s W) n = 0 :=
        cumulativeCoefficient_last_zero n hn W hstrong hzero s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
      simp only [htotal, mul_one_div, zero_div, sub_zero]
    _ = _ := Finset.sum_comm

theorem actual_weightedR_is_difference (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    CoefficientMap.weightedR n W t = telescoper n W t - telescoper n W (t + 1) := by
  rw [telescoper_difference_principal_parts n hn W hstrong hzero t]
  exact CoefficientMapPartialFractions.actual_global_partial_fractions n W
    (strong_proper_implies_proper n W hstrong) t hregular

theorem telescoper_positive_tendsto_zero (n : ℕ) (W : ℚ[X]) :
    Tendsto (fun T : ℕ => (telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (range n) (fun j hj => tendsto_finsetSum (Icc 1 9) (fun s hs =>
    (CoefficientMapSummation.shifted_reciprocal_tendsto_zero s (j + 1) (Finset.mem_Icc.mp hs).1).const_mul
      (cumulativeCoefficient n j s W : ℝ)))
  have he : (fun T : ℕ => (telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) =
      (fun T : ℕ => ∑ j ∈ range n, ∑ s ∈ Icc 1 9,
        (cumulativeCoefficient n j s W : ℝ) * (1 / ((T : ℝ) + ((j + 1 : ℕ) : ℝ)) ^ s)) := by
    funext T
    unfold telescoper
    push_cast
    simp only [mul_one_div, add_left_comm, add_comm]
  rw [he]
  simpa only [mul_zero, Finset.sum_const_zero] using h

theorem finite_sum_is_telescoper_boundary (n T : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    CoefficientMapFiniteSum.finiteL n T W = telescoper n W 1 - telescoper n W ((T + 1 : ℕ) : ℚ) := by
  induction T with
  | zero => simp [CoefficientMapFiniteSum.finiteL]
  | succ T ih =>
    have hstep : CoefficientMapFiniteSum.finiteL n (T + 1) W =
        CoefficientMapFiniteSum.finiteL n T W + CoefficientMap.weightedR n W ((T + 1 : ℕ) : ℚ) := by
      unfold CoefficientMapFiniteSum.finiteL
      exact Finset.sum_Icc_succ_top (by omega) _
    rw [hstep, ih, actual_weightedR_is_difference n hn W hstrong hzero]
    · have he : ((T + 1 : ℕ) : ℚ) + 1 = ((T + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [he]
      ring
    · intro k hk
      exact ne_of_gt (add_pos_of_pos_of_nonneg (by positivity) (Nat.cast_nonneg k))

theorem telescoper_at_one_zero (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) : telescoper n W 1 = 0 := by
  have hfinite := CoefficientMapSummation.actual_finiteL_tendsto_exactL n hn W hstrong
  rw [aggregate_zero_exactL n W hzero] at hfinite
  have hboundary := (tendsto_const_nhds (x := (telescoper n W 1 : ℝ))).sub
    (telescoper_positive_tendsto_zero n W)
  have he : (fun T : ℕ => (CoefficientMapFiniteSum.finiteL n T W : ℝ)) =
      (fun T : ℕ => (telescoper n W 1 : ℝ) - (telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) := by
    funext T
    rw [finite_sum_is_telescoper_boundary n T hn W hstrong hzero]
    push_cast
    rfl
  rw [he] at hfinite
  have h := tendsto_nhds_unique hfinite hboundary
  simp only [sub_zero] at h
  exact_mod_cast h.symm

theorem actual_weightedR_positive_zero (n k : ℕ) (W : ℚ[X]) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.weightedR n W (k : ℚ) = 0 := by
  have hprod : (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (show k - 1 < n by omega))
    have he : k - 1 + 1 = k := by omega
    exact sub_eq_zero.mpr (by exact_mod_cast he.symm)
  simp [CoefficientMap.weightedR, CoefficientMap.actualR, CoefficientMap.numerator, hprod]

theorem telescoper_positive_zeros (n k : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (hk1 : 1 ≤ k) (hkn : k ≤ n + 1) : telescoper n W (k : ℚ) = 0 := by
  have hzeros : ∀ l ≤ n, telescoper n W ((l + 1 : ℕ) : ℚ) = 0 := by
    intro l
    induction l with
    | zero => intro hl; exact telescoper_at_one_zero n hn W hstrong hzero
    | succ l ih =>
      intro hl
      have hprev := ih (by omega)
      have hdiff := actual_weightedR_is_difference n hn W hstrong hzero ((l + 1 : ℕ) : ℚ)
        (by intro k hk; exact ne_of_gt (add_pos_of_pos_of_nonneg (by positivity) (Nat.cast_nonneg k)))
      rw [actual_weightedR_positive_zero n (l + 1) W (by omega) (by omega), hprev] at hdiff
      have he : ((l + 1 : ℕ) : ℚ) + 1 = ((l + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [he] at hdiff
      linarith
  have he : k - 1 + 1 = k := by omega
  simpa only [he] using hzeros (k - 1) (by omega)

theorem cumulativeCoefficient_reflection (n j s : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (hj : j < n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    cumulativeCoefficient n (n - 1 - j) s W = (-1 : ℚ) ^ s * cumulativeCoefficient n j s W := by
  induction j with
  | zero =>
    have hn1 : 1 ≤ n := by omega
    have hlast := cumulativeCoefficient_last_zero n hn W hstrong hzero s hs1 hs9
    have hstep := cumulativeCoefficient_succ n (n - 1) s W
    rw [show n - 1 + 1 = n by omega, hlast] at hstep
    have hreflection := local_coefficient_reflection n 0 s hn W (by omega) hs1 hs9
    simp only [Nat.sub_zero, pow_succ] at hreflection
    simp only [Nat.sub_zero]
    have hfirst : cumulativeCoefficient n 0 s W = weightedLocalCoefficient n 0 s W := by
      simp [cumulativeCoefficient, prefixSum]
    rw [hfirst]
    rw [hreflection] at hstep
    nlinarith
  | succ j ih =>
    have hprev := ih (by omega)
    have hstep := cumulativeCoefficient_succ n (n - 1 - (j + 1)) s W
    rw [show n - 1 - (j + 1) + 1 = n - 1 - j by omega, hprev] at hstep
    have hreflection := local_coefficient_reflection n (j + 1) s hn W (by omega) hs1 hs9
    rw [show n - (j + 1) = n - 1 - j by omega] at hreflection
    rw [hreflection, pow_succ] at hstep
    rw [cumulativeCoefficient_succ]
    nlinarith

theorem telescoper_reflection (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (t : ℚ) :
    telescoper n W (1 - (n : ℚ) - t) = telescoper n W t := by
  have hreverse := sum_reverse_range (n - 1)
    (fun j => ∑ s ∈ Icc 1 9,
      cumulativeCoefficient n j s W / ((1 - (n : ℚ) - t) + (j : ℚ)) ^ s)
  rw [show n - 1 + 1 = n by omega] at hreverse
  unfold telescoper
  rw [← hreverse]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  apply Finset.sum_congr rfl
  intro s hs
  rw [cumulativeCoefficient_reflection n j s hn W hstrong hzero hjn
    (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2]
  have he : (1 - (n : ℚ) - t) + ((n - 1 - j : ℕ) : ℚ) = -(t + (j : ℚ)) := by
    have hnsub : (n - 1 - j : ℕ) + (j + 1) = n := by omega
    have hc : ((n - 1 - j : ℕ) : ℚ) + ((j : ℚ) + 1) = (n : ℚ) := by exact_mod_cast hnsub
    linarith
  rw [he, neg_pow (t + (j : ℚ))]
  exact mul_div_mul_left _ _ (pow_ne_zero s (by norm_num : (-1 : ℚ) ≠ 0))

theorem telescoper_negative_zeros (n k : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (hk : k ≤ n) :
    telescoper n W (-(n : ℚ) - (k : ℚ)) = 0 := by
  have hreflection := telescoper_reflection n hn1 hn W hstrong hzero (-(n : ℚ) - (k : ℚ))
  have he : 1 - (n : ℚ) - (-(n : ℚ) - (k : ℚ)) = ((k + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [he, telescoper_positive_zeros n (k + 1) hn W hstrong hzero (by omega) (by omega)] at hreflection
  exact hreflection.symm

theorem cleared_term_division (n j s : ℕ) (a t : ℚ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    (a * (CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t ^ 9 *
      (t + (j : ℚ)) ^ (9 - s)) / (polePolynomial n).eval t ^ 9 = a / (t + (j : ℚ)) ^ s := by
  apply (div_eq_div_iff
    (pow_ne_zero _ (CoefficientMapPartialFractions.polePolynomial_eval_ne_zero n t hregular))
    (pow_ne_zero _ (hregular j hj))).mpr
  rw [CoefficientMapPartialFractions.polePolynomial_eval_factor n j t hj, mul_pow]
  have he : (t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s = (t + (j : ℚ)) ^ 9 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = a * (CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t ^ 9 *
      ((t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s) := by ring
    _ = _ := by rw [he]; ring

theorem telescoper_actual_rational_representation (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) (t : ℚ)
    (hregular : ∀ k < n, t + (k : ℚ) ≠ 0) :
    telescoper n W t = (telescoperNumerator n W).eval t / (polePolynomial (n - 1)).eval t ^ 9 := by
  symm
  simp only [telescoperNumerator, partialBasis, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  simpa only [mul_assoc] using cleared_term_division (n - 1) j s (cumulativeCoefficient n j s W) t
    (by have := Finset.mem_range.mp hj; omega) (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
    (by intro k hk; exact hregular k (by omega))

theorem telescoperNumerator_natDegree_le (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) :
    (telescoperNumerator n W).natDegree ≤ 9 * n - 1 := by
  unfold telescoperNumerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  have h : (C (cumulativeCoefficient n j s W) * partialBasis (n - 1) j s).natDegree ≤
      (C (cumulativeCoefficient n j s W)).natDegree + (partialBasis (n - 1) j s).natDegree :=
    Polynomial.natDegree_mul_le
  rw [Polynomial.natDegree_C, zero_add,
    partialBasis_natDegree (n - 1) j s (by have := Finset.mem_range.mp hj; omega)] at h
  have horder := Finset.mem_Icc.mp hs
  omega

theorem rootNode_injective (n : ℕ) : Function.Injective (rootNode n) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      congr 1
      apply Fin.ext
      have he : (a.val : ℚ) = (b.val : ℚ) := by simpa [rootNode] using h
      exact_mod_cast he
    | inr b =>
      have ha : (0 : ℚ) ≤ (a.val : ℚ) := Nat.cast_nonneg _
      have hb : (0 : ℚ) ≤ (b.val : ℚ) := Nat.cast_nonneg _
      have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg _
      simp only [rootNode] at h
      linarith
  | inr a =>
    cases b with
    | inl b =>
      have ha : (0 : ℚ) ≤ (a.val : ℚ) := Nat.cast_nonneg _
      have hb : (0 : ℚ) ≤ (b.val : ℚ) := Nat.cast_nonneg _
      have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg _
      simp only [rootNode] at h
      linarith
    | inr b =>
      congr 1
      apply Fin.ext
      have he : (a.val : ℚ) = (b.val : ℚ) := by simp only [rootNode] at h; linarith
      exact_mod_cast he

theorem rootPolynomial_monic (n : ℕ) : (rootPolynomial n).Monic := by
  unfold rootPolynomial
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact Polynomial.monic_X_sub_C _

theorem rootPolynomial_eq_explicit_products (n : ℕ) :
    rootPolynomial n =
      (∏ k ∈ range (n + 1), (X - C ((k : ℚ) + 1))) *
      (∏ k ∈ range (n + 1), (X + C (n : ℚ) + C (k : ℚ))) := by
  unfold rootPolynomial
  rw [Fintype.prod_sum_type]
  simp only [rootNode]
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => (X - C ((k : ℚ) + 1) : ℚ[X])) (n + 1),
    Fin.prod_univ_eq_prod_range (fun k : ℕ => (X - C (-(n : ℚ) - (k : ℚ)) : ℚ[X])) (n + 1)]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp only [map_sub, map_neg]
  ring

theorem rootPolynomial_natDegree (n : ℕ) : (rootPolynomial n).natDegree = 2 * n + 2 := by
  unfold rootPolynomial
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i hi => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C]
  simp
  omega

theorem telescoperNumerator_zero_at_nodes (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (i : Fin (n + 1) ⊕ Fin (n + 1)) : (telescoperNumerator n W).eval (rootNode n i) = 0 := by
  have hregular : ∀ k < n, rootNode n i + (k : ℚ) ≠ 0 := by
    intro k hk
    cases i with
    | inl l =>
      simp only [rootNode]
      exact ne_of_gt (by positivity)
    | inr l =>
      simp only [rootNode]
      have hkn : (k : ℚ) < (n : ℚ) := by exact_mod_cast hk
      have hl : (0 : ℚ) ≤ (l.val : ℚ) := Nat.cast_nonneg _
      exact ne_of_lt (by linarith)
  have hvalue : telescoper n W (rootNode n i) = 0 := by
    cases i with
    | inl k =>
      simpa only [rootNode, Nat.cast_add, Nat.cast_one] using
        telescoper_positive_zeros n (k.val + 1) hn W hstrong hzero (by omega) (by have := k.isLt; omega)
    | inr k =>
      exact telescoper_negative_zeros n k.val hn1 hn W hstrong hzero (by have := k.isLt; omega)
  have hrep := telescoper_actual_rational_representation n hn1 W (rootNode n i) hregular
  have hden : (polePolynomial (n - 1)).eval (rootNode n i) ^ 9 ≠ 0 :=
    pow_ne_zero _ (CoefficientMapPartialFractions.polePolynomial_eval_ne_zero (n - 1) _
      (by intro k hk; exact hregular k (by omega)))
  rw [hvalue] at hrep
  have hmult := congrArg (fun x : ℚ => x * (polePolynomial (n - 1)).eval (rootNode n i) ^ 9) hrep
  rw [div_mul_cancel₀ _ hden] at hmult
  simpa only [zero_mul] using hmult.symm

theorem all_kernel_nodes_divide_telescoperNumerator (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    rootPolynomial n ∣ telescoperNumerator n W := by
  unfold rootPolynomial
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact Polynomial.pairwise_coprime_X_sub_C (rootNode_injective n) hab
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact telescoperNumerator_zero_at_nodes n hn1 hn W hstrong hzero i

theorem actual_polynomial_quotient_degree_bound (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    ∃ H : ℚ[X], telescoperNumerator n W = rootPolynomial n * H ∧ H.natDegree ≤ 7 * n - 3 := by
  obtain ⟨H, hH⟩ := all_kernel_nodes_divide_telescoperNumerator n hn1 hn W hstrong hzero
  refine ⟨H, hH, ?_⟩
  by_cases hH0 : H = 0
  · simp [hH0]
  · have hdegree := congrArg Polynomial.natDegree hH
    rw [Polynomial.natDegree_mul (rootPolynomial_monic n).ne_zero hH0, rootPolynomial_natDegree] at hdegree
    have hbound := telescoperNumerator_natDegree_le n hn1 W
    omega

end ZetaNine.CoefficientMapTelescoper

/- SOURCE module missions.zeta9.formalization.CoefficientMapShiftDegree; full proof bodies preserved. -/

/-! The actual polynomial shift operator used by the original quartic kernel route.
This file proves its coefficient obstruction; its relation to the genuine rational
telescoper is established separately. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Polynomial

namespace ZetaNine.CoefficientMapShiftDegree

theorem actual_nextCoeff_mul (P H : ℚ[X]) :
    (P * H).nextCoeff = P.nextCoeff * H.leadingCoeff + P.leadingCoeff * H.nextCoeff := by
  rw [← coeff_one_reverse, reverse_mul_of_domain, mul_coeff_one]
  simp only [coeff_zero_reverse, coeff_one_reverse]
  ring

theorem actual_shift_nextCoeff (H : ℚ[X]) :
    (H.comp (X + C 1)).nextCoeff = H.nextCoeff + (H.natDegree : ℚ) * H.leadingCoeff := by
  change (taylor 1 H).nextCoeff = _
  by_cases hd : H.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hd]
    simp
  have hdpos : 0 < H.natDegree := Nat.pos_of_ne_zero hd
  rw [nextCoeff_of_natDegree_pos (by simpa using hdpos), natDegree_taylor, taylor_coeff]
  have hdeg : (hasseDeriv (H.natDegree - 1) H).natDegree < 2 := by
    have h := natDegree_hasseDeriv_le H (H.natDegree - 1)
    omega
  rw [eval_eq_sum_range' hdeg 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_pow, mul_one,
    hasseDeriv_coeff]
  have hadd : 1 + (H.natDegree - 1) = H.natDegree := by omega
  have hchoose : H.natDegree.choose (H.natDegree - 1) = H.natDegree := by
    have h := Nat.choose_succ_self_right (H.natDegree - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ H.natDegree)] using h
  rw [hadd, Nat.choose_self, hchoose, Nat.cast_one, one_mul,
    ← nextCoeff_of_natDegree_pos hdpos, coeff_natDegree]

theorem shiftA_monic (n : ℕ) : (shiftA n).Monic :=
  (monic_X_sub_C _).mul ((monic_X_add_C _).pow 10)

theorem shiftB_monic (n : ℕ) : (shiftB n).Monic :=
  (monic_X.pow 10).mul (monic_X_add_C _)

theorem shiftA_natDegree (n : ℕ) : (shiftA n).natDegree = 11 := by
  rw [shiftA, natDegree_mul (monic_X_sub_C _).ne_zero ((monic_X_add_C _).pow 10).ne_zero]
  simp only [natDegree_X_sub_C, natDegree_pow, natDegree_X_add_C]

theorem shiftB_natDegree (n : ℕ) : (shiftB n).natDegree = 11 := by
  rw [shiftB, natDegree_mul (monic_X.pow 10).ne_zero (monic_X_add_C _).ne_zero]
  simp only [natDegree_pow, natDegree_X, natDegree_X_add_C]

theorem shiftA_nextCoeff (n : ℕ) : (shiftA n).nextCoeff = 9 * (n : ℚ) - 1 := by
  unfold shiftA
  rw [Monic.nextCoeff_mul (monic_X_sub_C _) ((monic_X_add_C _).pow 10),
    Monic.nextCoeff_pow (monic_X_add_C _) 10, nextCoeff_X_sub_C, nextCoeff_X_add_C]
  simp only [nsmul_eq_mul]
  ring

theorem shiftB_nextCoeff (n : ℕ) : (shiftB n).nextCoeff = 2 * (n : ℚ) + 1 := by
  have hX : (X : ℚ[X]).nextCoeff = 0 := by norm_num [nextCoeff]
  unfold shiftB
  rw [Monic.nextCoeff_mul (monic_X.pow 10) (monic_X_add_C _),
    Monic.nextCoeff_pow monic_X 10, hX, nextCoeff_X_add_C]
  simp

theorem actual_shift_difference_coefficient (n : ℕ) (H : ℚ[X]) (hH : H ≠ 0) :
    (shiftDifference n H).coeff (H.natDegree + 10) =
      (7 * (n : ℚ) - 2 - (H.natDegree : ℚ)) * H.leadingCoeff := by
  have hAH : (shiftA n * H).natDegree = 11 + H.natDegree := by
    rw [(shiftA_monic n).natDegree_mul' hH, shiftA_natDegree]
  have hHs : H.comp (X + C 1) ≠ 0 := by
    intro h
    exact hH ((taylor_eq_zero (r := (1 : ℚ)) (f := H)).mp h)
  have hHsdeg : (H.comp (X + C 1)).natDegree = H.natDegree := natDegree_taylor H 1
  have hHslead : (H.comp (X + C 1)).leadingCoeff = H.leadingCoeff := leadingCoeff_taylor 1 H
  have hBH : (shiftB n * H.comp (X + C 1)).natDegree = 11 + H.natDegree := by
    rw [(shiftB_monic n).natDegree_mul' hHs, shiftB_natDegree, hHsdeg]
  have hfirst : (shiftA n * H).coeff (H.natDegree + 10) =
      (9 * (n : ℚ) - 1) * H.leadingCoeff + H.nextCoeff := by
    have hnext := nextCoeff_of_natDegree_pos (p := shiftA n * H) (by omega)
    rw [hAH] at hnext
    rw [show 11 + H.natDegree - 1 = H.natDegree + 10 by omega] at hnext
    rw [← hnext, actual_nextCoeff_mul, shiftA_nextCoeff, (shiftA_monic n).leadingCoeff,
      one_mul]
  have hsecond : (shiftB n * H.comp (X + C 1)).coeff (H.natDegree + 10) =
      (2 * (n : ℚ) + 1) * H.leadingCoeff +
        (H.nextCoeff + (H.natDegree : ℚ) * H.leadingCoeff) := by
    have hnext := nextCoeff_of_natDegree_pos (p := shiftB n * H.comp (X + C 1)) (by omega)
    rw [hBH] at hnext
    rw [show 11 + H.natDegree - 1 = H.natDegree + 10 by omega] at hnext
    rw [← hnext, actual_nextCoeff_mul, shiftB_nextCoeff, (shiftB_monic n).leadingCoeff,
      one_mul, hHslead, actual_shift_nextCoeff]
  rw [shiftDifference, coeff_sub, hfirst, hsecond]
  ring

theorem actual_shift_difference_coefficient_ne_zero (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hH : H ≠ 0) (hdeg : H.natDegree ≤ 7 * n - 3) :
    (shiftDifference n H).coeff (H.natDegree + 10) ≠ 0 := by
  rw [actual_shift_difference_coefficient n H hH]
  have hb : H.natDegree + 3 ≤ 7 * n := by omega
  have hbq : (H.natDegree : ℚ) + 3 ≤ 7 * (n : ℚ) := by exact_mod_cast hb
  apply mul_ne_zero
  · have hpos : 0 < 7 * (n : ℚ) - 2 - (H.natDegree : ℚ) := by linarith
    exact ne_of_gt hpos
  · exact leadingCoeff_ne_zero.mpr hH

theorem actual_shift_difference_degree_lower_bound (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hH : H ≠ 0) (hdeg : H.natDegree ≤ 7 * n - 3) :
    H.natDegree + 10 ≤ (shiftDifference n H).natDegree :=
  le_natDegree_of_ne_zero (actual_shift_difference_coefficient_ne_zero n hn H hH hdeg)

theorem actual_shift_difference_small_degree_implies_zero (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hdeg : H.natDegree ≤ 7 * n - 3)
    (hsmall : (shiftDifference n H).natDegree ≤ 8) : H = 0 := by
  by_contra hH
  have h := actual_shift_difference_degree_lower_bound n hn H hH hdeg
  omega

end ZetaNine.CoefficientMapShiftDegree

/- SOURCE module missions.zeta9.formalization.CoefficientMapKernelBridge; full proof bodies preserved. -/

/-!
The genuine P0, R*A and shift identities linking the actual telescoper quotient
to a polynomial difference. No polynomial difference or trivial-kernel input is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapKernelBridge

open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapAggregate CoefficientMapTelescoper

theorem finite_product_shift_identity (n : ℕ) (f : ℕ → ℚ) :
    (∏ k ∈ range n, f (k + 1)) * f 0 = (∏ k ∈ range n, f k) * f n := by
  have h := Finset.prod_range_succ' f n
  rw [Finset.prod_range_succ] at h
  simpa only [mul_comm] using h.symm

theorem positiveProduct_shift (n : ℕ) (t : ℚ) :
    positiveProduct n (t + 1) * (t - (n : ℚ)) = t * positiveProduct n t := by
  have h := finite_product_shift_identity n (fun k => t - (k : ℚ))
  have he : positiveProduct n (t + 1) = ∏ k ∈ range n, (t - (k : ℚ)) := by
    unfold positiveProduct
    apply Finset.prod_congr rfl
    intro k hk
    ring
  rw [he]
  simpa only [positiveProduct, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, mul_comm] using h.symm

theorem negativeProduct_shift (n : ℕ) (t : ℚ) :
    negativeProduct n (t + 1) * (t + (n : ℚ) + 1) =
      negativeProduct n t * (t + 2 * (n : ℚ) + 1) := by
  have h := finite_product_shift_identity n (fun k => t + (n : ℚ) + ((k : ℚ) + 1))
  have he : (∏ k ∈ range n, (t + (n : ℚ) + (((k + 1 : ℕ) : ℚ) + 1))) =
      negativeProduct n (t + 1) := by
    unfold negativeProduct
    apply Finset.prod_congr rfl
    intro k hk
    push_cast
    ring
  rw [he] at h
  have hend : t + (n : ℚ) + ((n : ℚ) + 1) = t + 2 * (n : ℚ) + 1 := by ring
  simpa only [negativeProduct, Nat.cast_zero, zero_add, hend] using h

theorem numerator_shift_identity (n : ℕ) (t : ℚ) :
    CoefficientMap.numerator n (t + 1) * (t - (n : ℚ)) * (t + (n : ℚ) + 1) =
      CoefficientMap.numerator n t * t * (t + 2 * (n : ℚ) + 1) := by
  change (n.factorial : ℚ) ^ 7 * positiveProduct n (t + 1) * negativeProduct n (t + 1) *
      (t - (n : ℚ)) * (t + (n : ℚ) + 1) =
    (n.factorial : ℚ) ^ 7 * positiveProduct n t * negativeProduct n t * t * (t + 2 * (n : ℚ) + 1)
  calc
    _ = (n.factorial : ℚ) ^ 7 * (positiveProduct n (t + 1) * (t - (n : ℚ))) *
        (negativeProduct n (t + 1) * (t + (n : ℚ) + 1)) := by ring
    _ = _ := by rw [positiveProduct_shift, negativeProduct_shift]; ring

theorem poleProduct_shift_identity (n : ℕ) (t : ℚ) :
    CoefficientMap.poleProduct n (t + 1) * t = CoefficientMap.poleProduct n t * (t + (n : ℚ) + 1) := by
  have h := finite_product_shift_identity (n + 1) (fun k => t + (k : ℚ))
  simpa only [CoefficientMap.poleProduct, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero,
    add_assoc, add_comm, add_left_comm] using h

theorem actual_R_shift_A_equals_R_B (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0)
    (hregular1 : ∀ k ≤ n, (t + 1) + (k : ℚ) ≠ 0) :
    CoefficientMap.actualR n (t + 1) * aValue n (t + 1) = CoefficientMap.actualR n t * bValue n t := by
  have hden := CoefficientMap.poleProduct_ne_zero n t hregular
  have hden1 := CoefficientMap.poleProduct_ne_zero n (t + 1) hregular1
  have hnum := numerator_shift_identity n t
  have hpole := congrArg (fun x : ℚ => x ^ 9) (poleProduct_shift_identity n t)
  simp only [mul_pow] at hpole
  unfold CoefficientMap.actualR aValue bValue
  field_simp [hden, hden1]
  calc
    _ = (CoefficientMap.numerator n (t + 1) * (t - (n : ℚ)) * (t + (n : ℚ) + 1)) *
        ((t + (n : ℚ) + 1) ^ 9 * CoefficientMap.poleProduct n t ^ 9) := by ring
    _ = (CoefficientMap.numerator n t * t * (t + 2 * (n : ℚ) + 1)) *
        (CoefficientMap.poleProduct n (t + 1) ^ 9 * t ^ 9) := by rw [hnum, hpole]; ring
    _ = _ := by ring

theorem rootPolynomial_numerator_factor (n : ℕ) (t : ℚ) :
    (n.factorial : ℚ) ^ 7 * (rootPolynomial n).eval t =
      CoefficientMap.numerator n t * (t - (n : ℚ) - 1) * (t + (n : ℚ)) := by
  rw [rootPolynomial_eq_explicit_products]
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  rw [Finset.prod_range_succ (fun k : ℕ => t - ((k : ℚ) + 1)) n,
    Finset.prod_range_succ' (fun k : ℕ => t + (n : ℚ) + (k : ℚ)) n]
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  change (n.factorial : ℚ) ^ 7 * ((positiveProduct n t * (t - ((n : ℚ) + 1))) *
      (negativeProduct n t * (t + (n : ℚ)))) = _
  change _ = (n.factorial : ℚ) ^ 7 * positiveProduct n t * negativeProduct n t *
    (t - (n : ℚ) - 1) * (t + (n : ℚ))
  ring

theorem poleProduct_last_factor (n : ℕ) (hn1 : 1 ≤ n) (t : ℚ) :
    CoefficientMap.poleProduct n t = (polePolynomial (n - 1)).eval t * (t + (n : ℚ)) := by
  rw [CoefficientMapPartialFractions.polePolynomial_eval]
  unfold CoefficientMap.poleProduct
  rw [show n - 1 + 1 = n by omega]
  exact Finset.prod_range_succ _ _

theorem actual_R_A_equals_Pzero (n : ℕ) (hn1 : 1 ≤ n) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    CoefficientMap.actualR n t * aValue n t =
      (n.factorial : ℚ) ^ 7 * (rootPolynomial n).eval t / (polePolynomial (n - 1)).eval t ^ 9 := by
  have hden := CoefficientMapPartialFractions.polePolynomial_eval_ne_zero (n - 1) t
    (by intro k hk; exact hregular k (by omega))
  have hlast := hregular n (by omega)
  rw [rootPolynomial_numerator_factor]
  unfold CoefficientMap.actualR aValue
  rw [poleProduct_last_factor n hn1, mul_pow]
  field_simp [hden, hlast]

theorem telescoper_quotient_as_R_A (n : ℕ) (hn1 : 1 ≤ n) (W H : ℚ[X])
    (hH : telescoperNumerator n W = rootPolynomial n * H) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    telescoper n W t = CoefficientMap.actualR n t * aValue n t * H.eval t / (n.factorial : ℚ) ^ 7 := by
  have hfactor : (n.factorial : ℚ) ^ 7 ≠ 0 := pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
  rw [telescoper_actual_rational_representation n hn1 W t
    (by intro k hk; exact hregular k (by omega)), hH, Polynomial.eval_mul,
    actual_R_A_equals_Pzero n hn1 t hregular]
  field_simp [hfactor]

theorem actual_R_ne_zero_above_n (n : ℕ) (t : ℚ) (ht : (n : ℚ) < t) : CoefficientMap.actualR n t ≠ 0 := by
  have ht0 : (0 : ℚ) < t := lt_of_le_of_lt (Nat.cast_nonneg n) ht
  apply div_ne_zero
  · unfold CoefficientMap.numerator
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
      · apply Finset.prod_ne_zero_iff.mpr
        intro k hk
        have hk1 : (k : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
        exact ne_of_gt (by linarith)
    · apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact ne_of_gt (by positivity)
  · exact pow_ne_zero _ (CoefficientMap.poleProduct_ne_zero n t
      (by intro k hk; exact ne_of_gt (add_pos_of_pos_of_nonneg ht0 (Nat.cast_nonneg k))))

theorem kernel_actual_polynomial_relation (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W H : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (hH : telescoperNumerator n W = rootPolynomial n * H) :
    C ((n.factorial : ℚ) ^ 7) * W.comp (baseU n) =
      ((X - C ((n : ℚ) + 1)) * (X + C (n : ℚ)) ^ 10) * H -
        (X ^ 10 * (X + C (2 * (n : ℚ) + 1))) * H.comp (X + C 1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite ((n : ℚ) + 1)).mono
  intro t ht
  have ht1 : (n : ℚ) + 1 < t := ht
  have ht0 : (0 : ℚ) < t := by have hnonneg : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n; linarith
  have hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (add_pos_of_pos_of_nonneg ht0 (Nat.cast_nonneg k))
  have hregular1 : ∀ k ≤ n, (t + 1) + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (by positivity)
  have hR : CoefficientMap.actualR n t ≠ 0 := actual_R_ne_zero_above_n n t (by linarith)
  have hfac : (n.factorial : ℚ) ^ 7 ≠ 0 := pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
  have hdiff := actual_weightedR_is_difference n hn W hstrong hzero t hregular
  rw [telescoper_quotient_as_R_A n hn1 W H hH t hregular,
    telescoper_quotient_as_R_A n hn1 W H hH (t + 1) hregular1] at hdiff
  rw [actual_R_shift_A_equals_R_B n t hregular hregular1] at hdiff
  unfold CoefficientMap.weightedR at hdiff
  have he : (n.factorial : ℚ) ^ 7 * W.eval (t * (t + (n : ℚ))) =
      aValue n t * H.eval t - bValue n t * H.eval (t + 1) := by
    field_simp [hfac] at hdiff
    nlinarith [hdiff]
  simpa only [Set.mem_ofPred_eq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    baseU, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    aValue, bValue, sub_sub, add_assoc] using he

theorem original_quartic_aggregate_kernel_zero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : aggregate n W = 0) : W = 0 := by
  have hstrong := quartic_is_strong_proper n (by omega) W hW
  obtain ⟨H, hH, hdegree⟩ := actual_polynomial_quotient_degree_bound n (by omega) hn W hstrong hzero
  have hrelation := kernel_actual_polynomial_relation n (by omega) hn W H hstrong hzero hH
  have hdiff : CoefficientMapShiftDegree.shiftDifference n H =
      C ((n.factorial : ℚ) ^ 7) * W.comp (baseU n) := hrelation.symm
  have hsmall : (CoefficientMapShiftDegree.shiftDifference n H).natDegree ≤ 8 := by
    rw [hdiff]
    have hmul : (C ((n.factorial : ℚ) ^ 7) * W.comp (baseU n)).natDegree ≤
        (C ((n.factorial : ℚ) ^ 7)).natDegree + (W.comp (baseU n)).natDegree := Polynomial.natDegree_mul_le
    have hcomp := Polynomial.natDegree_comp_le (p := W) (q := baseU n)
    rw [Polynomial.natDegree_C, zero_add] at hmul
    rw [baseU_natDegree] at hcomp
    omega
  have hH0 := CoefficientMapShiftDegree.actual_shift_difference_small_degree_implies_zero n (by omega) H hdegree hsmall
  rw [hH0] at hdiff
  simp only [CoefficientMapShiftDegree.shiftDifference, Polynomial.zero_comp, mul_zero, sub_zero] at hdiff
  have hcomp : W.comp (baseU n) = 0 := by
    have hfac : C ((n.factorial : ℚ) ^ 7) ≠ (0 : ℚ[X]) :=
      Polynomial.C_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero))
    exact (mul_eq_zero.mp hdiff.symm).resolve_left hfac
  apply weightedNumerator_zero_implies_multiplier_zero n W
  simp only [weightedNumerator, hcomp, mul_zero]

theorem original_quartic_aggregate_injective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W V : ℚ[X]) (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
    (heq : aggregate n W = aggregate n V) : W = V := by
  have hdegree : (W - V).natDegree ≤ 4 :=
    le_trans (Polynomial.natDegree_sub_le W V) (max_le hW hV)
  have hzero : aggregate n (W - V) = 0 := by
    change aggregateLinearMap n (W - V) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr heq
  exact sub_eq_zero.mp (original_quartic_aggregate_kernel_zero n hn2 hn (W - V) hdegree hzero)

theorem original_five_dimensional_map_injective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    Function.Injective (quarticAggregateLinearMap n) := by
  intro a b heq
  apply coordinatePolynomial_injective
  exact original_quartic_aggregate_injective n hn2 hn (coordinatePolynomial a) (coordinatePolynomial b)
    (coordinatePolynomial_natDegree_le a) (coordinatePolynomial_natDegree_le b) heq

theorem original_five_dimensional_map_bijective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    Function.Bijective (quarticAggregateLinearMap n) := by
  have hi := original_five_dimensional_map_injective n hn2 hn
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

theorem every_exact_formal_output_has_unique_quartic (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) : ∃! W : {W : ℚ[X] // W.natDegree ≤ 4}, aggregate n W.val = b := by
  obtain ⟨a, ha⟩ := (original_five_dimensional_map_bijective n hn2 hn).surjective b
  refine ⟨⟨coordinatePolynomial a, coordinatePolynomial_natDegree_le a⟩, ha, ?_⟩
  intro V hV
  apply Subtype.ext
  exact original_quartic_aggregate_injective n hn2 hn V.val (coordinatePolynomial a) V.property
    (coordinatePolynomial_natDegree_le a) (hV.trans ha.symm)

theorem inverseMultiplier_natDegree_le (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    (inverseMultiplier n hn2 hn b).natDegree ≤ 4 := coordinatePolynomial_natDegree_le _

theorem inverseMultiplier_actual_aggregate (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    aggregate n (inverseMultiplier n hn2 hn b) = b := by
  change (actualAggregateEquiv n hn2 hn) ((actualAggregateEquiv n hn2 hn).symm b) = b
  exact (actualAggregateEquiv n hn2 hn).apply_symm_apply b

theorem inverseMultiplier_unique (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hWb : aggregate n W = b) : W = inverseMultiplier n hn2 hn b :=
  original_quartic_aggregate_injective n hn2 hn W _ hW (inverseMultiplier_natDegree_le n hn2 hn b)
    (hWb.trans (inverseMultiplier_actual_aggregate n hn2 hn b).symm)

theorem inverseMultiplier_nonzero_of_output_nonzero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) (hb : b ≠ 0) : inverseMultiplier n hn2 hn b ≠ 0 := by
  intro hW0
  have h := inverseMultiplier_actual_aggregate n hn2 hn b
  rw [hW0] at h
  have hF0 : aggregate n (0 : ℚ[X]) = 0 := (aggregateLinearMap n).map_zero
  exact hb (h.symm.trans hF0)

theorem inverseMultiplier_exact_L (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    CoefficientMapSummation.exactL n (inverseMultiplier n hn2 hn b) = prescribedL b := by
  have h := inverseMultiplier_actual_aggregate n hn2 hn b
  have hB : CoefficientMapFiniteSum.constantTerm n (inverseMultiplier n hn2 hn b) = b 0 := congrFun h 0
  have h3 : CoefficientMapFiniteSum.rho n 3 (inverseMultiplier n hn2 hn b) = b 1 := congrFun h 1
  have h5 : CoefficientMapFiniteSum.rho n 5 (inverseMultiplier n hn2 hn b) = b 2 := congrFun h 2
  have h7 : CoefficientMapFiniteSum.rho n 7 (inverseMultiplier n hn2 hn b) = b 3 := congrFun h 3
  have h9 : CoefficientMapFiniteSum.rho n 9 (inverseMultiplier n hn2 hn b) = b 4 := congrFun h 4
  simp only [CoefficientMapSummation.exactL, hB, h3, h5, h7, h9, prescribedL]

theorem inverseMultiplier_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)) (prescribedL b) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖) := by
  have hstrong := quartic_is_strong_proper n (by omega) _ (inverseMultiplier_natDegree_le n hn2 hn b)
  constructor
  · have h := CoefficientMapSummation.actualSeries_hasSum_exactL n hn _ hstrong
    rw [inverseMultiplier_exact_L n hn2 hn b] at h
    exact h
  · exact CoefficientMapSummation.actualSeries_norm_summable n _ hstrong

end ZetaNine.CoefficientMapKernelBridge

/- SOURCE module missions.zeta9.formalization.CoefficientMapConnection; full proof bodies preserved. -/

/-! The polynomial homogeneous kernel underlying the round-seven connection.
This source has no dependence on zeta values, aggregate maps or a kernel hypothesis. -/

noncomputable section
open Polynomial

namespace ZetaNine.CoefficientMapConnection

theorem connectionD_factor (n : ℕ) :
    connectionD n = (X - C (1 : ℚ)) ^ 10 * (X + C ((n : ℚ) + 1)) ^ 10 := by
  unfold connectionD connectionU
  have h : X * (X + C (n : ℚ)) - C ((n : ℚ) + 1) =
      (X - C (1 : ℚ)) * (X + C ((n : ℚ) + 1)) := by
    simp only [map_add, map_one]
    ring
  rw [h, mul_pow]

theorem connectionV_simple_root (n : ℕ) (hn : 1 ≤ n) :
    connectionV n - C (n : ℚ) = (X - C (1 : ℚ)) * (X + C (n : ℚ)) := by
  unfold connectionV
  rw [Nat.cast_sub hn]
  simp only [Nat.cast_one, map_sub, map_one]
  ring

theorem rootMultiplicity_le_natDegree_rat (q : ℚ[X]) (hq : q ≠ 0) (a : ℚ) :
    q.rootMultiplicity a ≤ q.natDegree := by
  have h := natDegree_le_of_dvd (pow_rootMultiplicity_dvd q a) hq
  simpa using h

theorem rootMultiplicity_simple_composition (q f g : ℚ[X]) (a b : ℚ)
    (hq : q ≠ 0) (hf : f - C a = (X - C b) * g)
    (hg : g.eval b ≠ 0) :
    (q.comp f).rootMultiplicity b = q.rootMultiplicity a := by
  obtain ⟨r, hr, hrdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq a
  have hrval : r.eval a ≠ 0 := by
    simpa only [dvd_iff_isRoot, IsRoot.def] using hrdvd
  have hfa : f.eval b = a := by
    have hh := congrArg (fun p : ℚ[X] => p.eval b) hf
    simp only [eval_sub, eval_C, eval_mul, eval_X, sub_self, zero_mul] at hh
    exact sub_eq_zero.mp hh
  let m := q.rootMultiplicity a
  let s := g ^ m * r.comp f
  have hsval : s.eval b ≠ 0 := by
    dsimp [s]
    simp only [eval_mul, eval_pow, eval_comp, hfa]
    exact mul_ne_zero (pow_ne_zero _ hg) hrval
  have hs : s ≠ 0 := by
    intro h
    apply hsval
    simp [h]
  have hqs : q.comp f = s * (X - C b) ^ m := by
    rw [hr, mul_comp, pow_comp, sub_comp, X_comp, C_comp, hf]
    dsimp [s]
    rw [mul_pow]
    ring
  rw [hqs, rootMultiplicity_mul_X_sub_C_pow hs,
    rootMultiplicity_eq_zero (show ¬ IsRoot s b from hsval), zero_add]

theorem first_factor_eval_one_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    ((X - C ((n : ℚ) + 1)) * (X + C ((n : ℚ) + 1)) ^ 10).eval 1 ≠ 0 := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow]
  apply mul_ne_zero
  · linarith
  · apply pow_ne_zero
    linarith

theorem connection_homogeneous_q_zero (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X])
    (hqdeg : q.natDegree ≤ 9)
    (heq : connectionD n * P.comp (connectionU n) + connectionH n q = 0) : q = 0 := by
  by_contra hq
  let A : ℚ[X] := (X - C ((n : ℚ) + 1)) * (X + C ((n : ℚ) + 1)) ^ 10
  have hA : A.eval 1 ≠ 0 := first_factor_eval_one_ne_zero n hn
  have hA0 : A ≠ 0 := by
    intro h
    apply hA
    simp [h]
  have hcomp : q.comp (connectionV n) ≠ 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h | ⟨_, hv⟩
    · exact hq h
    · have hv2 := congrArg (fun p : ℚ[X] => p.coeff 2) hv
      simp [connectionV, coeff_X_mul] at hv2
  have hF0 : A * q.comp (connectionV n) ≠ 0 := mul_ne_zero hA0 hcomp
  have hdvd : (X - C (1 : ℚ)) ^ 10 ∣ A * q.comp (connectionV n) := by
    refine ⟨(X + C (2 * (n : ℚ) + 1)) *
      q.comp ((X + 1) * (X + C (n : ℚ))) -
        (X + C ((n : ℚ) + 1)) ^ 10 * P.comp (connectionU n), ?_⟩
    rw [connectionD_factor] at heq
    dsimp [connectionH] at heq
    dsimp [A]
    simp only [map_one] at heq ⊢
    linear_combination heq
  have hmult : (A * q.comp (connectionV n)).rootMultiplicity 1 = q.rootMultiplicity (n : ℚ) := by
    rw [rootMultiplicity_mul hF0,
      rootMultiplicity_eq_zero (show ¬ IsRoot A 1 from hA), zero_add]
    apply rootMultiplicity_simple_composition q (connectionV n) (X + C (n : ℚ))
      (n : ℚ) 1 hq (connectionV_simple_root n hn)
    simp only [eval_add, eval_X, eval_C]
    positivity
  have hm10 := (le_rootMultiplicity_iff hF0).mpr hdvd
  rw [hmult] at hm10
  have hm9 := (rootMultiplicity_le_natDegree_rat q hq (n : ℚ)).trans hqdeg
  omega

theorem connectionU_comp_eq_zero (n : ℕ) (P : ℚ[X])
    (h : P.comp (connectionU n) = 0) : P = 0 := by
  rcases comp_eq_zero_iff.mp h with h | ⟨_, hu⟩
  · exact h
  · have h2 := congrArg (fun p : ℚ[X] => p.coeff 2) hu
    simp [connectionU, coeff_X_mul] at h2

theorem connection_homogeneous_kernel_zero (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X])
    (hqdeg : q.natDegree ≤ 9)
    (heq : connectionD n * P.comp (connectionU n) + connectionH n q = 0) :
    P = 0 ∧ q = 0 := by
  have hq := connection_homogeneous_q_zero n hn P q hqdeg heq
  have hD : connectionD n ≠ 0 := by
    rw [connectionD_factor]
    apply mul_ne_zero
    · exact pow_ne_zero _ (X_sub_C_ne_zero 1)
    · apply pow_ne_zero
      simpa only [sub_neg_eq_add, map_neg] using X_sub_C_ne_zero (-((n : ℚ) + 1))
  have hP : P.comp (connectionU n) = 0 := by
    simpa only [hq, connectionH, zero_comp, mul_zero, sub_self, add_zero,
      mul_eq_zero, hD, false_or] using heq
  exact ⟨connectionU_comp_eq_zero n P hP, hq⟩

theorem connectionU_reflection (n : ℕ) :
    (connectionU n).comp (connectionReflection n) = connectionU n := by
  simp only [connectionU, connectionReflection, mul_comp, add_comp, X_comp, C_comp]
  ring

theorem connectionH_reflection (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) :
    (connectionH n q).comp (connectionReflection n) = connectionH n q := by
  have hv : (connectionV n).comp (connectionReflection n) =
      (X + 1) * (X + C (n : ℚ)) := by
    simp only [connectionV, connectionReflection, mul_comp, add_comp, X_comp, C_comp]
    rw [Nat.cast_sub hn]
    simp only [Nat.cast_one, map_sub, map_one]
    ring
  have hw : ((X + 1) * (X + C (n : ℚ))).comp (connectionReflection n) =
      connectionV n := by
    simp only [connectionV, connectionReflection, mul_comp, add_comp, X_comp, C_comp,
      one_comp]
    rw [Nat.cast_sub hn]
    simp only [Nat.cast_one, map_sub, map_one]
    ring
  have ha : (X - C ((n : ℚ) + 1)).comp (connectionReflection n) =
      -(X + C (2 * (n : ℚ) + 1)) := by
    rw [sub_comp, X_comp, C_comp]
    simp only [connectionReflection, map_add, map_mul, map_ofNat, map_one]
    ring
  have hb : (X + C ((n : ℚ) + 1)).comp (connectionReflection n) = -(X - 1) := by
    rw [add_comp, X_comp, C_comp]
    simp only [connectionReflection, map_add, map_one]
    ring
  have hc : (X + C (2 * (n : ℚ) + 1)).comp (connectionReflection n) =
      -(X - C ((n : ℚ) + 1)) := by
    rw [add_comp, X_comp, C_comp]
    simp only [connectionReflection, map_add, map_mul, map_ofNat, map_one]
    ring
  have hd : (X - 1 : ℚ[X]).comp (connectionReflection n) =
      -(X + C ((n : ℚ) + 1)) := by
    simp only [sub_comp, X_comp, one_comp, connectionReflection, map_add, map_one]
    ring
  simp only [connectionH, sub_comp, mul_comp, pow_comp, comp_assoc,
    hv, hw, ha, hb, hc, hd]
  ring

theorem reflected_natDegree_even (n : ℕ) (p : ℚ[X]) (hp : p ≠ 0)
    (href : p.comp (connectionReflection n) = p) : Even p.natDegree := by
  have hd : (connectionReflection n).natDegree = 1 := by
    rw [connectionReflection, natDegree_sub_C, natDegree_neg, natDegree_X]
  have hl : (connectionReflection n).leadingCoeff = -1 := by
    have heq : connectionReflection n = -(X + C (n : ℚ)) := by
      unfold connectionReflection
      ring
    rw [heq, leadingCoeff_neg, leadingCoeff_X_add_C]
  have hh := congrArg Polynomial.leadingCoeff href
  rw [leadingCoeff_comp (by omega), hl] at hh
  have hpow : (-1 : ℚ) ^ p.natDegree = 1 := by
    apply (mul_left_cancel₀ (leadingCoeff_ne_zero.mpr hp))
    simpa using hh
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℚ) ≠ 1)).mp hpow

theorem reflected_even_coefficients_determine (n : ℕ) (p : ℚ[X])
    (hdeg : p.natDegree ≤ 29) (href : p.comp (connectionReflection n) = p)
    (heven : ∀ i : Fin 15, p.coeff (2 * i.val) = 0) : p = 0 := by
  by_contra hp
  obtain ⟨k, hk⟩ := reflected_natDegree_even n p hp href
  have hk15 : k < 15 := by omega
  have h := heven ⟨k, hk15⟩
  have h2 : p.natDegree = 2 * k := by omega
  rw [← h2, coeff_natDegree] at h
  exact leadingCoeff_ne_zero.mpr hp h

theorem coefficientPolynomial_coeff (d : ℕ) (c : Fin d → ℚ) (i : Fin d) :
    (coefficientPolynomial d c).coeff i.val = c i := by
  classical
  rw [coefficientPolynomial, finsetSum_coeff]
  simp only [coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : i.val ≠ j.val := by
      intro h
      exact hji (Fin.ext h.symm)
    simp [hne]
  · simp

theorem coefficientPolynomial_add (d : ℕ) (c e : Fin d → ℚ) :
    coefficientPolynomial d (c + e) = coefficientPolynomial d c + coefficientPolynomial d e := by
  classical
  simp only [coefficientPolynomial, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem coefficientPolynomial_smul (d : ℕ) (a : ℚ) (c : Fin d → ℚ) :
    coefficientPolynomial d (a • c) = a • coefficientPolynomial d c := by
  classical
  simp only [coefficientPolynomial, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem coefficientPolynomial_degree (d : ℕ) (c : Fin d → ℚ) :
    (coefficientPolynomial d c).natDegree ≤ d - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply (natDegree_smul_le (c i) (X ^ i.val)).trans
  simp only [natDegree_X_pow]
  omega

theorem connectionOperator_reflection (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X]) :
    (connectionOperator n P q).comp (connectionReflection n) = connectionOperator n P q := by
  simp only [connectionOperator, add_comp, mul_comp, connectionD, pow_comp,
    sub_comp, C_comp, connectionU_reflection, comp_assoc, connectionH_reflection n hn]

theorem connectionOperator_degree (n : ℕ) (P q : ℚ[X])
    (hP : P.natDegree ≤ 4) (hq : q.natDegree ≤ 9) :
    (connectionOperator n P q).natDegree ≤ 29 := by
  have hu : (connectionU n).natDegree ≤ 2 := by
    have h := natDegree_mul_le (p := (X : ℚ[X])) (q := X + C (n : ℚ))
    rw [natDegree_X, natDegree_X_add_C] at h
    exact h
  have hv : (connectionV n).natDegree ≤ 2 := by
    have h := natDegree_mul_le (p := (X : ℚ[X])) (q := X + C ((n - 1 : ℕ) : ℚ))
    rw [natDegree_X, natDegree_X_add_C] at h
    exact h
  have hw : (((X : ℚ[X]) + 1) * (X + C (n : ℚ))).natDegree ≤ 2 := by
    have h := natDegree_mul_le (p := (X : ℚ[X]) + C 1) (q := X + C (n : ℚ))
    rw [natDegree_X_add_C, natDegree_X_add_C] at h
    exact h
  have hD : (connectionD n).natDegree ≤ 20 := by
    exact (natDegree_pow_le (p := connectionU n - C ((n : ℚ) + 1)) (n := 10)).trans
      (by simpa only [natDegree_sub_C] using Nat.mul_le_mul_left 10 hu)
  have hA : ((X - C ((n : ℚ) + 1)) * (X + C ((n : ℚ) + 1)) ^ 10).natDegree ≤ 11 := by
    have h := natDegree_mul_le (p := (X : ℚ[X]) - C ((n : ℚ) + 1))
      (q := (X + C ((n : ℚ) + 1)) ^ 10)
    rw [natDegree_X_sub_C, natDegree_pow, natDegree_X_add_C] at h
    exact h
  have hB : ((X + C (2 * (n : ℚ) + 1)) * (X - 1) ^ 10).natDegree ≤ 11 := by
    have h := natDegree_mul_le (p := (X : ℚ[X]) + C (2 * (n : ℚ) + 1))
      (q := (X - C 1) ^ 10)
    rw [natDegree_X_add_C, natDegree_pow, natDegree_X_sub_C] at h
    exact h
  have hpcomp : (P.comp (connectionU n)).natDegree ≤ 8 :=
    natDegree_comp_le.trans (by nlinarith)
  have hqcomp : (q.comp (connectionV n)).natDegree ≤ 18 :=
    natDegree_comp_le.trans (by nlinarith)
  have hqwcomp : (q.comp ((X + 1) * (X + C (n : ℚ)))).natDegree ≤ 18 :=
    natDegree_comp_le.trans (by nlinarith)
  change (connectionD n * P.comp (connectionU n) + connectionH n q).natDegree ≤ 29
  apply natDegree_add_le_of_degree_le
  · exact natDegree_mul_le.trans (by omega)
  · unfold connectionH
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by omega)
    · exact natDegree_mul_le.trans (by omega)

theorem connectionOperator_add (n : ℕ) (P Q q r : ℚ[X]) :
    connectionOperator n (P + Q) (q + r) =
      connectionOperator n P q + connectionOperator n Q r := by
  simp only [connectionOperator, connectionH, add_comp, mul_add]
  ring

theorem connectionOperator_smul (n : ℕ) (a : ℚ) (P q : ℚ[X]) :
    connectionOperator n (a • P) (a • q) = a • connectionOperator n P q := by
  simp only [connectionOperator, connectionH, smul_comp, mul_smul_comm, smul_sub, smul_add]

theorem connectionLinearMap_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (connectionLinearMap n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro c hc
  have hP : (inputP c).natDegree ≤ 4 := coefficientPolynomial_degree 5 _
  have hq : (inputQ c).natDegree ≤ 9 := coefficientPolynomial_degree 10 _
  have heven : ∀ i : Fin 15, (connectionOperator n (inputP c) (inputQ c)).coeff
      (2 * i.val) = 0 := by
    intro i
    exact congrFun hc i
  have hz := reflected_even_coefficients_determine n
    (connectionOperator n (inputP c) (inputQ c))
    (connectionOperator_degree n _ _ hP hq)
    (connectionOperator_reflection n hn _ _) heven
  obtain ⟨hP0, hq0⟩ := connection_homogeneous_kernel_zero n hn _ _ hq hz
  funext i
  by_cases hi : i.val < 5
  · have h := coefficientPolynomial_coeff 5 (fun j => c ⟨j.val, by omega⟩) ⟨i.val, hi⟩
    change (inputP c).coeff i.val = c i at h
    simpa only [hP0, coeff_zero, Pi.zero_apply] using h.symm
  · have h := coefficientPolynomial_coeff 10 (fun j => c ⟨j.val + 5, by omega⟩)
      ⟨i.val - 5, by omega⟩
    have hidx : i.val - 5 + 5 = i.val := by omega
    change (inputQ c).coeff (i.val - 5) = c ⟨i.val - 5 + 5, _⟩ at h
    simpa only [hq0, coeff_zero, hidx, Pi.zero_apply] using h.symm

theorem connectionLinearMap_bijective (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (connectionLinearMap n) :=
  ⟨connectionLinearMap_injective n hn,
    LinearMap.injective_iff_surjective.mp (connectionLinearMap_injective n hn)⟩

theorem connection_reflected_target_exists_unique (n : ℕ) (hn : 1 ≤ n) (f : ℚ[X])
    (hdeg : f.natDegree ≤ 29) (href : f.comp (connectionReflection n) = f) :
    ∃! c : Fin 15 → ℚ, connectionOperator n (inputP c) (inputQ c) = f := by
  obtain ⟨c, hc⟩ := (connectionLinearMap_bijective n hn).2 (fun i => f.coeff (2 * i.val))
  have hpdeg : (inputP c).natDegree ≤ 4 := coefficientPolynomial_degree 5 _
  have hqdeg : (inputQ c).natDegree ≤ 9 := coefficientPolynomial_degree 10 _
  have hzero : connectionOperator n (inputP c) (inputQ c) - f = 0 := by
    apply reflected_even_coefficients_determine n
    · exact (natDegree_sub_le _ _).trans
        (max_le (connectionOperator_degree n _ _ hpdeg hqdeg) hdeg)
    · simp only [sub_comp, connectionOperator_reflection n hn, href]
    · intro i
      rw [coeff_sub]
      exact sub_eq_zero.mpr (congrFun hc i)
  refine ⟨c, sub_eq_zero.mp hzero, ?_⟩
  intro d hd
  apply connectionLinearMap_injective n hn
  funext i
  change (connectionOperator n (inputP d) (inputQ d)).coeff (2 * i.val) =
    (connectionOperator n (inputP c) (inputQ c)).coeff (2 * i.val)
  rw [hd, sub_eq_zero.mp hzero]

theorem connectionOperator_sub (n : ℕ) (P Q q r : ℚ[X]) :
    connectionOperator n (P - Q) (q - r) =
      connectionOperator n P q - connectionOperator n Q r := by
  simp only [connectionOperator, connectionH, sub_comp, mul_sub]
  ring

theorem connection_original_system_exists_unique (n : ℕ) (hn : 1 ≤ n) (f : ℚ[X])
    (hf : f.natDegree ≤ 14) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        f.comp (connectionU n) := by
  have hu : (connectionU n).natDegree ≤ 2 := by
    have h := natDegree_mul_le (p := (X : ℚ[X])) (q := X + C (n : ℚ))
    rw [natDegree_X, natDegree_X_add_C] at h
    exact h
  have htarget : (f.comp (connectionU n)).natDegree ≤ 29 :=
    natDegree_comp_le.trans (by nlinarith)
  have hreflect : (f.comp (connectionU n)).comp (connectionReflection n) =
      f.comp (connectionU n) := by
    rw [comp_assoc, connectionU_reflection]
  obtain ⟨c, hc, _⟩ := connection_reflected_target_exists_unique n hn
    (f.comp (connectionU n)) htarget hreflect
  have hPc : (inputP c).natDegree ≤ 4 := coefficientPolynomial_degree 5 _
  have hqc : (inputQ c).natDegree ≤ 9 := coefficientPolynomial_degree 10 _
  refine ⟨(inputP c, inputQ c), ⟨hPc, hqc, hc⟩, ?_⟩
  intro pq hpq
  have hdiff : (pq.2 - inputQ c).natDegree ≤ 9 :=
    (natDegree_sub_le _ _).trans (max_le hpq.2.1 hqc)
  have hz : connectionOperator n (pq.1 - inputP c) (pq.2 - inputQ c) = 0 := by
    rw [connectionOperator_sub, hc]
    change (connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2) -
      f.comp (connectionU n) = 0
    rw [hpq.2.2, sub_self]
  obtain ⟨hP, hq⟩ := connection_homogeneous_kernel_zero n hn _ _ hdiff hz
  exact Prod.ext (sub_eq_zero.mp hP) (sub_eq_zero.mp hq)

theorem connectionTarget_degree (n r : ℕ) (hr : r ≤ 4) :
    (connectionTarget n r).natDegree ≤ 7 := by
  have hZ : (connectionZ n).natDegree ≤ 3 := by
    unfold connectionZ
    apply natDegree_mul_le.trans
    have h := natDegree_mul_le (p := X - C (((n : ℚ) + 1) * (2 * (n : ℚ) + 1)))
      (q := X - C (((n : ℚ) + 2) * (2 * (n : ℚ) + 2)))
    rw [natDegree_X_sub_C, natDegree_X_sub_C] at h
    rw [natDegree_X_sub_C]
    omega
  unfold connectionTarget
  have hC := natDegree_mul_le (p := C ((((n : ℚ) + 1) * ((n : ℚ) + 2)) ^ 7))
    (q := connectionZ n)
  rw [natDegree_C, zero_add] at hC
  apply natDegree_mul_le.trans
  rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  omega

theorem connection_five_systems_unique (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        (connectionTarget n r.val).comp (connectionU n) := by
  apply connection_original_system_exists_unique n hn
  exact (connectionTarget_degree n r.val (by omega)).trans (by norm_num)

end ZetaNine.CoefficientMapConnection

/- SOURCE module missions.zeta9.formalization.CoefficientMapParameterShift; full proof bodies preserved. -/

/-!
Actual n -> n+2 rational-function transport at regular rational points.
This is a candidate awaiting its first Lean compilation. It does not assert
transport of the five formal coefficient coordinates or an infinite sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapParameterShift

open CoefficientMapKernelBridge CoefficientMapConnection

theorem positiveProduct_add_two (n : ℕ) (t : ℚ) :
    positiveProduct (n + 2) t =
      positiveProduct n t * (t - (n : ℚ) - 1) * (t - (n : ℚ) - 2) := by
  unfold positiveProduct
  rw [Finset.prod_range_succ, Finset.prod_range_succ]
  push_cast
  ring

theorem positiveProduct_parameter_shift (n : ℕ) (t : ℚ) :
    positiveProduct (n + 2) (t - 1) * (t - 1) =
      positiveProduct n t * (t - (n : ℚ) - 1) *
        (t - (n : ℚ) - 2) * (t - (n : ℚ) - 3) := by
  have h := positiveProduct_shift (n + 2) (t - 1)
  rw [sub_add_cancel, positiveProduct_add_two] at h
  push_cast at h
  calc
    _ = (t - 1) * positiveProduct (n + 2) (t - 1) := by ring
    _ = _ := by rw [← h]; ring

theorem negativeProduct_add_two_sub_one (n : ℕ) (t : ℚ) :
    negativeProduct (n + 2) (t - 1) = negativeProduct n (t + 1) *
      (t + 2 * (n : ℚ) + 2) * (t + 2 * (n : ℚ) + 3) := by
  unfold negativeProduct
  rw [Finset.prod_range_succ, Finset.prod_range_succ]
  have he : (∏ k ∈ range n, (t - 1 + ((n + 2 : ℕ) : ℚ) + ((k : ℚ) + 1))) =
      ∏ k ∈ range n, (t + 1 + (n : ℚ) + ((k : ℚ) + 1)) := by
    apply Finset.prod_congr rfl
    intro k hk
    push_cast
    ring
  rw [he]
  push_cast
  ring

theorem negativeProduct_parameter_shift (n : ℕ) (t : ℚ) :
    negativeProduct (n + 2) (t - 1) * (t + (n : ℚ) + 1) =
      negativeProduct n t * (t + 2 * (n : ℚ) + 1) *
        (t + 2 * (n : ℚ) + 2) * (t + 2 * (n : ℚ) + 3) := by
  rw [negativeProduct_add_two_sub_one]
  calc
    _ = (negativeProduct n (t + 1) * (t + (n : ℚ) + 1)) *
        (t + 2 * (n : ℚ) + 2) * (t + 2 * (n : ℚ) + 3) := by ring
    _ = _ := by rw [negativeProduct_shift]

theorem poleProduct_parameter_shift (n : ℕ) (t : ℚ) :
    CoefficientMap.poleProduct (n + 2) (t - 1) =
      (t - 1) * CoefficientMap.poleProduct n t * (t + (n : ℚ) + 1) := by
  unfold CoefficientMap.poleProduct
  rw [Finset.prod_range_succ', Finset.prod_range_succ]
  have he : (∏ k ∈ range (n + 1), (t - 1 + ((k + 1 : ℕ) : ℚ))) =
      ∏ k ∈ range (n + 1), (t + (k : ℚ)) := by
    apply Finset.prod_congr rfl
    intro k hk
    push_cast
    ring
  rw [he]
  push_cast
  ring

theorem factorial_parameter_shift (n : ℕ) :
    ((n + 2).factorial : ℚ) ^ 7 = parameterScale n * (n.factorial : ℚ) ^ 7 := by
  rw [Nat.factorial_succ, Nat.factorial_succ]
  unfold parameterScale
  push_cast
  ring

theorem connectionZ_eval_factors (n : ℕ) (t : ℚ) :
    (connectionZ n).eval (t * (t + (n : ℚ))) =
      ((t - (n : ℚ) - 1) * (t + 2 * (n : ℚ) + 1)) *
        ((t - (n : ℚ) - 2) * (t + 2 * (n : ℚ) + 2)) *
        ((t - (n : ℚ) - 3) * (t + 2 * (n : ℚ) + 3)) := by
  simp only [connectionZ, eval_mul, eval_sub, eval_X, eval_C]
  ring

theorem numerator_parameter_shift (n : ℕ) (t : ℚ) :
    CoefficientMap.numerator (n + 2) (t - 1) * (t - 1) * (t + (n : ℚ) + 1) =
      parameterScale n * CoefficientMap.numerator n t *
        (connectionZ n).eval (t * (t + (n : ℚ))) := by
  change ((n + 2).factorial : ℚ) ^ 7 * positiveProduct (n + 2) (t - 1) *
      negativeProduct (n + 2) (t - 1) * (t - 1) * (t + (n : ℚ) + 1) =
    parameterScale n * ((n.factorial : ℚ) ^ 7 * positiveProduct n t * negativeProduct n t) * _
  rw [factorial_parameter_shift, connectionZ_eval_factors]
  calc
    _ = parameterScale n * (n.factorial : ℚ) ^ 7 *
        (positiveProduct (n + 2) (t - 1) * (t - 1)) *
        (negativeProduct (n + 2) (t - 1) * (t + (n : ℚ) + 1)) := by ring
    _ = _ := by rw [positiveProduct_parameter_shift, negativeProduct_parameter_shift]; ring

theorem connectionD_eval_factors (n : ℕ) (t : ℚ) :
    (connectionD n).eval t = (t - 1) ^ 10 * (t + (n : ℚ) + 1) ^ 10 := by
  rw [connectionD_factor]
  simp only [eval_mul, eval_pow, eval_sub, eval_add, eval_C, eval_X]
  ring

theorem shifted_regular_conditions (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    (∀ k ≤ n, t + (k : ℚ) ≠ 0) ∧
      (∀ k ≤ n, t + 1 + (k : ℚ) ≠ 0) ∧
        t - 1 ≠ 0 ∧ t ≠ 0 ∧ t + (n : ℚ) + 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have h := hregular (k + 1) (by omega)
    convert h using 1 <;> push_cast <;> ring
  · intro k hk
    have h := hregular (k + 2) (by omega)
    convert h using 1 <;> push_cast <;> ring
  · simpa using hregular 0 (by omega)
  · convert hregular 1 (by omega) using 1 <;> norm_num <;> ring
  · convert hregular (n + 2) (by omega) using 1 <;> push_cast <;> ring

theorem actual_R_parameter_shift (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    CoefficientMap.actualR (n + 2) (t - 1) * (connectionD n).eval t =
      parameterScale n * (connectionZ n).eval (t * (t + (n : ℚ))) *
        CoefficientMap.actualR n t := by
  obtain ⟨hreg, _, hm, _, hp⟩ := shifted_regular_conditions n t hregular
  have hd := CoefficientMap.poleProduct_ne_zero n t hreg
  rw [connectionD_eval_factors]
  unfold CoefficientMap.actualR
  calc
    _ = (CoefficientMap.numerator (n + 2) (t - 1) * (t - 1) *
        (t + (n : ℚ) + 1)) / CoefficientMap.poleProduct n t ^ 9 := by
      rw [poleProduct_parameter_shift]
      field_simp [hm, hp, hd]
    _ = _ := by rw [numerator_parameter_shift]; ring

theorem connectionRemainder_successor (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) (t : ℚ)
    (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    connectionRemainder n q (t + 1) =
      CoefficientMap.actualR n t * (t + 2 * (n : ℚ) + 1) /
        (t + (n : ℚ) + 1) ^ 10 * q.eval ((t + 1) * (t + (n : ℚ))) := by
  obtain ⟨hreg, hreg1, _, ht, hp⟩ := shifted_regular_conditions n t hregular
  have h := actual_R_shift_A_equals_R_B n t hreg hreg1
  have hv : (connectionV n).eval (t + 1) = (t + 1) * (t + (n : ℚ)) := by
    simp only [connectionV, eval_mul, eval_add, eval_X, eval_C, Nat.cast_sub hn, Nat.cast_one]
    ring
  unfold connectionRemainder
  rw [hv]
  have hs : t + 1 - 1 = t := by ring
  have ha : t + 1 - (n : ℚ) - 1 = t - (n : ℚ) := by ring
  rw [hs, ha]
  unfold aValue bValue at h
  have he : CoefficientMap.actualR n (t + 1) * (t - (n : ℚ)) /
      t ^ 10 = CoefficientMap.actualR n t * (t + 2 * (n : ℚ) + 1) /
        (t + (n : ℚ) + 1) ^ 10 := by
    apply (div_eq_div_iff (pow_ne_zero _ ht) (pow_ne_zero _ hp)).mpr
    convert h using 1 <;> ring
  rw [he]

theorem connectionRemainder_difference (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) (t : ℚ)
    (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    connectionRemainder n q t - connectionRemainder n q (t + 1) =
      CoefficientMap.actualR n t * (connectionH n q).eval t / (connectionD n).eval t := by
  obtain ⟨_, _, hm, _, hp⟩ := shifted_regular_conditions n t hregular
  rw [connectionRemainder_successor n hn q t hregular, connectionRemainder,
    connectionD_eval_factors]
  simp only [connectionH, eval_sub, eval_mul, eval_pow, eval_add, eval_comp, eval_X, eval_C,
    eval_one, Nat.cast_add, Nat.cast_one]
  field_simp [hm, hp]
  ring

theorem actual_original_connection_transport (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (P q : ℚ[X])
    (heq : connectionD n * P.comp (connectionU n) + connectionH n q =
      (connectionTarget n r).comp (connectionU n))
    (t : ℚ) (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    CoefficientMap.actualR (n + 2) (t - 1) *
        (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r =
      CoefficientMap.actualR n t * P.eval (t * (t + (n : ℚ))) +
        (connectionRemainder n q t - connectionRemainder n q (t + 1)) := by
  obtain ⟨_, _, hm, _, hp⟩ := shifted_regular_conditions n t hregular
  have hD : (connectionD n).eval t ≠ 0 := by
    rw [connectionD_eval_factors]
    exact mul_ne_zero (pow_ne_zero _ hm) (pow_ne_zero _ hp)
  have hpoly := congrArg (fun p : ℚ[X] => p.eval t) heq
  simp only [eval_add, eval_mul, eval_comp, connectionTarget, connectionU,
    eval_pow, eval_sub, eval_X, eval_C] at hpoly
  change (connectionD n).eval t * P.eval (t * (t + (n : ℚ))) +
      (connectionH n q).eval t = parameterScale n *
        (connectionZ n).eval (t * (t + (n : ℚ))) *
          (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r at hpoly
  have hR := actual_R_parameter_shift n t hregular
  rw [connectionRemainder_difference n hn q t hregular]
  apply (mul_right_cancel₀ hD)
  calc
    _ = (CoefficientMap.actualR (n + 2) (t - 1) * (connectionD n).eval t) *
        (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r := by ring
    _ = CoefficientMap.actualR n t *
        (parameterScale n * (connectionZ n).eval (t * (t + (n : ℚ))) *
          (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r) := by rw [hR]; ring
    _ = CoefficientMap.actualR n t *
        ((connectionD n).eval t * P.eval (t * (t + (n : ℚ))) + (connectionH n q).eval t) := by
      rw [← hpoly]
    _ = _ := by field_simp [hD]

theorem five_actual_connection_transports_exist_unique (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        (connectionTarget n r.val).comp (connectionU n) ∧
      ∀ t : ℚ, (∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) →
        CoefficientMap.actualR (n + 2) (t - 1) *
            (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r.val =
          CoefficientMap.actualR n t * pq.1.eval (t * (t + (n : ℚ))) +
            (connectionRemainder n pq.2 t - connectionRemainder n pq.2 (t + 1)) := by
  obtain ⟨pq, ⟨hP, hq, heq⟩, huniq⟩ := connection_five_systems_unique n hn r
  refine ⟨pq, ⟨hP, hq, heq, ?_⟩, ?_⟩
  · intro t hregular
    exact actual_original_connection_transport n hn r.val pq.1 pq.2 heq t hregular
  · intro pq' hpq'
    exact huniq pq' ⟨hpq'.1, hpq'.2.1, hpq'.2.2.1⟩

end ZetaNine.CoefficientMapParameterShift

/- SOURCE module missions.zeta9.formalization.CoefficientMapFormalTransportData; full proof bodies preserved. -/

/-!
UNCOMPILED DATA CANDIDATE for the genuine five-output parameter transport.
This file chooses the actual unique Connection pair and defines the real
remainder numerator and proper-numerator local jets. No PF existence,
coefficient transport or matrix identity is assumed or proved here.
The witness specification below merely reuses the existing native Connection
theorem. The new generic PF and transport obligations are in the design note.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFormalTransportData

open CoefficientMapConnection CoefficientMapJet CoefficientMapInjectivity

theorem connectionPair_spec (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    (connectionP n r).natDegree ≤ 4 ∧ (connectionQ n r).natDegree ≤ 9 ∧
      connectionD n * (connectionP n r).comp (connectionU n) +
        connectionH n (connectionQ n r) =
          (connectionTarget n r.val).comp (connectionU n) := by
  simpa only [connectionP, connectionQ, connectionPair, dif_pos hn] using
    (Classical.choose_spec (connection_five_systems_unique n hn r).exists)

/-- Rows are new monomial indices; columns are old P coefficient indices. -/
end ZetaNine.CoefficientMapFormalTransportData

/- SOURCE module missions.zeta9.formalization.CoefficientMapFormalTransportBounds; full proof bodies preserved. -/

/-!
Basic actual-choice and strict proper-numerator bridge for formal transport.
The chosen pair is the genuine Connection witness, with n >= 1.  Gamma
recovers its actual quartic P.  The true cancellation numerator is zero at
t=2, including n=1, and is strictly proper in shifted coordinates when
deg(q)<=9.  This does not supply partial fractions or five-output transport.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFormalTransportBounds

open CoefficientMapFormalTransportData CoefficientMapConnection
open CoefficientMapAggregate CoefficientMapInjectivity

theorem connectionP_natDegree_le (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    (connectionP n r).natDegree ≤ 4 := (connectionPair_spec n hn r).1

theorem connectionQ_natDegree_le (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    (connectionQ n r).natDegree ≤ 9 := (connectionPair_spec n hn r).2.1

theorem chosen_connection_equation (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    connectionD n * (connectionP n r).comp (connectionU n) +
      connectionH n (connectionQ n r) =
        (connectionTarget n r.val).comp (connectionU n) :=
  (connectionPair_spec n hn r).2.2

theorem connectionGamma_row_coordinates (n : ℕ) (r : Fin 5) :
    connectionGamma n r = polynomialCoordinates (connectionP n r) := rfl

theorem connectionGamma_restores_P (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    coordinatePolynomial (connectionGamma n r) = connectionP n r := by
  rw [connectionGamma_row_coordinates]
  exact polynomial_restore _ (connectionP_natDegree_le n hn r)

theorem connectionP_eq_Gamma_row_sum (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    connectionP n r = ∑ l : Fin 5, C (connectionGamma n r l) * X ^ l.val :=
  (connectionGamma_restores_P n hn r).symm

theorem remainderNumerator_eval_two (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) :
    (remainderNumerator n q).eval 2 = 0 := by
  have hL : (∏ i ∈ range n, (X - C ((i : ℚ) + 2))).eval 2 = 0 := by
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    apply Finset.prod_eq_zero (show 0 ∈ range n from mem_range.mpr (by omega))
    norm_num
  simp only [remainderNumerator, eval_mul, hL, mul_zero, zero_mul]

theorem shiftedRemainderNumerator_eval_one (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) :
    (shiftedRemainderNumerator n q).eval 1 = 0 := by
  simpa only [shiftedRemainderNumerator, eval_comp, eval_add, eval_X, eval_one,
    show (1 : ℚ) + 1 = 2 by norm_num] using remainderNumerator_eval_two n hn q

theorem connectionV_natDegree (n : ℕ) : (connectionV n).natDegree = 2 :=
  baseU_natDegree (n - 1)

theorem remainderNumerator_natDegree_le (n : ℕ) (q : ℚ[X]) :
    (remainderNumerator n q).natDegree ≤ 2 * n + 2 * q.natDegree := by
  have hL : (∏ i ∈ range n, (X - C ((i : ℚ) + 2))).natDegree ≤ n := by
    calc
      _ ≤ ∑ i ∈ range n, (X - C ((i : ℚ) + 2)).natDegree := natDegree_prod_le _ _
      _ = n := by
        simp only [natDegree_X_sub_C]
        simp
  have hR : (∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1))).natDegree ≤ n := by
    calc
      _ ≤ ∑ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1)).natDegree := natDegree_prod_le _ _
      _ = n := by
        simp only [natDegree_X_add_C]
        simp
  have h1 := natDegree_mul_le (p := C ((n.factorial : ℚ) ^ 7))
    (q := ∏ i ∈ range n, (X - C ((i : ℚ) + 2)))
  have h2 := natDegree_mul_le
    (p := C ((n.factorial : ℚ) ^ 7) * (∏ i ∈ range n, (X - C ((i : ℚ) + 2))))
    (q := ∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1)))
  have h3 := natDegree_mul_le
    (p := C ((n.factorial : ℚ) ^ 7) * (∏ i ∈ range n, (X - C ((i : ℚ) + 2))) *
      (∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1))))
    (q := q.comp (connectionV n))
  have hc := natDegree_comp_le (p := q) (q := connectionV n)
  rw [connectionV_natDegree] at hc
  simp only [natDegree_C, zero_add] at h1
  unfold remainderNumerator
  omega

theorem shiftedRemainderNumerator_natDegree_le (n : ℕ) (q : ℚ[X]) :
    (shiftedRemainderNumerator n q).natDegree ≤ 2 * n + 2 * q.natDegree := by
  have h := natDegree_comp_le (p := remainderNumerator n q) (q := X + 1)
  have hx : (X + 1 : ℚ[X]).natDegree = 1 := by
    simpa only [map_one] using (natDegree_X_add_C (1 : ℚ))
  rw [hx, Nat.mul_one] at h
  exact h.trans (remainderNumerator_natDegree_le n q)

theorem remainderNumerator_degree_nine_bound (n : ℕ) (q : ℚ[X]) (hq : q.natDegree ≤ 9) :
    (remainderNumerator n q).natDegree ≤ 2 * n + 18 := by
  have h := remainderNumerator_natDegree_le n q
  omega

theorem shiftedRemainderNumerator_degree_nine_bound (n : ℕ) (q : ℚ[X]) (hq : q.natDegree ≤ 9) :
    (shiftedRemainderNumerator n q).natDegree ≤ 2 * n + 18 := by
  have h := shiftedRemainderNumerator_natDegree_le n q
  omega

theorem remainderNumerator_strict_proper (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X])
    (hq : q.natDegree ≤ 9) : (remainderNumerator n q).natDegree < 9 * (n + 2) := by
  have h := remainderNumerator_degree_nine_bound n q hq
  omega

theorem shiftedRemainderNumerator_strict_proper (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X])
    (hq : q.natDegree ≤ 9) : (shiftedRemainderNumerator n q).natDegree < 9 * (n + 2) := by
  have h := shiftedRemainderNumerator_degree_nine_bound n q hq
  omega

theorem shiftedRemainderNumerator_below_pole_degree (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X])
    (hq : q.natDegree ≤ 9) :
    (shiftedRemainderNumerator n q).natDegree < (polePolynomial (n + 1) ^ 9).natDegree := by
  rw [polePolynomial_pow_natDegree]
  exact shiftedRemainderNumerator_strict_proper n hn q hq

theorem chosen_shifted_remainder_degree_bound (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    (shiftedRemainderNumerator n (connectionQ n r)).natDegree ≤ 2 * n + 18 :=
  shiftedRemainderNumerator_degree_nine_bound n _ (connectionQ_natDegree_le n hn r)

theorem chosen_shifted_remainder_strict_proper (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    (shiftedRemainderNumerator n (connectionQ n r)).natDegree < 9 * (n + 2) :=
  shiftedRemainderNumerator_strict_proper n hn _ (connectionQ_natDegree_le n hn r)

theorem boundary_n_one_zero (q : ℚ[X]) : (remainderNumerator 1 q).eval 2 = 0 :=
  remainderNumerator_eval_two 1 (by decide) q

theorem boundary_n_one_strict_proper (q : ℚ[X]) (hq : q.natDegree ≤ 9) :
    (shiftedRemainderNumerator 1 q).natDegree < 27 := by
  exact shiftedRemainderNumerator_strict_proper 1 (by decide) q hq

end ZetaNine.CoefficientMapFormalTransportBounds

/- SOURCE module missions.zeta9.formalization.CoefficientMapFormalTransportNumerators; full proof bodies preserved. -/

/-!
Universal numerator transport for the actual chosen connection pair.

The actual chosen Connection pair supplies the polynomial equation.  The
proved ParameterShift identity is used only at positive regular rational
points.  Genuine product identities give the common denominator; infinitely
many such points then give the polynomial identity.  No PF-existence,
coefficient-transport, invertibility, parity or summation premise is added.
The finite independent probes are not used as proof evidence.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFormalTransportNumerators

open CoefficientMapFormalTransportData CoefficientMapFormalTransportBounds
open CoefficientMapKernelBridge CoefficientMapParameterShift
open CoefficientMapInjectivity CoefficientMapPartialFractions

theorem positiveProduct_remainder_cancellation (n : ℕ) (t : ℚ) :
    positiveProduct n t * (t - (n : ℚ) - 1) =
      (t - 1) * ∏ i ∈ range n, (t - ((i : ℚ) + 2)) := by
  have h := positiveProduct_shift n (t - 1)
  rw [sub_add_cancel] at h
  have he : positiveProduct n (t - 1) =
      ∏ i ∈ range n, (t - ((i : ℚ) + 2)) := by
    unfold positiveProduct
    apply Finset.prod_congr rfl
    intro i hi
    ring
  calc
    _ = positiveProduct n t * ((t - 1) - (n : ℚ)) := by ring
    _ = (t - 1) * positiveProduct n (t - 1) := h
    _ = _ := by rw [he]

theorem remainderNumerator_eval (n : ℕ) (q : ℚ[X]) (t : ℚ) :
    (remainderNumerator n q).eval t =
      (n.factorial : ℚ) ^ 7 *
        (∏ i ∈ range n, (t - ((i : ℚ) + 2))) *
        negativeProduct n t * q.eval ((CoefficientMapConnection.connectionV n).eval t) := by
  have he : (∏ i ∈ range n, (t + ((n : ℚ) + (i : ℚ) + 1))) =
      negativeProduct n t := by
    unfold negativeProduct
    apply Finset.prod_congr rfl
    intro i hi
    ring
  simp only [remainderNumerator, eval_mul, eval_prod, eval_sub,
    eval_add, eval_X, eval_C, eval_comp]
  rw [he]

theorem remainderNumerator_actual_cancellation (n : ℕ) (q : ℚ[X]) (t : ℚ) :
    CoefficientMap.numerator n t * (t - (n : ℚ) - 1) *
        q.eval ((CoefficientMapConnection.connectionV n).eval t) =
      (t - 1) * (remainderNumerator n q).eval t := by
  rw [remainderNumerator_eval]
  change (n.factorial : ℚ) ^ 7 * positiveProduct n t * negativeProduct n t *
      (t - (n : ℚ) - 1) * q.eval ((CoefficientMapConnection.connectionV n).eval t) = _
  calc
    _ = (n.factorial : ℚ) ^ 7 * (positiveProduct n t * (t - (n : ℚ) - 1)) *
        negativeProduct n t * q.eval ((CoefficientMapConnection.connectionV n).eval t) := by ring
    _ = _ := by rw [positiveProduct_remainder_cancellation]; ring

theorem connectionRemainder_as_actual_numerator (n : ℕ) (q : ℚ[X]) (t : ℚ)
    (hm : t - 1 ≠ 0) (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    connectionRemainder n q t =
      (remainderNumerator n q).eval t /
        ((t - 1) * (polePolynomial n).eval t) ^ 9 := by
  have hd := CoefficientMap.poleProduct_ne_zero n t hregular
  rw [polePolynomial_eval]
  unfold connectionRemainder CoefficientMap.actualR
  calc
    _ = (CoefficientMap.numerator n t * (t - (n : ℚ) - 1) *
        q.eval ((CoefficientMapConnection.connectionV n).eval t)) /
        (CoefficientMap.poleProduct n t ^ 9 * (t - 1) ^ 10) := by
      field_simp [hm, hd]
      <;> ring
    _ = ((t - 1) * (remainderNumerator n q).eval t) /
        (CoefficientMap.poleProduct n t ^ 9 * (t - 1) ^ 10) := by
      rw [remainderNumerator_actual_cancellation]
    _ = _ := by
      field_simp [hm, hd]
      <;> ring

theorem polePolynomial_successor_eval (n : ℕ) (t : ℚ) :
    (polePolynomial (n + 1)).eval t =
      (polePolynomial n).eval t * (t + ((n : ℚ) + 1)) := by
  simp only [polePolynomial_eval, CoefficientMap.poleProduct]
  rw [Finset.prod_range_succ]
  simp only [Nat.cast_add, Nat.cast_one]

theorem polePolynomial_successor_shift_eval (n : ℕ) (x : ℚ) :
    (polePolynomial (n + 1)).eval x =
      x * (polePolynomial n).eval (x + 1) := by
  simp only [polePolynomial_eval, CoefficientMap.poleProduct]
  rw [Finset.prod_range_succ']
  have he : (∏ k ∈ range (n + 1), (x + ((k + 1 : ℕ) : ℚ))) =
      ∏ k ∈ range (n + 1), (x + 1 + (k : ℚ)) := by
    apply Finset.prod_congr rfl
    intro k hk
    push_cast
    ring
  rw [he]
  simp only [Nat.cast_zero, add_zero]
  ring

theorem polePolynomial_add_two_shift_eval (n : ℕ) (x : ℚ) :
    (polePolynomial (n + 2)).eval x =
      x * (polePolynomial n).eval (x + 1) * (x + ((n : ℚ) + 2)) := by
  have h := poleProduct_parameter_shift n (x + 1)
  rw [show x + 1 - 1 = x by ring] at h
  simp only [polePolynomial_eval]
  calc
    _ = x * CoefficientMap.poleProduct n (x + 1) * (x + 1 + (n : ℚ) + 1) := by
      simpa only [show x + 1 - 1 = x by ring] using h
    _ = _ := by ring

theorem polePolynomial_successor_shift (n : ℕ) :
    polePolynomial (n + 1) = X * (polePolynomial n).comp (X + 1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℚ)).mono
  intro x hx
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
  exact polePolynomial_successor_shift_eval n x

theorem polePolynomial_add_two_shift (n : ℕ) :
    polePolynomial (n + 2) =
      X * (polePolynomial n).comp (X + 1) * (X + C ((n : ℚ) + 2)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℚ)).mono
  intro x hx
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one, eval_C]
  exact polePolynomial_add_two_shift_eval n x

theorem connectionRemainder_shifted_as_actual_numerator (n : ℕ) (q : ℚ[X]) (x : ℚ)
    (hregular : ∀ k ≤ n + 1, x + (k : ℚ) ≠ 0) :
    connectionRemainder n q (x + 1) =
      (shiftedRemainderNumerator n q).eval x / (polePolynomial (n + 1)).eval x ^ 9 := by
  have hx : x ≠ 0 := by simpa using hregular 0 (by omega)
  have hm : x + 1 - 1 ≠ 0 := by simpa only [add_sub_cancel_right] using hx
  have hreg : ∀ k ≤ n, x + 1 + (k : ℚ) ≠ 0 := by
    intro k hk
    have h := hregular (k + 1) (by omega)
    convert h using 1 <;> push_cast <;> ring
  calc
    _ = (remainderNumerator n q).eval (x + 1) /
        ((x + 1 - 1) * (polePolynomial n).eval (x + 1)) ^ 9 :=
      connectionRemainder_as_actual_numerator n q (x + 1) hm hreg
    _ = _ := by
      rw [shiftedRemainderNumerator, eval_comp, eval_add, eval_X, eval_one,
        polePolynomial_successor_shift_eval]
      rw [show x + 1 - 1 = x by ring]

theorem connectionRemainder_eval_two (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) :
    connectionRemainder n q 2 = 0 := by
  have hregular : ∀ k ≤ n, (2 : ℚ) + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (by positivity)
  rw [connectionRemainder_as_actual_numerator n q 2 (by norm_num) hregular,
    remainderNumerator_eval_two n hn q, zero_div]

theorem actual_chosen_connection_transport_positive (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (x : ℚ) (hx : 0 < x) :
    CoefficientMap.weightedR (n + 2) (X ^ r.val) x =
      CoefficientMap.weightedR n (connectionP n r) (x + 1) +
        (connectionRemainder n (connectionQ n r) (x + 1) -
          connectionRemainder n (connectionQ n r) (x + 1 + 1)) := by
  have hregular : ∀ k ≤ n + 2, x + 1 - 1 + (k : ℚ) ≠ 0 := by
    intro k hk
    rw [show x + 1 - 1 = x by ring]
    exact ne_of_gt (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k))
  have hu : (x + 1) * (x + 1 + (n : ℚ)) - ((n : ℚ) + 1) =
      x * (x + ((n + 2 : ℕ) : ℚ)) := by
    push_cast
    ring
  have h := actual_original_connection_transport n hn r.val (connectionP n r)
    (connectionQ n r) (chosen_connection_equation n hn r) (x + 1) hregular
  simpa only [CoefficientMap.weightedR, eval_pow, eval_X, hu,
    show x + 1 - 1 = x by ring] using h

private theorem three_denominator_combination (B C D x y M : ℚ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hM : M ≠ 0) :
    B / M ^ 9 + (C / (x * M) ^ 9 - D / (M * y) ^ 9) =
      (x ^ 9 * y ^ 9 * B + y ^ 9 * C - x ^ 9 * D) / (x * M * y) ^ 9 := by
  field_simp [hx, hy, hM]
  <;> ring

theorem actual_chosen_cleared_numerator_transport_eval (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (x : ℚ) (hx : 0 < x) :
    (weightedNumerator (n + 2) (X ^ r.val)).eval x =
      x ^ 9 * (x + ((n : ℚ) + 2)) ^ 9 *
          (weightedNumerator n (connectionP n r)).eval (x + 1) +
        (x + ((n : ℚ) + 2)) ^ 9 *
          (shiftedRemainderNumerator n (connectionQ n r)).eval x -
        x ^ 9 * (shiftedRemainderNumerator n (connectionQ n r)).eval (x + 1) := by
  have hreg : ∀ k ≤ n + 1, x + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k))
  have hreg1 : ∀ k ≤ n + 1, x + 1 + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (by positivity)
  have hregOld : ∀ k ≤ n, x + 1 + (k : ℚ) ≠ 0 := by
    intro k hk
    exact hreg1 k (by omega)
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : x + ((n : ℚ) + 2) ≠ 0 := ne_of_gt (by positivity)
  have hM : (polePolynomial n).eval (x + 1) ≠ 0 :=
    polePolynomial_eval_ne_zero n (x + 1) hregOld
  have hright : (polePolynomial (n + 1)).eval (x + 1) =
      (polePolynomial n).eval (x + 1) * (x + ((n : ℚ) + 2)) := by
    rw [polePolynomial_successor_eval]
    ring
  have h := actual_chosen_connection_transport_positive n hn r x hx
  rw [actual_weighted_rational_representation, actual_weighted_rational_representation,
    connectionRemainder_shifted_as_actual_numerator n (connectionQ n r) x hreg,
    connectionRemainder_shifted_as_actual_numerator n (connectionQ n r) (x + 1) hreg1,
    polePolynomial_add_two_shift_eval n x,
    polePolynomial_successor_shift_eval n x, hright] at h
  rw [three_denominator_combination
    ((weightedNumerator n (connectionP n r)).eval (x + 1))
    ((shiftedRemainderNumerator n (connectionQ n r)).eval x)
    ((shiftedRemainderNumerator n (connectionQ n r)).eval (x + 1))
    x (x + ((n : ℚ) + 2)) ((polePolynomial n).eval (x + 1)) hx0 hy0 hM] at h
  exact (div_left_inj' (pow_ne_zero 9 (mul_ne_zero (mul_ne_zero hx0 hM) hy0))).mp h

/-- Actual universal polynomial transport, with the chosen pair and no relation premise. -/
theorem actual_chosen_cleared_numerator_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    weightedNumerator (n + 2) (X ^ r.val) =
      X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 *
          (weightedNumerator n (connectionP n r)).comp (X + 1) +
        (X + C ((n : ℚ) + 2)) ^ 9 *
          shiftedRemainderNumerator n (connectionQ n r) -
        X ^ 9 * (shiftedRemainderNumerator n (connectionQ n r)).comp (X + 1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℚ)).mono
  intro x hx
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_comp, eval_one]
  exact actual_chosen_cleared_numerator_transport_eval n hn r x hx

end ZetaNine.CoefficientMapFormalTransportNumerators

/- SOURCE module missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions; full proof bodies preserved. -/

/-!
Fixed-nine partial fractions for an arbitrary actual rational polynomial
numerator. The coefficients are exactly FormalTransportData's cleared
formal-series jets. Strict properness is a degree condition on this A;
no partial-fraction existence or abstract coefficient array is assumed.

The truncation, coprimality and pole-degree tools come from the already
proved special-numerator PF modules. This adds their numerator-independent
argument without changing any frozen source. It does not prove transport,
integer heights, a zeta-independence assertion or irrationality.
Native source/type/value/boundary evidence is recorded separately in
verification/formalization-coefficient-map-numerator-pf-2026-10-04/.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapNumeratorPartialFractions

open CoefficientMapInjectivity CoefficientMapPartialFractions
open CoefficientMapFormalTransportData

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

/- SOURCE module missions.zeta9.formalization.CoefficientMapFormalTransportJets; full proof bodies preserved. -/

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

/- SOURCE module missions.zeta9.formalization.CoefficientMapMatrix; full proof bodies preserved. -/

/-!
The actual round-seven F matrix uses monomial rows and formal-output columns.
The inverse coefficients are rational, including for integer output targets.
This source is prepared offline and awaits its first actual Lean compilation.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Matrix
open Polynomial

namespace ZetaNine.CoefficientMapMatrix

open CoefficientMapAggregate CoefficientMapKernelBridge

theorem quarticAggregate_eq_row_vector (n : ℕ) (c : Fin 5 → ℚ) :
    quarticAggregateLinearMap n c = c ᵥ* actualFMatrix n := by
  classical
  calc
    quarticAggregateLinearMap n c =
        aggregateLinearMap n (∑ i : Fin 5, c i • (X ^ i.val : ℚ[X])) := by
      simp only [quartic_aggregate_is_actual, coordinatePolynomial, smul_eq_C_mul]
      rfl
    _ = ∑ i : Fin 5, c i • aggregateLinearMap n (X ^ i.val : ℚ[X]) := by
      rw [map_sum]
      simp only [map_smul]
    _ = c ᵥ* actualFMatrix n := by
      rw [Matrix.vecMul_eq_sum]
      rfl

theorem coordinatePolynomial_single_one (i : Fin 5) :
    coordinatePolynomial (Pi.single i 1) = (X : ℚ[X]) ^ i.val := by
  classical
  simp [coordinatePolynomial, Pi.single_apply]

/-- Mathlib's standard column-action matrix is the transpose of the paper's F. -/
theorem column_action_matrix_is_transpose (n : ℕ) :
    LinearMap.toMatrix' (quarticAggregateLinearMap n) = (actualFMatrix n)ᵀ := by
  ext i j
  rw [LinearMap.toMatrix'_apply, quartic_aggregate_is_actual, coordinatePolynomial_single_one]
  rfl

theorem actualFMatrix_row_action_bijective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    Function.Bijective (actualFMatrix n).vecMul := by
  have heq : (actualFMatrix n).vecMul = quarticAggregateLinearMap n := by
    funext c
    exact (quarticAggregate_eq_row_vector n c).symm
  rw [heq]
  exact original_five_dimensional_map_bijective n hn2 hn

theorem actualFMatrix_det_isUnit (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    IsUnit (actualFMatrix n).det := by
  have hunit : IsUnit (actualFMatrix n) := Matrix.vecMul_surjective_iff_isUnit.mp
    (actualFMatrix_row_action_bijective n hn2 hn).surjective
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit

theorem actualFMatrix_det_ne_zero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    (actualFMatrix n).det ≠ 0 := (actualFMatrix_det_isUnit n hn2 hn).ne_zero

theorem inverseMultiplier_coordinates_eq_row_inverse (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    polynomialCoordinates (inverseMultiplier n hn2 hn b) = b ᵥ* (actualFMatrix n)⁻¹ := by
  have hrow : polynomialCoordinates (inverseMultiplier n hn2 hn b) ᵥ* actualFMatrix n = b := by
    rw [← quarticAggregate_eq_row_vector, quartic_aggregate_is_actual,
      polynomial_restore _ (inverseMultiplier_natDegree_le n hn2 hn b),
      inverseMultiplier_actual_aggregate]
  have h := congrArg (fun c : Fin 5 → ℚ => c ᵥ* (actualFMatrix n)⁻¹) hrow
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (actualFMatrix_det_isUnit n hn2 hn),
    Matrix.vecMul_one] using h

theorem inverseMultiplier_eq_coordinatePolynomial_row_inverse (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b : Fin 5 → ℚ) :
    inverseMultiplier n hn2 hn b = coordinatePolynomial (b ᵥ* (actualFMatrix n)⁻¹) := by
  rw [← inverseMultiplier_coordinates_eq_row_inverse n hn2 hn b,
    polynomial_restore _ (inverseMultiplier_natDegree_le n hn2 hn b)]

/-- The genuine two selected output directions are B and rho9. -/
theorem selectedIntegerPair_mul_selection (b a : ℤ) :
    selectedIntegerPair b a ᵥ* selectionMatrix = selectedIntegerOutput b a := by
  have h04 : (0 : Fin 5) ≠ 4 := by decide
  ext j
  fin_cases j <;>
    norm_num [Matrix.vecMul_apply_eq_sum, selectionMatrix, selectedIntegerPair,
      selectedIntegerOutput, Fin.sum_univ_succ, h04]

theorem selectedIntegerMultiplier_coordinates (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    polynomialCoordinates (selectedIntegerMultiplier n hn2 hn b a) =
      (selectedIntegerPair b a ᵥ* selectionMatrix) ᵥ* (actualFMatrix n)⁻¹ := by
  rw [selectedIntegerMultiplier, inverseMultiplier_coordinates_eq_row_inverse,
    selectedIntegerPair_mul_selection]

theorem selectedIntegerMultiplier_coordinates_product (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    polynomialCoordinates (selectedIntegerMultiplier n hn2 hn b a) =
      selectedIntegerPair b a ᵥ* (selectionMatrix * (actualFMatrix n)⁻¹) := by
  rw [selectedIntegerMultiplier_coordinates, Matrix.vecMul_vecMul]

theorem selectedIntegerMultiplier_natDegree_le (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    (selectedIntegerMultiplier n hn2 hn b a).natDegree ≤ 4 :=
  inverseMultiplier_natDegree_le n hn2 hn (selectedIntegerOutput b a)

theorem selectedIntegerMultiplier_actual_output (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    aggregate n (selectedIntegerMultiplier n hn2 hn b a) = selectedIntegerOutput b a :=
  inverseMultiplier_actual_aggregate n hn2 hn (selectedIntegerOutput b a)

theorem selectedIntegerMultiplier_five_actual_coordinates (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    CoefficientMapFiniteSum.constantTerm n (selectedIntegerMultiplier n hn2 hn b a) = (b : ℚ) ∧
      CoefficientMapFiniteSum.rho n 3 (selectedIntegerMultiplier n hn2 hn b a) = 0 ∧
      CoefficientMapFiniteSum.rho n 5 (selectedIntegerMultiplier n hn2 hn b a) = 0 ∧
      CoefficientMapFiniteSum.rho n 7 (selectedIntegerMultiplier n hn2 hn b a) = 0 ∧
      CoefficientMapFiniteSum.rho n 9 (selectedIntegerMultiplier n hn2 hn b a) = (a : ℚ) := by
  have h := selectedIntegerMultiplier_actual_output n hn2 hn b a
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  exact ⟨by simpa [aggregate, selectedIntegerOutput] using h0,
    by simpa [aggregate, selectedIntegerOutput] using h1,
    by simpa [aggregate, selectedIntegerOutput] using h2,
    by simpa [aggregate, selectedIntegerOutput] using h3,
    by simpa [aggregate, selectedIntegerOutput] using h4⟩

theorem selected_prescribed_L (b a : ℤ) :
    prescribedL (selectedIntegerOutput b a) =
      (b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9 := by
  norm_num [prescribedL, selectedIntegerOutput, Fin.ext_iff]

theorem selectedIntegerMultiplier_actual_exact_L (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    CoefficientMapSummation.exactL n (selectedIntegerMultiplier n hn2 hn b a) =
      (b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9 := by
  rw [selectedIntegerMultiplier, inverseMultiplier_exact_L, selected_prescribed_L]

theorem selectedIntegerMultiplier_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
      ((t + 1 : ℕ) : ℚ) : ℝ))
        ((b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖) := by
  simpa only [selectedIntegerMultiplier, selected_prescribed_L] using
    inverseMultiplier_actual_HasSum_and_absolute n hn2 hn (selectedIntegerOutput b a)

end ZetaNine.CoefficientMapMatrix

/- SOURCE module missions.zeta9.formalization.CoefficientMapFormalTransportOutputs; full proof bodies preserved. -/

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
open scoped BigOperators Matrix
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
    Nat.cast_add, Nat.cast_one, add_comm (1 : ℚ)] using h.symm

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

open scoped BigOperators Matrix
open Finset Polynomial
open ZetaNine.CoefficientMapFormalTransportOutputs
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapFormalTransportData

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    actualFMatrix (n + 2) = connectionGamma n * actualFMatrix n := by
  exact ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport n hn

#print axioms solution
