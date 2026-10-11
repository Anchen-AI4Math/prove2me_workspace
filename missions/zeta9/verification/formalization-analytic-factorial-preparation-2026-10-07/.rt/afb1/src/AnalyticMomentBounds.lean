import AnalyticRationalLogBound
import AnalyticRationalTail
import AnalyticPSeriesTail

/-!
UNCOMPILED SOURCE preparation. Actual raw moments, starting at k = m+1,
with the product's first n zero terms kept in the sequence. Summability is
proved by actual tail comparison rather than assumed or imported through
the partial-fraction / exactL proof chain.

This preparation reaches a genuine compact plus factorial-tail estimate.
The final exponential tail simplification and uniform changing-coefficient
estimate remain separate endpoints to add; this file does not assert Z9.A.
-/

set_option autoImplicit false
set_option maxHeartbeats 2600000

noncomputable section
open scoped BigOperators
open Finset

namespace ZetaNine.AnalyticMomentBounds

def actualMomentTerm (n r k : ℕ) : ℝ :=
  (CoefficientMap.actualR n (k : ℚ) : ℝ) *
    ((k : ℝ) * ((k : ℝ) + (n : ℝ))) ^ r

def actualMomentSequence (n r m : ℕ) : ℝ := actualMomentTerm n r (m + 1)

def actualMoment (n r : ℕ) : ℝ := ∑' m : ℕ, actualMomentSequence n r m

def tailPower (n r : ℕ) : ℕ := 7 * n + 9 - 2 * r

def tailCoefficient (n r : ℕ) : ℝ :=
  (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n * (3 / 2 : ℝ) ^ r

theorem actualR_zero_of_pos_le (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.actualR n (k : ℚ) = 0 := by
  have hpred : ((k - 1 : ℕ) : ℚ) + 1 = (k : ℚ) := by
    exact_mod_cast (Nat.sub_add_cancel hk)
  have hfall : (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) = 0 := by
    apply Finset.prod_eq_zero (mem_range.mpr (by omega : k - 1 < n))
    rw [hpred]
    ring
  simp only [CoefficientMap.actualR, CoefficientMap.numerator, hfall,
    mul_zero, zero_mul, zero_div]

theorem actualMomentTerm_zero_of_pos_le (n r k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    actualMomentTerm n r k = 0 := by
  simp only [actualMomentTerm, actualR_zero_of_pos_le n k hk hkn,
    Rat.cast_zero, zero_mul]

theorem actualMomentTerm_nonneg (n r k : ℕ) (hk : 1 ≤ k) :
    0 ≤ actualMomentTerm n r k := by
  by_cases hkn : k ≤ n
  · rw [actualMomentTerm_zero_of_pos_le n r k hk hkn]
  · have hR := AnalyticRationalFactorial.actualR_real_pos n k (by omega : n < k)
    unfold actualMomentTerm
    positivity

theorem actualMomentSequence_nonneg (n r m : ℕ) :
    0 ≤ actualMomentSequence n r m :=
  actualMomentTerm_nonneg n r (m + 1) (by omega)

theorem actual_compact_weight_le (n k : ℕ) (hk : k ≤ 2 * n) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ 6 * (n : ℝ) ^ 2 := by
  have h : (k : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hp := mul_le_mul h (by linarith : (k : ℝ) + n ≤ 3 * (n : ℝ))
    (by positivity : (0 : ℝ) ≤ (k : ℝ) + n)
    (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
  nlinarith

theorem actual_compact_momentTerm_bound (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    actualMomentTerm n r k ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 9 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := by
  have hR := AnalyticRationalLogBound.actualR_compact_bound n k hn hk hk2
  have hu := actual_compact_weight_le n k hk2
  have hu0 : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + n) := by positivity
  have hp := pow_le_pow_left₀ hu0 hu r
  have hterm := mul_le_mul hR hp (pow_nonneg hu0 r) (by positivity)
  have hc : 4 * (6 : ℝ) ^ r ≤ 5184 := by interval_cases r <;> norm_num
  have he :
      (4 * Real.exp 18 * (n : ℝ) ^ 9 * Real.exp (-(2641 / 250 : ℝ) * n)) *
        (6 * (n : ℝ) ^ 2) ^ r =
      (4 * (6 : ℝ) ^ r) *
        (Real.exp 18 * (n : ℝ) ^ 9 * (n : ℝ) ^ (2 * r) *
          Real.exp (-(2641 / 250 : ℝ) * n)) := by
    rw [mul_pow, ← pow_mul]
    ring
  unfold actualMomentTerm
  exact hterm.trans (he.le.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (by positivity)))

theorem tailPower_ge (n r : ℕ) (hr : r ≤ 4) :
    7 * n + 1 ≤ tailPower n r := by
  unfold tailPower
  omega

theorem tailCoefficient_nonneg (n r : ℕ) : 0 ≤ tailCoefficient n r := by
  unfold tailCoefficient
  positivity

theorem actual_tail_momentTerm_bound (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : 2 * n ≤ k) :
    actualMomentTerm n r k ≤ tailCoefficient n r / (k : ℝ) ^ tailPower n r := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hR := AnalyticRationalTail.actualR_tail_bound n k hn hk
  have hu := AnalyticRationalTail.actual_tail_weight_le n k hk
  have hu0 : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + n) := by positivity
  have hp := pow_le_pow_left₀ hu0 hu r
  have hterm := mul_le_mul hR hp (pow_nonneg hu0 r) (by positivity)
  have hindex : 7 * n + 9 = tailPower n r + 2 * r := by
    unfold tailPower
    omega
  have hpow : (k : ℝ) ^ (7 * n + 9) =
      (k : ℝ) ^ tailPower n r * (k : ℝ) ^ (2 * r) := by
    calc
      _ = (k : ℝ) ^ (tailPower n r + 2 * r) := congrArg (fun a : ℕ => (k : ℝ) ^ a) hindex
      _ = _ := pow_add _ _ _
  have he :
      ((n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n / (k : ℝ) ^ (7 * n + 9)) *
        ((3 / 2 : ℝ) * (k : ℝ) ^ 2) ^ r =
      tailCoefficient n r / (k : ℝ) ^ tailPower n r := by
    unfold tailCoefficient
    rw [mul_pow, ← pow_mul, hpow]
    field_simp [hk0.ne']
    ring
  unfold actualMomentTerm
  exact hterm.trans_eq he

theorem actualMomentSequence_summable (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (actualMomentSequence n r) := by
  have hs : 2 ≤ tailPower n r := by have := tailPower_ge n r hr; omega
  have hmajor : Summable (fun m : ℕ =>
      tailCoefficient n r / ((m + 2 * n : ℕ) : ℝ) ^ tailPower n r) := by
    simpa only [mul_one_div] using
      (AnalyticPSeriesTail.reciprocal_power_tail_summable (2 * n) (tailPower n r) hs).mul_left
        (tailCoefficient n r)
  have htail : Summable (fun m : ℕ => actualMomentSequence n r (m + (2 * n - 1))) := by
    apply Summable.of_nonneg_of_le
      (fun m => actualMomentSequence_nonneg n r (m + (2 * n - 1))) _ hmajor
    intro m
    have hindex : m + (2 * n - 1) + 1 = m + 2 * n := by omega
    simpa only [actualMomentSequence, hindex] using
      actual_tail_momentTerm_bound n r (m + 2 * n) hn hr (by omega)
  exact (summable_nat_add_iff (2 * n - 1)).mp htail

theorem actualMomentSequence_norm_summable (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (fun m : ℕ => ‖actualMomentSequence n r m‖) :=
  (actualMomentSequence_summable n r hn hr).norm

theorem actual_compact_moment_sum_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑ m ∈ range (2 * n - 1), actualMomentSequence n r m) ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := by
  have hindex : 2 * n - 1 = n + (n - 1) := by omega
  rw [hindex, Finset.sum_range_add]
  have hzero : (∑ m ∈ range n, actualMomentSequence n r m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    exact actualMomentTerm_zero_of_pos_le n r (m + 1) (by omega)
      (by have := mem_range.mp hm; omega)
  rw [hzero, zero_add]
  let B : ℝ := 5184 * Real.exp 18 * (n : ℝ) ^ 9 * (n : ℝ) ^ (2 * r) *
    Real.exp (-(2641 / 250 : ℝ) * n)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    (∑ m ∈ range (n - 1), actualMomentSequence n r (m + n)) ≤
        ∑ _m ∈ range (n - 1), B := by
      apply Finset.sum_le_sum
      intro m hm
      have hm0 := mem_range.mp hm
      exact actual_compact_momentTerm_bound n r (m + n + 1) hn hr (by omega) (by omega)
    _ = ((n - 1 : ℕ) : ℝ) * B := by simp
    _ ≤ (n : ℝ) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 1) hB
    _ = _ := by dsimp [B]; ring

theorem actual_tail_moment_sum_factorial_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) ≤
      tailCoefficient n r / (2 * (n : ℝ)) ^ tailPower n r * (9 / 7 : ℝ) := by
  have hs : 2 ≤ tailPower n r := by have := tailPower_ge n r hr; omega
  have hmajor : Summable (fun m : ℕ =>
      tailCoefficient n r / ((m + 2 * n : ℕ) : ℝ) ^ tailPower n r) := by
    simpa only [mul_one_div] using
      (AnalyticPSeriesTail.reciprocal_power_tail_summable (2 * n) (tailPower n r) hs).mul_left
        (tailCoefficient n r)
  have hminor : Summable (fun m : ℕ => actualMomentTerm n r (m + 2 * n)) := by
    apply Summable.of_nonneg_of_le _ _ hmajor
    · intro m
      exact actualMomentTerm_nonneg n r (m + 2 * n) (by omega)
    · intro m
      exact actual_tail_momentTerm_bound n r (m + 2 * n) hn hr (by omega)
  have hterm : (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) ≤
      ∑' m : ℕ, tailCoefficient n r / ((m + 2 * n : ℕ) : ℝ) ^ tailPower n r :=
    Summable.tsum_le_tsum
      (fun m => actual_tail_momentTerm_bound n r (m + 2 * n) hn hr (by omega)) hminor hmajor
  have hp := AnalyticPSeriesTail.reciprocal_power_tail_bound_factored
    (2 * n) (tailPower n r) (by omega) hs
  have hs1 : (0 : ℝ) < ((tailPower n r - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < tailPower n r - 1 by omega)
  have hden : 7 * (n : ℝ) ≤ ((tailPower n r - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 7 * n ≤ tailPower n r - 1 by have := tailPower_ge n r hr; omega)
  have hratio : 1 + (2 * n : ℝ) / ((tailPower n r - 1 : ℕ) : ℝ) ≤ (9 / 7 : ℝ) := by
    have h := (div_le_iff₀ hs1).mpr (by nlinarith :
      (2 * n : ℝ) ≤ (2 / 7 : ℝ) * ((tailPower n r - 1 : ℕ) : ℝ))
    linarith
  have hratio_nat :
      1 + ((2 * n : ℕ) : ℝ) / ((tailPower n r - 1 : ℕ) : ℝ) ≤ (9 / 7 : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hratio
  calc
    (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) ≤
        ∑' m : ℕ, tailCoefficient n r / ((m + 2 * n : ℕ) : ℝ) ^ tailPower n r := hterm
    _ = tailCoefficient n r * (∑' m : ℕ, 1 / ((m + 2 * n : ℕ) : ℝ) ^ tailPower n r) := by
      rw [tsum_mul_left]
      congr 1
      funext m
      rw [mul_one_div]
    _ ≤ tailCoefficient n r *
        (1 / ((2 * n : ℕ) : ℝ) ^ tailPower n r *
          (1 + ((2 * n : ℕ) : ℝ) / ((tailPower n r - 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hp (tailCoefficient_nonneg n r)
    _ ≤ tailCoefficient n r *
        (1 / ((2 * n : ℕ) : ℝ) ^ tailPower n r * (9 / 7 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (tailCoefficient_nonneg n r)
      exact mul_le_mul_of_nonneg_left hratio_nat (by positivity)
    _ = _ := by push_cast; ring

theorem actualMoment_eq_compact_add_tail (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    actualMoment n r = (∑ m ∈ range (2 * n - 1), actualMomentSequence n r m) +
      ∑' m : ℕ, actualMomentTerm n r (m + 2 * n) := by
  have h := (actualMomentSequence_summable n r hn hr).sum_add_tsum_nat_add (2 * n - 1)
  have hindex : ∀ m : ℕ, m + (2 * n - 1) + 1 = m + 2 * n := by intro m; omega
  simpa only [actualMoment, actualMomentSequence, hindex] using h.symm

theorem actualMoment_compact_add_factorial_tail_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    actualMoment n r ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) +
      tailCoefficient n r / (2 * (n : ℝ)) ^ tailPower n r * (9 / 7 : ℝ) := by
  rw [actualMoment_eq_compact_add_tail n r hn hr]
  exact add_le_add (actual_compact_moment_sum_bound n r hn hr)
    (actual_tail_moment_sum_factorial_bound n r hn hr)

end ZetaNine.AnalyticMomentBounds

#print axioms ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le
#print axioms ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable
#print axioms ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable
#print axioms ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound
#print axioms ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound
#print axioms ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail
#print axioms ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound
