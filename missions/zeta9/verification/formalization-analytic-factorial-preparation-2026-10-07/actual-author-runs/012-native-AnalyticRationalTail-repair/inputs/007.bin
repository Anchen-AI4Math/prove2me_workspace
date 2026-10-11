import AnalyticRationalFactorial
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
UNCOMPILED SOURCE preparation. Direct product bound for the actual tail
k >= 2n, n >= 1. No factorial-formula assumption, summability assumption,
Stirling asymptotic, or infinite-tail estimate is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open scoped BigOperators
open Finset

namespace ZetaNine.AnalyticRationalTail

theorem actual_falling_product_le (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) ≤ (k : ℚ) ^ n := by
  calc
    _ ≤ ∏ _i ∈ range n, (k : ℚ) := by
      apply Finset.prod_le_prod
      · intro i hi
        have hi1 : i + 1 ≤ k := by have := mem_range.mp hi; omega
        have hir : (i : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hi1
        linarith
      · intro i hi
        have hi0 : (0 : ℚ) ≤ i := by positivity
        linarith
    _ = _ := by simp

theorem actual_rising_product_tail_le (n k : ℕ) (hk : 2 * n ≤ k) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) ≤
      (2 * (k : ℚ)) ^ n := by
  calc
    _ ≤ ∏ _i ∈ range n, (2 * (k : ℚ)) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hi1 : n + i + 1 ≤ k := by have := mem_range.mp hi; omega
        have hir : (n : ℚ) + (i : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hi1
        linarith
    _ = _ := by simp

theorem actual_poleProduct_ge (n k : ℕ) :
    (k : ℚ) ^ (n + 1) ≤ CoefficientMap.poleProduct n (k : ℚ) := by
  unfold CoefficientMap.poleProduct
  calc
    (k : ℚ) ^ (n + 1) = ∏ _i ∈ range (n + 1), (k : ℚ) := by simp
    _ ≤ ∏ i ∈ range (n + 1), ((k : ℚ) + i) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact le_add_of_nonneg_right (Nat.cast_nonneg i)

theorem actualR_tail_bound_rational (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    CoefficientMap.actualR n (k : ℚ) ≤
      (n.factorial : ℚ) ^ 7 * (2 : ℚ) ^ n / (k : ℚ) ^ (7 * n + 9) := by
  have hkn : n < k := by omega
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hfac : (0 : ℚ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hfall := actual_falling_product_le n k hkn
  have hrise := actual_rising_product_tail_le n k hk
  have hfall0 :
      0 ≤ ∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1)) := by
    apply Finset.prod_nonneg
    intro i hi
    have hi1 : i + 1 ≤ k := by have := mem_range.mp hi; omega
    have hir : (i : ℚ) + 1 ≤ (k : ℚ) := by exact_mod_cast hi1
    linarith
  have hrise0 :
      0 ≤ ∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1)) := by
    apply Finset.prod_nonneg
    intro i hi
    positivity
  have hnum : CoefficientMap.numerator n (k : ℚ) ≤
      (n.factorial : ℚ) ^ 7 * (k : ℚ) ^ n * (2 * (k : ℚ)) ^ n := by
    unfold CoefficientMap.numerator
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hfall (by positivity)) hrise hrise0 (by positivity)
  have hbase := actual_poleProduct_ge n k
  have hbase0 : (0 : ℚ) < (k : ℚ) ^ (n + 1) := by positivity
  have hpole0 : (0 : ℚ) < CoefficientMap.poleProduct n (k : ℚ) :=
    lt_of_lt_of_le hbase0 hbase
  have hden := pow_le_pow_left₀ hbase0.le hbase 9
  have hpow : ((k : ℚ) ^ (n + 1)) ^ 9 =
      (k : ℚ) ^ (7 * n + 9) * (k : ℚ) ^ n * (k : ℚ) ^ n := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  unfold CoefficientMap.actualR
  calc
    CoefficientMap.numerator n (k : ℚ) /
        CoefficientMap.poleProduct n (k : ℚ) ^ 9 ≤
      ((n.factorial : ℚ) ^ 7 * (k : ℚ) ^ n * (2 * (k : ℚ)) ^ n) /
        CoefficientMap.poleProduct n (k : ℚ) ^ 9 :=
      div_le_div_of_nonneg_right hnum (pow_pos hpole0 9).le
    _ ≤ ((n.factorial : ℚ) ^ 7 * (k : ℚ) ^ n * (2 * (k : ℚ)) ^ n) /
        ((k : ℚ) ^ (n + 1)) ^ 9 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      rw [mul_pow, hpow]
      field_simp [hk0.ne']

theorem actualR_tail_bound (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n / (k : ℝ) ^ (7 * n + 9) := by
  have h := actualR_tail_bound_rational n k hn hk
  have hc : (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (( (n.factorial : ℚ) ^ 7 * (2 : ℚ) ^ n / (k : ℚ) ^ (7 * n + 9) : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at hc
  exact hc

theorem actual_tail_weight_le (n k : ℕ) (hk : 2 * n ≤ k) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ (3 / 2 : ℝ) * (k : ℝ) ^ 2 := by
  have h : 2 * (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  nlinarith

end ZetaNine.AnalyticRationalTail

#print axioms ZetaNine.AnalyticRationalTail.actual_falling_product_le
#print axioms ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le
#print axioms ZetaNine.AnalyticRationalTail.actual_poleProduct_ge
#print axioms ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational
#print axioms ZetaNine.AnalyticRationalTail.actualR_tail_bound
#print axioms ZetaNine.AnalyticRationalTail.actual_tail_weight_le
