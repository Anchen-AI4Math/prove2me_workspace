import CoefficientMap
import AnalyticFactorialBounds

/-!
UNCOMPILED SOURCE preparation. These endpoints start from the actual
CoefficientMap.numerator/poleProduct products. The factorial formula is a
conclusion, never a hypothesis. No logarithmic bound or moment estimate is
claimed to have passed Lean or kernel verification.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open scoped BigOperators
open Finset

namespace ZetaNine.AnalyticRationalFactorial

theorem rational_factorial_ne_zero (n : ℕ) : (n.factorial : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero n

theorem ascending_product_factorial (a m : ℕ) (ha : 1 ≤ a) :
    (∏ i ∈ range m, ((a : ℚ) + (i : ℚ))) =
      ((a + m - 1).factorial : ℚ) / ((a - 1).factorial : ℚ) := by
  have h := Nat.factorial_mul_ascFactorial' a m (by omega : 0 < a)
  rw [Nat.ascFactorial_eq_prod_range] at h
  have hc := congrArg (fun z : ℕ => (z : ℚ)) h
  simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_add] at hc
  apply (eq_div_iff (rational_factorial_ne_zero (a - 1))).mpr
  simpa only [mul_comm] using hc

theorem actual_falling_product_factorial (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) =
      ((k - 1).factorial : ℚ) / ((k - n - 1).factorial : ℚ) := by
  have hk1 : 1 ≤ k := by omega
  have hpred : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
    exact_mod_cast (Nat.cast_sub hk1 : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1)
  have hproduct :
      (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) =
        ((k - 1).descFactorial n : ℚ) := by
    calc
      _ = ∏ i ∈ range n, (((k - 1 : ℕ) : ℚ) - (i : ℚ)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hpred]
        ring
      _ = _ := by
        rw [Finset.prod_range_natCast_sub, ← Nat.descFactorial_eq_prod_range]
  rw [hproduct]
  have h := Nat.factorial_mul_descFactorial (by omega : n ≤ k - 1)
  have hc := congrArg (fun z : ℕ => (z : ℚ)) h
  have hindex : k - 1 - n = k - n - 1 := by omega
  simp only [Nat.cast_mul, hindex] at hc
  apply (eq_div_iff (rational_factorial_ne_zero (k - n - 1))).mpr
  simpa only [mul_comm] using hc

theorem actual_rising_product_factorial (n k : ℕ) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) =
      ((k + 2 * n).factorial : ℚ) / ((k + n).factorial : ℚ) := by
  have h := ascending_product_factorial (k + n + 1) n (by omega)
  have htop : k + n + 1 + n - 1 = k + 2 * n := by omega
  have hbot : k + n + 1 - 1 = k + n := by omega
  rw [htop, hbot] at h
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using h

theorem actual_poleProduct_factorial (n k : ℕ) (hk : 1 ≤ k) :
    CoefficientMap.poleProduct n (k : ℚ) =
      ((k + n).factorial : ℚ) / ((k - 1).factorial : ℚ) := by
  have h := ascending_product_factorial k (n + 1) hk
  have htop : k + (n + 1) - 1 = k + n := by omega
  simpa only [CoefficientMap.poleProduct, htop] using h

theorem actualR_factorial (n k : ℕ) (hk : n < k) :
    CoefficientMap.actualR n (k : ℚ) =
      (n.factorial : ℚ) ^ 7 * ((k - 1).factorial : ℚ) ^ 10 *
        ((k + 2 * n).factorial : ℚ) /
      (((k - n - 1).factorial : ℚ) * ((k + n).factorial : ℚ) ^ 10) := by
  have hk1 : 1 ≤ k := by omega
  unfold CoefficientMap.actualR CoefficientMap.numerator
  rw [actual_falling_product_factorial n k hk,
    actual_rising_product_factorial n k, actual_poleProduct_factorial n k hk1]
  field_simp [rational_factorial_ne_zero]

theorem actualR_factorial_real (n k : ℕ) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      (n.factorial : ℝ) ^ 7 * ((k - 1).factorial : ℝ) ^ 10 *
        ((k + 2 * n).factorial : ℝ) /
      (((k - n - 1).factorial : ℝ) * ((k + n).factorial : ℝ) ^ 10) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (actualR_factorial n k hk)
  push_cast at h
  exact h

theorem actualR_pos (n k : ℕ) (hk : n < k) :
    0 < CoefficientMap.actualR n (k : ℚ) := by
  rw [actualR_factorial n k hk]
  have h0 : (0 : ℚ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 : (0 : ℚ) < (k - 1).factorial := by
    exact_mod_cast Nat.factorial_pos (k - 1)
  have h2 : (0 : ℚ) < (k + 2 * n).factorial := by
    exact_mod_cast Nat.factorial_pos (k + 2 * n)
  have h3 : (0 : ℚ) < (k - n - 1).factorial := by
    exact_mod_cast Nat.factorial_pos (k - n - 1)
  have h4 : (0 : ℚ) < (k + n).factorial := by
    exact_mod_cast Nat.factorial_pos (k + n)
  positivity

theorem actualR_real_pos (n k : ℕ) (hk : n < k) :
    0 < (CoefficientMap.actualR n (k : ℚ) : ℝ) := by
  exact_mod_cast actualR_pos n k hk

/-- Exact log identity after removing the two predecessor factorials. -/
theorem actualR_log_factorial (n k : ℕ) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      7 * Real.log (n.factorial : ℝ) + 10 * Real.log (k.factorial : ℝ) +
        Real.log ((k + 2 * n).factorial : ℝ) -
        Real.log ((k - n).factorial : ℝ) -
        10 * Real.log ((k + n).factorial : ℝ) -
        10 * Real.log (k : ℝ) + Real.log ((k - n : ℕ) : ℝ) := by
  have h0 := AnalyticFactorialBounds.real_factorial_pos n
  have h1 := AnalyticFactorialBounds.real_factorial_pos (k - 1)
  have h2 := AnalyticFactorialBounds.real_factorial_pos (k + 2 * n)
  have h3 := AnalyticFactorialBounds.real_factorial_pos (k - n - 1)
  have h4 := AnalyticFactorialBounds.real_factorial_pos (k + n)
  rw [actualR_factorial_real n k hk,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) h2.ne',
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul h3.ne' (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
  rw [AnalyticFactorialBounds.log_factorial_pred k (by omega)]
  have hpred : k - n - 1 = (k - n) - 1 := by omega
  rw [hpred, AnalyticFactorialBounds.log_factorial_pred (k - n) (by omega)]
  ring

end ZetaNine.AnalyticRationalFactorial

#print axioms ZetaNine.AnalyticRationalFactorial.ascending_product_factorial
#print axioms ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial
#print axioms ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial
#print axioms ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial
#print axioms ZetaNine.AnalyticRationalFactorial.actualR_factorial
#print axioms ZetaNine.AnalyticRationalFactorial.actualR_factorial_real
#print axioms ZetaNine.AnalyticRationalFactorial.actualR_pos
#print axioms ZetaNine.AnalyticRationalFactorial.actualR_real_pos
#print axioms ZetaNine.AnalyticRationalFactorial.actualR_log_factorial
