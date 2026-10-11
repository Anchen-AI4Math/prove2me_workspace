import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
SOURCE preparation: elementary factorial logarithm bounds for the actual
ZetaNine rational function. This file has not been compiled or kernel checked.
Every endpoint has a complete proof body; no estimate is an input hypothesis.

The lower bound also holds at zero because Real.log 0 = 0. The upper bound is
stated only for n >= 1. Both induction steps use log x <= x - 1, applied to
the two reciprocal ratios n/(n+1) and (n+1)/n.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace ZetaNine.AnalyticFactorialBounds

theorem real_factorial_pos (n : ℕ) : 0 < (n.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

theorem log_factorial_succ (n : ℕ) :
    Real.log ((n + 1).factorial : ℝ) =
      Real.log ((n : ℝ) + 1) + Real.log (n.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  exact Real.log_mul (by positivity) (real_factorial_pos n).ne'

/-- The induction increment for the lower factorial bound. -/
theorem log_successor_increment_upper (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hn1 hn0)
  rw [Real.log_div hn1.ne' hn0.ne'] at h
  calc
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤
        (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left h hn0.le
    _ = 1 := by field_simp [hn0.ne']; ring

/-- The induction increment for the upper factorial bound. -/
theorem log_successor_increment_lower (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ ((n : ℝ) + 1) *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
  rw [Real.log_div hn0.ne' hn1.ne'] at h
  have hmul := mul_le_mul_of_nonneg_left h hn1.le
  have he : ((n : ℝ) + 1) * ((n : ℝ) / ((n : ℝ) + 1) - 1) = -1 := by
    field_simp [hn1.ne']
    ring
  rw [he] at hmul
  nlinarith

/-- Genuine lower bound, including n = 0. -/
theorem log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log (n : ℝ) - n ≤ Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      norm_num
    · have hn1 : 1 ≤ n := by omega
      have hstep := log_successor_increment_upper n hn1
      rw [Nat.succ_eq_add_one, log_factorial_succ, Nat.cast_add, Nat.cast_one]
      nlinarith

/-- Genuine upper bound, with the positive-index domain used below. -/
theorem log_factorial_upper (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      ((n : ℝ) + 1) * Real.log (n : ℝ) - n + 1 := by
  have hall : ∀ m : ℕ, 1 ≤ m →
      Real.log (m.factorial : ℝ) ≤
        ((m : ℝ) + 1) * Real.log (m : ℝ) - m + 1 := by
    intro m
    induction m with
    | zero => intro hm; omega
    | succ m ih =>
      intro hm
      by_cases hm0 : m = 0
      · subst m
        norm_num
      · have hm1 : 1 ≤ m := by omega
        have hprevious := ih hm1
        have hstep := log_successor_increment_lower m hm1
        rw [Nat.succ_eq_add_one, log_factorial_succ, Nat.cast_add, Nat.cast_one]
        nlinarith
  exact hall n hn

/-- Remove the shifted factorial exactly before estimating the logarithm. -/
theorem log_factorial_pred (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n - 1).factorial : ℝ) =
      Real.log (n.factorial : ℝ) - Real.log (n : ℝ) := by
  have hnrec : n - 1 + 1 = n := by omega
  have h := log_factorial_succ (n - 1)
  rw [hnrec] at h
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hnrec
  rw [hcast] at h
  linarith

end ZetaNine.AnalyticFactorialBounds

#print axioms ZetaNine.AnalyticFactorialBounds.real_factorial_pos
#print axioms ZetaNine.AnalyticFactorialBounds.log_factorial_succ
#print axioms ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper
#print axioms ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower
#print axioms ZetaNine.AnalyticFactorialBounds.log_factorial_lower
#print axioms ZetaNine.AnalyticFactorialBounds.log_factorial_upper
#print axioms ZetaNine.AnalyticFactorialBounds.log_factorial_pred
