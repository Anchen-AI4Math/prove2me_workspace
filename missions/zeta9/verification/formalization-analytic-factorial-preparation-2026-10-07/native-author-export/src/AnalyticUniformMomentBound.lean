import AnalyticMomentBounds

/-!
UNCOMPILED SOURCE preparation. This connects the actual compact sum and
infinite factorial-tail bound to a coefficient-independent five-moment
exponential bound. Every estimate is proved from n >= 1 and r <= 4.
Changing-coefficient polynomial evaluation and uniform-o(1) endpoints remain
to be added before the full weighted Z9.A statement can be claimed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators

namespace ZetaNine.AnalyticUniformMomentBound
open AnalyticMomentBounds

def tailWeightConstant (r : ℕ) : ℝ :=
  (9 / 7 : ℝ) * (3 / 2 : ℝ) ^ r / (2 : ℝ) ^ (9 - 2 * r)

def tailMajorant (n r : ℕ) : ℝ :=
  tailCoefficient n r / (2 * (n : ℝ)) ^ tailPower n r * (9 / 7 : ℝ) /
    (n : ℝ) ^ (2 * r)

def tailExponent : ℝ := 7 + 6 * Real.log 2

def momentBoundConstant : ℝ := 5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7

theorem tailWeightConstant_pos (r : ℕ) : 0 < tailWeightConstant r := by
  unfold tailWeightConstant
  positivity

theorem tailWeightConstant_le (r : ℕ) (hr : r ≤ 4) :
    tailWeightConstant r ≤ (729 / 224 : ℝ) := by
  unfold tailWeightConstant
  interval_cases r <;> norm_num

theorem tailMajorant_pos (n r : ℕ) (hn : 1 ≤ n) : 0 < tailMajorant n r := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfact := AnalyticFactorialBounds.real_factorial_pos n
  unfold tailMajorant tailCoefficient
  positivity

theorem log_tailWeightConstant (r : ℕ) :
    Real.log (tailWeightConstant r) = Real.log (9 / 7 : ℝ) +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      ((9 - 2 * r : ℕ) : ℝ) * Real.log 2 := by
  unfold tailWeightConstant
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num : (9 / 7 : ℝ) ≠ 0) (by positivity),
    Real.log_pow, Real.log_pow]

theorem log_tailMajorant_identity (n r : ℕ) (hn : 1 ≤ n) :
    Real.log (tailMajorant n r) =
      7 * Real.log (n.factorial : ℝ) + (n : ℝ) * Real.log 2 +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      (tailPower n r : ℝ) * (Real.log 2 + Real.log (n : ℝ)) +
      Real.log (9 / 7 : ℝ) - ((2 * r : ℕ) : ℝ) * Real.log (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hfact := AnalyticFactorialBounds.real_factorial_pos n
  unfold tailMajorant tailCoefficient
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by norm_num : (9 / 7 : ℝ) ≠ 0),
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
  norm_num

theorem log_tailMajorant_upper (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Real.log (tailMajorant n r) ≤ Real.log (tailWeightConstant r) + 7 -
      tailExponent * n - 2 * Real.log (n : ℝ) := by
  have hfact := AnalyticFactorialBounds.log_factorial_upper n hn
  have hidentity := log_tailMajorant_identity n r hn
  have hconstant := log_tailWeightConstant r
  have hsdom : 2 * r ≤ 7 * n + 9 := by omega
  have hrdomain : 2 * r ≤ 9 := by omega
  have hscast : (tailPower n r : ℝ) = 7 * (n : ℝ) + 9 - 2 * (r : ℝ) := by
    unfold tailPower
    rw [Nat.cast_sub hsdom]
    push_cast
    ring
  have hrcast : ((9 - 2 * r : ℕ) : ℝ) = 9 - 2 * (r : ℝ) := by
    rw [Nat.cast_sub hrdomain]
    push_cast
    ring
  rw [hscast] at hidentity
  rw [hrcast] at hconstant
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hidentity
  unfold tailExponent
  nlinarith

theorem certified_tailExponent_gap :
    (2641 / 250 : ℝ) + (297441 / 500000 : ℝ) < tailExponent := by
  have h := AnalyticPhase.log_two_lower_rational
  unfold tailExponent
  nlinarith

theorem tailMajorant_certified_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    tailMajorant n r ≤ (729 / 224 : ℝ) * Real.exp 7 *
      Real.exp (-(2641 / 250 : ℝ) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hconstant := Real.log_le_log (tailWeightConstant_pos r) (tailWeightConstant_le r hr)
  have hgamma : (2641 / 250 : ℝ) ≤ tailExponent := by have := certified_tailExponent_gap; linarith
  have hmul := mul_le_mul_of_nonneg_right hgamma hn0.le
  have hlog : Real.log (tailMajorant n r) ≤
      Real.log (729 / 224 : ℝ) + 7 - (2641 / 250 : ℝ) * n := by
    have h := log_tailMajorant_upper n r hn hr
    nlinarith
  have h := (Real.log_le_iff_le_exp (tailMajorant_pos n r hn)).mp hlog
  have he : Real.exp (Real.log (729 / 224 : ℝ) + 7 - (2641 / 250 : ℝ) * n) =
      (729 / 224 : ℝ) * Real.exp 7 * Real.exp (-(2641 / 250 : ℝ) * n) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ) < 729 / 224)]
    rw [neg_mul]
  exact h.trans_eq he

theorem actual_tail_moment_sum_certified_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) ≤
      (729 / 224 : ℝ) * Real.exp 7 * Real.exp (-(2641 / 250 : ℝ) * n) *
        (n : ℝ) ^ (2 * r) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (0 : ℝ) < (n : ℝ) ^ (2 * r) := pow_pos hn0 _
  have h := div_le_div_of_nonneg_right
    (actual_tail_moment_sum_factorial_bound n r hn hr) hpow.le
  have hnormal : (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) / (n : ℝ) ^ (2 * r) ≤
      tailMajorant n r := h
  exact (div_le_iff₀ hpow).mp (hnormal.trans (tailMajorant_certified_bound n r hn hr))

theorem momentBoundConstant_pos : 0 < momentBoundConstant := by
  unfold momentBoundConstant
  positivity

/-- The actual raw five moments, including all first n zero terms. -/
theorem actualMoment_uniform_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    actualMoment n r ≤ momentBoundConstant * ((n : ℝ) + 1) ^ 10 *
      Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hpow0 : (n : ℝ) ^ 10 ≤ ((n : ℝ) + 1) ^ 10 :=
    pow_le_pow_left₀ hn0 (by linarith) _
  have hpow1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 10 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hn1 10
  have hcomp := actual_compact_moment_sum_bound n r hn hr
  have htail := actual_tail_moment_sum_certified_bound n r hn hr
  have hsplit := actualMoment_eq_compact_add_tail n r hn hr
  have hsum : actualMoment n r ≤
      (5184 * Real.exp 18 * (n : ℝ) ^ 10 + (729 / 224 : ℝ) * Real.exp 7) *
        (Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r)) := by
    rw [hsplit]
    have h := add_le_add hcomp htail
    convert h using 1 <;> first | rfl | ring
  have hc0 : (0 : ℝ) ≤ 5184 * Real.exp 18 := by positivity
  have hc1 : (0 : ℝ) ≤ (729 / 224 : ℝ) * Real.exp 7 := by positivity
  have hcoef : 5184 * Real.exp 18 * (n : ℝ) ^ 10 + (729 / 224 : ℝ) * Real.exp 7 ≤
      momentBoundConstant * ((n : ℝ) + 1) ^ 10 := by
    have h0 := mul_le_mul_of_nonneg_left hpow0 hc0
    have h1 := mul_le_mul_of_nonneg_left hpow1 hc1
    unfold momentBoundConstant
    nlinarith
  exact hsum.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef (by positivity))

end ZetaNine.AnalyticUniformMomentBound

#print axioms ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper
#print axioms ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap
#print axioms ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound
#print axioms ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound
#print axioms ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound
