import AnalyticRationalFactorial
import AnalyticPhaseUpperBound

/-!
UNCOMPILED SOURCE preparation. Private compilation must use the already
verified native-export AnalyticPhase / AnalyticPhaseUpperBound dependencies,
not the unchanged historical shared preparations with the same module names.

This is a pointwise bound for the actual product-defined rational function.
The full infinite moment estimate still requires a quantitative p-series tail
bound and the finite compact/tail summation argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace ZetaNine.AnalyticRationalLogBound

theorem scaled_phase_identity (n k : ℝ) (hn : 0 < n) (hk : n < k) :
    7 * n * Real.log n + 10 * k * Real.log k +
      (k + 2 * n) * Real.log (k + 2 * n) -
      (k - n) * Real.log (k - n) -
      10 * (k + n) * Real.log (k + n) =
      n * AnalyticPhase.phase (k / n) := by
  have hk0 : 0 < k := lt_trans hn hk
  have hkm : 0 < k - n := sub_pos.mpr hk
  have hkp : 0 < k + n := by positivity
  have hk2 : 0 < k + 2 * n := by positivity
  have he2 : k / n + 2 = (k + 2 * n) / n := by
    field_simp [hn.ne']
  have hem : k / n - 1 = (k - n) / n := by
    field_simp [hn.ne']
  have hep : k / n + 1 = (k + n) / n := by
    field_simp [hn.ne']
  unfold AnalyticPhase.phase
  rw [he2, hem, hep, Real.log_div hk0.ne' hn.ne',
    Real.log_div hk2.ne' hn.ne', Real.log_div hkm.ne' hn.ne',
    Real.log_div hkp.ne' hn.ne']
  field_simp [hn.ne']
  ring

/-- The exact residual log terms and constant are 7 log n, log(k+2n),
log(k-n), and 18. The factorial shifts have already been eliminated exactly. -/
theorem actualR_log_le_phase (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n : ℝ) * AnalyticPhase.phase ((k : ℝ) / (n : ℝ)) +
        7 * Real.log (n : ℝ) + Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : (n : ℝ) < k := by exact_mod_cast hk
  have hnupper := AnalyticFactorialBounds.log_factorial_upper n hn
  have hkupper := AnalyticFactorialBounds.log_factorial_upper k (by omega)
  have hk2upper := AnalyticFactorialBounds.log_factorial_upper (k + 2 * n) (by omega)
  have hkmnlower := AnalyticFactorialBounds.log_factorial_lower (k - n)
  have hkplower := AnalyticFactorialBounds.log_factorial_lower (k + n)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (Nat.le_of_lt hk)] at hk2upper hkmnlower hkplower
  rw [AnalyticRationalFactorial.actualR_log_factorial n k hk]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (Nat.le_of_lt hk)]
  have hphase := scaled_phase_identity (n : ℝ) (k : ℝ) hn0 hkn
  nlinarith

theorem actualR_log_le_certified (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      -(2641 / 250 : ℝ) * n + 7 * Real.log (n : ℝ) +
        Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : (n : ℝ) < k := by exact_mod_cast hk
  have hratio : 1 < (k : ℝ) / (n : ℝ) := (one_lt_div hn0).mpr hkn
  have hphase := AnalyticPhase.phase_global_upper_bound _ hratio
  have hmul := mul_le_mul_of_nonneg_left hphase hn0.le
  have h := actualR_log_le_phase n k hn hk
  nlinarith

/-- Exponentiating the genuine log bound gives an explicit polynomial factor. -/
theorem actualR_le_certified (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      Real.exp 18 * (n : ℝ) ^ 7 * ((k : ℝ) + 2 * (n : ℝ)) *
        ((k : ℝ) - (n : ℝ)) * Real.exp (-(2641 / 250 : ℝ) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : (n : ℝ) < k := by exact_mod_cast hk
  have hkm : (0 : ℝ) < (k : ℝ) - (n : ℝ) := sub_pos.mpr hkn
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 * (n : ℝ) := by linarith
  have hR := AnalyticRationalFactorial.actualR_real_pos n k hk
  have h := (Real.log_le_iff_le_exp hR).mp (actualR_log_le_certified n k hn hk)
  have he :
      Real.exp (-(2641 / 250 : ℝ) * n + 7 * Real.log (n : ℝ) +
        Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18) =
      Real.exp 18 * (n : ℝ) ^ 7 * ((k : ℝ) + 2 * (n : ℝ)) *
        ((k : ℝ) - (n : ℝ)) * Real.exp (-(2641 / 250 : ℝ) * n) := by
    rw [show 7 * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ 7) by
      simpa only [Nat.cast_ofNat] using (Real.log_pow (n : ℝ) 7).symm]
    simp only [Real.exp_add, Real.exp_log (pow_pos hn0 7),
      Real.exp_log hk2, Real.exp_log hkm]
    ring
  exact h.trans_eq he

theorem actualR_compact_bound (n k : ℕ) (hn : 1 ≤ n)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      4 * Real.exp 18 * (n : ℝ) ^ 9 * Real.exp (-(2641 / 250 : ℝ) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : (n : ℝ) < k := by exact_mod_cast hk
  have hk2r : (k : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hk2
  have hprod : ((k : ℝ) + 2 * (n : ℝ)) * ((k : ℝ) - (n : ℝ)) ≤
      4 * (n : ℝ) ^ 2 := by
    have hleft : (k : ℝ) + 2 * (n : ℝ) ≤ 4 * (n : ℝ) := by linarith
    have hright : (k : ℝ) - (n : ℝ) ≤ (n : ℝ) := by linarith
    have h := mul_le_mul hleft hright (by linarith : (0 : ℝ) ≤ (k : ℝ) - n)
      (by positivity : (0 : ℝ) ≤ 4 * (n : ℝ))
    nlinarith
  calc
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
        Real.exp 18 * (n : ℝ) ^ 7 *
          (((k : ℝ) + 2 * (n : ℝ)) * ((k : ℝ) - (n : ℝ))) *
          Real.exp (-(2641 / 250 : ℝ) * n) := by
      simpa only [mul_assoc] using actualR_le_certified n k hn hk
    _ ≤ Real.exp 18 * (n : ℝ) ^ 7 * (4 * (n : ℝ) ^ 2) *
          Real.exp (-(2641 / 250 : ℝ) * n) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod (by positivity)) (Real.exp_pos _).le
    _ = _ := by ring

end ZetaNine.AnalyticRationalLogBound

#print axioms ZetaNine.AnalyticRationalLogBound.scaled_phase_identity
#print axioms ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase
#print axioms ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified
#print axioms ZetaNine.AnalyticRationalLogBound.actualR_le_certified
#print axioms ZetaNine.AnalyticRationalLogBound.actualR_compact_bound
