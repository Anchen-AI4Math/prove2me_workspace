import Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_bound
import Theorems.Thm_TaoFivePrimes_mertens_tail_le_partial_sum
import Mathlib

/-!
# Reduction of the logarithmic Mertens product bound to Mawia (2017)

Target (Rosser--Schoenfeld 1962, (3.29) in logarithmic form):

    for every real x >= 10^8,
      sum_{p <= floor x} log (p/(p-1)) < gamma + log log x + log (1 + 1/(2 log^2 x)).

The reduction splits the summand with the identity, valid for every prime `p`,

    log (p/(p-1)) = 1/p - (log (1 - 1/p) + 1/p),

which is the termwise form of `log prod p/(p-1) = sum 1/p - sum (log(1-1/p) + 1/p)`.
Summing over `Nat.primesLE ⌊x⌋₊` and writing `T` for the series over all primes,
`S1` for `sum_{p <= x} 1/p` and `P` for the finite sum of the correction, leaves

    S1 - P  =  (S1 - log log x - (gamma + T))  +  log log x + gamma  +  (T - P).

The three pieces are bounded separately:

* `|S1 - log log x - (gamma + T)| <= 4 / log^3 x` is
  `TaoFivePrimes.mawia_reciprocal_sum_bound` (R. Mawia, *Explicit Mertens sums*,
  2017, zbMATH 1412.11125) — a quoted published estimate, valid for all `x >= 2`;
* `T - P <= 0` is `TaoFivePrimes.mertens_tail_le_partial_sum`, which is **Proved**;
* `4 / log^3 x < log (1 + 1/(2 log^2 x))` is elementary. With `u = log x > 16`,

      log (1 + 1/(2u^2)) >= (1/(2u^2)) / (1 + 1/(2u^2)) = 1/(2u^2 + 1) > 4/u^3,

  the first step from `Real.log_le_sub_one_of_pos` applied to `(1+z)⁻¹` together
  with `Real.log_inv`, the second because `u^2 (u - 8) > 4` as soon as `u > 16`.

So exactly **one** open input is used, the Mawia citation; the Mertens tail is
proved. The file has no `sorry`, no `axiom`, and imports only those two platform
nodes plus Mathlib.
-/

/-- `log (1 + z) >= z / (1 + z)` for `z > 0`, from `Real.log_le_sub_one_of_pos`
applied to `(1+z)⁻¹` and `Real.log_inv`. -/
theorem log_one_add_ge_div (z : ℝ) (hz : 0 < z) :
    Real.log (1 + z) ≥ z / (1 + z) := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : Real.log (1 + z)⁻¹ ≤ (1 + z)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [Real.log_inv] at h2
  have h3 : (1 + z)⁻¹ - 1 = -(z / (1 + z)) := by
    field_simp
  rw [h3] at h2
  linarith

/-- `exp 1 < 3`, from Mathlib's tabulated `Real.exp_one_lt_d9`. -/
theorem exp_one_lt_three : Real.exp 1 < 3 :=
  lt_trans Real.exp_one_lt_d9 (by norm_num)

/-- `exp 16 < 10^8`, by four squarings from `exp 1 < 3`. -/
theorem exp_sixteen_lt_hundred_million : Real.exp 16 < 100000000 := by
  have e2 : Real.exp 2 < 10 := by
    have h := mul_lt_mul exp_one_lt_three exp_one_lt_three
      (Real.exp_pos 1).le (Real.exp_pos 1).le
    nlinarith
  have e4 : Real.exp 4 < 100 := by
    have h := mul_lt_mul e2 e2 (Real.exp_pos 2).le (by norm_num : (0 : ℝ) < 10)
    nlinarith
  have e8 : Real.exp 8 < 10000 := by
    have h := mul_lt_mul e4 e4 (Real.exp_pos 4).le (by norm_num : (0 : ℝ) < 100)
    nlinarith
  have h := mul_lt_mul e8 e8 (Real.exp_pos 8).le (by norm_num : (0 : ℝ) < 10000)
  nlinarith

theorem solution (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) <
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  -- Step 0.  `log x > 16`, from `exp 16 < 10^8 <= x`.
  have hx0 : (0 : ℝ) < x := by positivity
  have hu : 16 < Real.log x := by
    rw [← Real.exp_log hx0, ← Real.exp_lt_exp]
    exact lt_trans exp_sixteen_lt_hundred_million hx
  have hu0 : (0 : ℝ) < Real.log x := lt_trans (by norm_num) hu
  -- Step 1.  The elementwise splitting identity.
  have hid : ∀ p ∈ Nat.primesLE ⌊x⌋₊,
      Real.log ((p : ℝ) / ((p : ℝ) - 1)) =
        1 / (p : ℝ) - (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
    intro p hp
    have hp' : p.Prime := by
      rw [Nat.primesLE_eq_filter_range] at hp
      exact (Finset.mem_filter.mp hp).2
    have hp2 : 2 ≤ p := hp'.two_le
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hsub : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hlog₁ : Real.log ((p : ℝ) / ((p : ℝ) - 1)) =
        Real.log (p : ℝ) - Real.log ((p : ℝ) - 1) :=
      Real.log_div (ne_of_gt hp0) (ne_of_gt hsub)
    have hlog₂ : Real.log (1 - 1 / (p : ℝ)) =
        Real.log ((p : ℝ) - 1) - Real.log (p : ℝ) := by
      have heq : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
      rw [heq, Real.log_div (ne_of_gt hsub) (ne_of_gt hp0)]
    rw [hlog₁, hlog₂]
    ring
  have hsum₁ : (∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)))
      = (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ))
        - ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
    rw [Finset.sum_congr rfl hid, Finset.sum_sub_distrib]
  -- Step 2.  The analytic input and the proved tail.
  have h2x : 2 ≤ x := le_trans (by norm_num) hx
  have hMawia := TaoFivePrimes.mawia_reciprocal_sum_bound x h2x
  have hTail := TaoFivePrimes.mertens_tail_le_partial_sum x
  have hcore : (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ))
        - ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))
      ≤ Real.eulerMascheroniConstant + Real.log (Real.log x)
        + 4 / (Real.log x) ^ 3 := by
    have hM := (Real.abs_le.1 hMawia).2
    linarith
  -- Step 3.  `4 / log^3 x < log (1 + 1/(2 log^2 x))`.
  have hsq : Real.log x ^ 2 > 256 := by
    nlinarith [mul_pos (show (0 : ℝ) < Real.log x - 16 by linarith)
      (show (0 : ℝ) < Real.log x + 16 by linarith)]
  have hlin : (0 : ℝ) < Real.log x - 8 := by linarith
  have hlin8 : 8 < Real.log x - 8 := by linarith
  have hprod : 2048 < Real.log x ^ 2 * (Real.log x - 8) := by
    have h1 : (0 : ℝ) < Real.log x ^ 2 := by nlinarith [hsq]
    calc (2048 : ℝ) = 256 * 8 := by norm_num
      _ < Real.log x ^ 2 * (Real.log x - 8) := mul_lt_mul hsq hlin (by norm_num) h1
  have hkey : Real.log x ^ 3 > 4 * (2 * Real.log x ^ 2 + 1) := by
    have h : Real.log x ^ 2 * (Real.log x - 8) > 4 :=
      lt_trans (by norm_num) hprod
    nlinarith [h]
  have hfrac : (4 : ℝ) / Real.log x ^ 3 < 1 / (2 * Real.log x ^ 2 + 1) := by
    have hden : (0 : ℝ) < 2 * Real.log x ^ 2 + 1 := by positivity
    rw [lt_div_iff₀ hden, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    linarith [hkey]
  have hstep : (4 : ℝ) / Real.log x ^ 3
      ≤ Real.log (1 + 1 / (2 * Real.log x ^ 2)) := by
    refine le_trans hfrac (le_of_eq ?_)
    have hz : (0 : ℝ) < 1 / (2 * Real.log x ^ 2) := by positivity
    have h := log_one_add_ge_div (1 / (2 * Real.log x ^ 2)) hz
    convert h using 1 <;> field_simp
  -- Step 4.  Assemble.
  rw [hsum₁]
  linarith [hcore, hstep]
