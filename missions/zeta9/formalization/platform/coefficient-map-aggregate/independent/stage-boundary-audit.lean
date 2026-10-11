import Solutions.Sol_ZetaNine_CoefficientMapAggregate_aggregate_zero_all_rho
import Lean
import Mathlib.Tactic

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapInjectivity

open scoped BigOperators
open Finset Polynomial

theorem baseNumerator_eval (n : ℕ) (t : ℚ) :
    (baseNumerator n).eval t = CoefficientMap.numerator n t := by
  simp only [baseNumerator, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rfl

end ZetaNine.CoefficientMapInjectivity

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapPartialFractions

open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity

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

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFiniteSum

open scoped BigOperators
open Finset Polynomial
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

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapReflection

open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity CoefficientMapPartialFractions

theorem quartic_is_strong_proper (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    StrongProperMultiplier n W := by
  unfold StrongProperMultiplier
  omega

end ZetaNine.CoefficientMapReflection

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapSummation

open scoped BigOperators Topology
open Finset Polynomial Filter
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

end ZetaNine.CoefficientMapSummation

open Lean Meta Polynomial Finset
open scoped BigOperators
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false
set_option maxHeartbeats 2200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem checked_five_actual_coordinates (n : ℕ) (W : ℚ[X]) :
    aggregate n W 0 = ZetaNine.CoefficientMapFiniteSum.constantTerm n W ∧
    aggregate n W 1 = ZetaNine.CoefficientMapFiniteSum.rho n 3 W ∧
    aggregate n W 2 = ZetaNine.CoefficientMapFiniteSum.rho n 5 W ∧
    aggregate n W 3 = ZetaNine.CoefficientMapFiniteSum.rho n 7 W ∧
    aggregate n W 4 = ZetaNine.CoefficientMapFiniteSum.rho n 9 W :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem checked_actual_monomial_basis (i : Fin 5) :
    coordinatePolynomial (Pi.single i (1 : ℚ)) = X ^ i.val := by
  classical
  unfold coordinatePolynomial
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem checked_basis_columns (n : ℕ) (i : Fin 5) :
    quarticAggregateLinearMap n (Pi.single i (1 : ℚ)) = aggregate n (X ^ i.val) := by
  rw [quartic_aggregate_is_actual, checked_actual_monomial_basis]

theorem checked_n_zero_X_four_aggregate_kernel :
    aggregate 0 (X ^ 4 : ℚ[X]) = 0 ∧ (X ^ 4 : ℚ[X]) ≠ 0 ∧
    ZetaNine.CoefficientMapInjectivity.ProperMultiplier 0 (X ^ 4 : ℚ[X]) ∧
    ¬ StrongProperMultiplier 0 (X ^ 4 : ℚ[X]) ∧
    ZetaNine.CoefficientMapReflection.rho 0 1 (X ^ 4 : ℚ[X]) = 1 := by
  have hkernel : aggregate 0 (X ^ 4 : ℚ[X]) = 0 := by
    funext i
    fin_cases i <;> norm_num [aggregate, ZetaNine.CoefficientMapFiniteSum.constantTerm,
      ZetaNine.CoefficientMapFiniteSum.rho, ZetaNine.HarmonicStability.harmonicPower,
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
      ZetaNine.CoefficientMapJet.weightedClearedSeries, ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator, ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
      ZetaNine.CoefficientMapJet.localU, ZetaNine.CoefficientMapJet.shiftedVariable,
      Polynomial.pow_comp, Polynomial.X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X, ← pow_two, ← pow_mul]
  refine ⟨hkernel, pow_ne_zero 4 X_ne_zero, ?_, ?_, ?_⟩
  · norm_num [ZetaNine.CoefficientMapInjectivity.ProperMultiplier]
  · norm_num [StrongProperMultiplier]
  · norm_num [ZetaNine.CoefficientMapReflection.rho, ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
      ZetaNine.CoefficientMapJet.weightedClearedSeries, ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator, ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
      ZetaNine.CoefficientMapJet.localU, ZetaNine.CoefficientMapJet.shiftedVariable,
      Polynomial.pow_comp, Polynomial.X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X, ← pow_two, ← pow_mul]

theorem checked_original_quartic_zero_all_orders (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : aggregate n W = 0) :
    ∀ s, 1 ≤ s → s ≤ 9 →
      (∑ j ∈ range (n + 1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) = 0 := by
  intro s hs1 hs9
  exact checked_aggregate_zero_all_rho n hn W (quartic_is_strong_proper n (by omega) W hW) hzero s hs1 hs9

theorem checked_original_quartic_zero_exact_sum (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : aggregate n W = 0) :
    HasSum (fun t : ℕ => (ZetaNine.CoefficientMap.weightedR n W ((t + 1 : ℕ) : ℚ) : ℝ)) 0 := by
  have h := ZetaNine.CoefficientMapSummation.actualSeries_hasSum_exactL n hn W
    (quartic_is_strong_proper n (by omega) W hW)
  rw [aggregate_zero_exactL n W hzero] at h
  exact h

theorem agg_ind_actual_B_negative_harmonic (n : ℕ) (W : ℚ[X]) :
    aggregate n W 0 = -(∑ j ∈ range (n+1), ∑ s ∈ Icc 1 9,
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W *
        ZetaNine.HarmonicStability.harmonicPower s j) := rfl

theorem agg_ind_actual_five_odd_coordinates (n : ℕ) (W : ℚ[X]) :
    aggregate n W 1 = (∑ j ∈ range (n+1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 3 W) ∧
    aggregate n W 2 = (∑ j ∈ range (n+1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 5 W) ∧
    aggregate n W 3 = (∑ j ∈ range (n+1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 7 W) ∧
    aggregate n W 4 = (∑ j ∈ range (n+1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j 9 W) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem agg_ind_general_rational_linearity (n : ℕ) (a b : ℚ) (W V : ℚ[X]) :
    aggregate n (a • W + b • V) = a • aggregate n W + b • aggregate n V := by
  rw [aggregate_add, aggregate_smul, aggregate_smul]

theorem agg_ind_zero_all_n (n : ℕ) : aggregate n (0 : ℚ[X]) = 0 :=
  (aggregateLinearMap n).map_zero

theorem agg_ind_coordinate_zero : coordinatePolynomial (0 : Fin 5 → ℚ) = 0 :=
  coordinateLinearMap.map_zero

theorem agg_ind_roundtrip_zero : coordinatePolynomial (polynomialCoordinates (0 : ℚ[X])) = 0 :=
  polynomial_restore 0 (by simp)

theorem agg_ind_roundtrip_nonmonic :
    coordinatePolynomial (polynomialCoordinates (C (3 : ℚ) * X ^ 4 + C 7)) = C 3 * X ^ 4 + C 7 := by
  apply polynomial_restore
  exact (natDegree_add_le _ _).trans (by simp)

theorem agg_ind_basis (i : Fin 5) : coordinatePolynomial (Pi.single i (1 : ℚ)) = X ^ i.val := by
  classical
  unfold coordinatePolynomial
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem agg_ind_quartic_restoration_kernel (n : ℕ) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    aggregate n W = 0 ↔ quarticAggregateLinearMap n (polynomialCoordinates W) = 0 := by
  rw [quartic_aggregate_is_actual, polynomial_restore W hW]

theorem agg_ind_hasSum_zero_strong_even (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hf : aggregate n W = 0) :
    HasSum (fun k : ℕ => (ZetaNine.CoefficientMap.weightedR n W ((k+1 : ℕ) : ℚ) : ℝ)) 0 := by
  have h := actualSeries_hasSum_exactL n hn W hstrong
  rw [aggregate_zero_exactL n W hf] at h
  exact h

theorem agg_ind_all_rho_zero_strong_even (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hf : aggregate n W = 0) :
    ∀ s, 1 ≤ s → s ≤ 9 →
      (∑ j ∈ range (n+1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) = 0 := by
  intro s hs1 hs9
  exact checked_aggregate_zero_all_rho n hn W hstrong hf s hs1 hs9

theorem agg_ind_n_zero_series (W : ℚ[X]) :
    ZetaNine.CoefficientMapJet.weightedClearedSeries 0 0 W =
      (W.comp ((X : ℚ[X]) ^ 2) : PowerSeries ℚ) := by
  have hb : ZetaNine.CoefficientMapJet.clearedSeries 0 0 = 1 := by
    simp [ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator,
      ZetaNine.CoefficientMapJet.shiftedClearedDenominator]
  have hu : ZetaNine.CoefficientMapJet.localU 0 0 = (X : ℚ[X]) ^ 2 := by
    simp [ZetaNine.CoefficientMapJet.localU,ZetaNine.CoefficientMapJet.shiftedVariable,pow_two]
  simp only [ZetaNine.CoefficientMapJet.weightedClearedSeries,hb,hu,one_mul]

theorem agg_ind_n_zero_harmonic_constant (W : ℚ[X]) : aggregate 0 W 0 = 0 := by
  simp [aggregate,ZetaNine.CoefficientMapFiniteSum.constantTerm,ZetaNine.HarmonicStability.harmonicPower]

theorem agg_ind_n_zero_X_four_odd_rho (s : ℕ) (hs2 : 2 ≤ s) (hs9 : s ≤ 9) :
    ZetaNine.CoefficientMapFiniteSum.rho 0 s ((X : ℚ[X]) ^ 4) = 0 := by
  have hindex : 9-s ≠ 8 := by omega
  unfold ZetaNine.CoefficientMapFiniteSum.rho
  rw [Finset.sum_range_one,ZetaNine.CoefficientMapJet.weightedLocalCoefficient,agg_ind_n_zero_series]
  simp only [Polynomial.pow_comp,Polynomial.X_comp,map_pow,Polynomial.coe_X]
  rw [← pow_mul]
  norm_num [PowerSeries.coeff_X_pow,hindex,Ne.symm hindex]

theorem agg_ind_n_zero_X_four_F_zero : aggregate 0 ((X : ℚ[X]) ^ 4) = 0 := by
  funext i
  fin_cases i
  · exact agg_ind_n_zero_harmonic_constant _
  all_goals exact agg_ind_n_zero_X_four_odd_rho _ (by omega) (by omega)

theorem agg_ind_n_zero_X_four_rho1 : ZetaNine.CoefficientMapFiniteSum.rho 0 1 ((X : ℚ[X]) ^ 4) = 1 := by
  unfold ZetaNine.CoefficientMapFiniteSum.rho
  rw [Finset.sum_range_one,ZetaNine.CoefficientMapJet.weightedLocalCoefficient,agg_ind_n_zero_series]
  simp only [Polynomial.pow_comp,Polynomial.X_comp,map_pow,Polynomial.coe_X]
  rw [← pow_mul]
  norm_num

theorem agg_ind_n_zero_X_four_proper_not_strong :
    ProperMultiplier 0 ((X : ℚ[X]) ^ 4) ∧ ¬ StrongProperMultiplier 0 ((X : ℚ[X]) ^ 4) := by
  norm_num [ProperMultiplier,StrongProperMultiplier,Polynomial.natDegree_pow]

theorem agg_ind_n_zero_actual_F_not_injective : ¬ Function.Injective (aggregate 0) := by
  intro h
  have hz : (X : ℚ[X]) ^ 4 = 0 := h (agg_ind_n_zero_X_four_F_zero.trans (agg_ind_zero_all_n 0).symm)
  exact pow_ne_zero 4 X_ne_zero hz

theorem agg_ind_n_zero_quartic_F_nonzero_kernel :
    quarticAggregateLinearMap 0 (Pi.single (4 : Fin 5) (1 : ℚ)) = 0 ∧
      (Pi.single (4 : Fin 5) (1 : ℚ) : Fin 5 → ℚ) ≠ 0 := by
  constructor
  · rw [quartic_aggregate_is_actual,agg_ind_basis]
    exact agg_ind_n_zero_X_four_F_zero
  · intro h
    have hh := congrFun h (4 : Fin 5)
    norm_num at hh

theorem agg_ind_n_zero_X_three_output : aggregate 0 ((X : ℚ[X]) ^ 3) = Pi.single (1 : Fin 5) (1 : ℚ) := by
  funext i
  fin_cases i <;>
    norm_num [aggregate,ZetaNine.CoefficientMapFiniteSum.constantTerm,ZetaNine.HarmonicStability.harmonicPower,
      ZetaNine.CoefficientMapFiniteSum.rho,ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
      agg_ind_n_zero_series,Polynomial.pow_comp,Polynomial.X_comp,Polynomial.coe_pow,Polynomial.coe_X,
      ← pow_mul] <;> simp

theorem agg_ind_n_zero_X_four_actual_sequence (k : ℕ) :
    actualSeries 0 ((X : ℚ[X]) ^ 4) k = 1 / ((k : ℝ)+1) := by
  have ht : ((k+1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hQ : ZetaNine.CoefficientMap.weightedR 0 ((X : ℚ[X]) ^ 4) ((k+1 : ℕ) : ℚ) =
      1 / ((k+1 : ℕ) : ℚ) := by
    simp [ZetaNine.CoefficientMap.weightedR,ZetaNine.CoefficientMap.actualR,
      ZetaNine.CoefficientMap.numerator,ZetaNine.CoefficientMap.poleProduct]
    field_simp
  unfold actualSeries
  rw [hQ]
  push_cast
  rfl

theorem agg_ind_n_zero_F_zero_does_not_give_HasSum (L : ℝ) :
    aggregate 0 ((X : ℚ[X]) ^ 4) = 0 ∧ ¬ HasSum (actualSeries 0 ((X : ℚ[X]) ^ 4)) L := by
  refine ⟨agg_ind_n_zero_X_four_F_zero,?_⟩
  intro h
  have hshift : Summable (fun k : ℕ => 1 / ((k+1 : ℕ) : ℝ)) :=
    h.summable.congr (fun k => by simpa only [Nat.cast_add,Nat.cast_one] using agg_ind_n_zero_X_four_actual_sequence k)
  have hall : Summable (fun k : ℕ => 1 / (k : ℝ)) :=
    (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ)) 1).mp hshift
  exact Real.not_summable_one_div_natCast hall

run_meta do
  let emit (kind : String) (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let val ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str name.toString),
      ("type",Json.str typ.pretty),("axioms",toJson (axs.toList.map Name.toString)),
      ("definitionValue",val)]).compress
  for name in [`ZetaNine.CoefficientMapAggregate.coordinatePolynomial, `ZetaNine.CoefficientMapAggregate.actual_constant_smul, `ZetaNine.CoefficientMapAggregate.coordinates_restore, `ZetaNine.CoefficientMapAggregate.actual_rho_smul, `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_injective, `ZetaNine.CoefficientMapAggregate.polynomialCoordinates, `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_add, `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_smul, `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_coeff, `ZetaNine.CoefficientMapAggregate.aggregate, `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_coeff_above, `ZetaNine.CoefficientMapAggregate.aggregateLinearMap, `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_natDegree_le, `ZetaNine.CoefficientMapAggregate.polynomial_restore, `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap, `ZetaNine.CoefficientMapAggregate.quartic_aggregate_is_actual, `ZetaNine.CoefficientMapAggregate.actual_rho_add, `ZetaNine.CoefficientMapAggregate.checked_aggregate_zero_all_rho, `ZetaNine.CoefficientMapAggregate.aggregate_zero_exactL, `ZetaNine.CoefficientMapAggregate.actual_constant_add, `ZetaNine.CoefficientMapAggregate.aggregate_smul, `ZetaNine.CoefficientMapAggregate.aggregate_zero_iff, `ZetaNine.CoefficientMapAggregate.actual_local_coefficient_smul, `ZetaNine.CoefficientMapAggregate.actual_local_coefficient_add, `ZetaNine.CoefficientMapAggregate.aggregate_add, `ZetaNine.CoefficientMapAggregate.coordinateLinearMap, `checked_five_actual_coordinates, `checked_actual_monomial_basis, `checked_basis_columns, `checked_n_zero_X_four_aggregate_kernel, `checked_original_quartic_zero_all_orders, `checked_original_quartic_zero_exact_sum, `agg_ind_actual_B_negative_harmonic, `agg_ind_actual_five_odd_coordinates, `agg_ind_general_rational_linearity, `agg_ind_zero_all_n, `agg_ind_coordinate_zero, `agg_ind_roundtrip_zero, `agg_ind_roundtrip_nonmonic, `agg_ind_basis, `agg_ind_quartic_restoration_kernel, `agg_ind_hasSum_zero_strong_even, `agg_ind_all_rho_zero_strong_even, `agg_ind_n_zero_series, `agg_ind_n_zero_harmonic_constant, `agg_ind_n_zero_X_four_odd_rho, `agg_ind_n_zero_X_four_F_zero, `agg_ind_n_zero_X_four_rho1, `agg_ind_n_zero_X_four_proper_not_strong, `agg_ind_n_zero_actual_F_not_injective, `agg_ind_n_zero_quartic_F_nonzero_kernel, `agg_ind_n_zero_X_three_output, `agg_ind_n_zero_X_four_actual_sequence, `agg_ind_n_zero_F_zero_does_not_give_HasSum] do emit "native_exact_boundary" name
  for name in [`ZetaNine.CoefficientMapInjectivity.baseNumerator_eval, `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval, `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero, `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor, `ZetaNine.CoefficientMapPartialFractions.actual_weighted_rational_representation, `ZetaNine.CoefficientMapPartialFractions.partial_term_division, `ZetaNine.CoefficientMapPartialFractions.actual_global_partial_fractions, `ZetaNine.CoefficientMapFiniteSum.harmonicPower_succ, `ZetaNine.CoefficientMapFiniteSum.shifted_harmonic_sum, `ZetaNine.CoefficientMapFiniteSum.actual_finite_harmonic_identity, `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity, `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_no_simple_pole, `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_odd, `ZetaNine.CoefficientMapFiniteSum.harmonic_difference_eq_shifted, `ZetaNine.CoefficientMapReflection.quartic_is_strong_proper, `ZetaNine.CoefficientMapSummation.actual_finite_odd_identity, `ZetaNine.CoefficientMapSummation.sum_Icc_eq_sum_range_successor, `ZetaNine.CoefficientMapSummation.harmonicPower_cast, `ZetaNine.CoefficientMapSummation.harmonicPower_cast_eq_range, `ZetaNine.CoefficientMapSummation.zetaReal_eq_tsum, `ZetaNine.CoefficientMapSummation.harmonicPower_tendsto_zeta, `ZetaNine.CoefficientMapSummation.shifted_reciprocal_tendsto_zero, `ZetaNine.CoefficientMapSummation.harmonic_fixed_tail_tendsto_zero, `ZetaNine.CoefficientMapSummation.actual_shiftedTail_tendsto_zero, `ZetaNine.CoefficientMapSummation.actual_finiteL_tendsto_exactL, `ZetaNine.CoefficientMapSummation.simple_pole_difference_identity, `ZetaNine.CoefficientMapSummation.simple_pole_difference_summable, `ZetaNine.CoefficientMapSummation.shifted_high_order_summable, `ZetaNine.CoefficientMapSummation.actualSeries_eq_principal_parts, `ZetaNine.CoefficientMapSummation.actualSeries_eq_cancelled_principal_parts, `ZetaNine.CoefficientMapSummation.actualSeries_summable, `ZetaNine.CoefficientMapSummation.actualSeries_partial_sums, `ZetaNine.CoefficientMapSummation.actualSeries_hasSum_exactL] do emit "boundary_only_genuine_helper" name
