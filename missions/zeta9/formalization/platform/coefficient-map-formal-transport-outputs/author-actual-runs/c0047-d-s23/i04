import Oracle.CoefficientMapReflection
import Oracle.CoefficientMapFiniteSum
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

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

namespace OutputsPlatformOracle.CoefficientMapSummation

open HarmonicStability CoefficientMapInjectivity CoefficientMapReflection

def zetaReal (s : ℕ) : ℝ := (riemannZeta (s : ℂ)).re

def exactL (n : ℕ) (W : ℚ[X]) : ℝ :=
  (CoefficientMapFiniteSum.constantTerm n W : ℝ) +
    ((CoefficientMapFiniteSum.rho n 3 W : ℝ) * zetaReal 3 +
     (CoefficientMapFiniteSum.rho n 5 W : ℝ) * zetaReal 5 +
     (CoefficientMapFiniteSum.rho n 7 W : ℝ) * zetaReal 7 +
     (CoefficientMapFiniteSum.rho n 9 W : ℝ) * zetaReal 9)

def actualSeries (n : ℕ) (W : ℚ[X]) (t : ℕ) : ℝ :=
  (CoefficientMap.weightedR n W ((t + 1 : ℕ) : ℚ) : ℝ)

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

end OutputsPlatformOracle.CoefficientMapSummation

#print axioms OutputsPlatformOracle.CoefficientMapSummation.actual_finite_odd_identity
#print axioms OutputsPlatformOracle.CoefficientMapSummation.zetaReal_eq_tsum
#print axioms OutputsPlatformOracle.CoefficientMapSummation.harmonicPower_tendsto_zeta
#print axioms OutputsPlatformOracle.CoefficientMapSummation.actual_shiftedTail_tendsto_zero
#print axioms OutputsPlatformOracle.CoefficientMapSummation.actual_finiteL_tendsto_exactL
#print axioms OutputsPlatformOracle.CoefficientMapSummation.simple_pole_difference_summable
#print axioms OutputsPlatformOracle.CoefficientMapSummation.actualSeries_eq_cancelled_principal_parts
#print axioms OutputsPlatformOracle.CoefficientMapSummation.actualSeries_summable
#print axioms OutputsPlatformOracle.CoefficientMapSummation.actualSeries_norm_summable
#print axioms OutputsPlatformOracle.CoefficientMapSummation.actualSeries_hasSum_exactL
#print axioms OutputsPlatformOracle.CoefficientMapSummation.actualSeries_tsum_exactL
#print axioms OutputsPlatformOracle.CoefficientMapSummation.original_integer_quartic_exact_infinite_L
