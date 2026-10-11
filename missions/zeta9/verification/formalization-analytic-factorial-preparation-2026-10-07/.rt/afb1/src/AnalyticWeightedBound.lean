import AnalyticUniformMomentBound
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
UNCOMPILED SOURCE preparation for the actual weighted Z9.A upper bound.
The raw series is definitionally the original rational weightedR at m+1.
No coefficient growth, parity, HasSum, moment bound, or uniform error bound
is an input hypothesis. The only domains are n >= 1 and natDegree W <= 4.

This SOURCE includes the actual arbitrary-quartic triangle bound and an
explicit coefficient-independent error tending to zero. It becomes a
formalized result only after actual author and independent kernel checks.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section
open scoped BigOperators Topology
open Finset Filter Polynomial

namespace ZetaNine.AnalyticWeightedBound
open AnalyticMomentBounds AnalyticUniformMomentBound

def actualWeightedSequence (n : ℕ) (W : ℚ[X]) (m : ℕ) : ℝ :=
  (CoefficientMap.weightedR n W ((m + 1 : ℕ) : ℚ) : ℝ)

def weightedCoefficientHeight (n : ℕ) (W : ℚ[X]) : ℝ :=
  ∑ r ∈ range 5, |(W.coeff r : ℝ)| * (n : ℝ) ^ (2 * r)

def analyticPrefactor (n : ℕ) : ℝ :=
  momentBoundConstant * ((n : ℝ) + 1) ^ 10 * Real.exp (-(2641 / 250 : ℝ) * n)

def uniformError (n : ℕ) : ℝ :=
  (Real.log momentBoundConstant + 10 * Real.log ((n : ℝ) + 1)) / (n : ℝ)

theorem actualWeightedSequence_eq_actual_moment_sum (n : ℕ) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) (m : ℕ) :
    actualWeightedSequence n W m =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * actualMomentSequence n r m := by
  unfold actualWeightedSequence CoefficientMap.weightedR
  rw [Polynomial.eval_eq_sum_range' (by omega : W.natDegree < 5)]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  unfold actualMomentSequence actualMomentTerm
  push_cast
  ring

theorem actualWeighted_hasSum_actual_moments (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    HasSum (actualWeightedSequence n W)
      (∑ r ∈ range 5, (W.coeff r : ℝ) * actualMoment n r) := by
  have hsum : HasSum
      (fun m : ℕ => ∑ r ∈ range 5, (W.coeff r : ℝ) * actualMomentSequence n r m)
      (∑ r ∈ range 5, (W.coeff r : ℝ) * actualMoment n r) := by
    apply hasSum_sum
    intro r hr
    have hr4 : r ≤ 4 := by have := mem_range.mp hr; omega
    exact (actualMomentSequence_summable n r hn hr4).hasSum.mul_left (W.coeff r : ℝ)
  exact hsum.congr (fun m => (actualWeightedSequence_eq_actual_moment_sum n W hW m).symm)

theorem actualWeighted_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    Summable (actualWeightedSequence n W) :=
  (actualWeighted_hasSum_actual_moments n hn W hW).summable

theorem actualWeighted_norm_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    Summable (fun m : ℕ => ‖actualWeightedSequence n W m‖) :=
  (actualWeighted_summable n hn W hW).norm

theorem actualWeighted_tsum_eq_actual_moment_sum (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    (∑' m : ℕ, actualWeightedSequence n W m) =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * actualMoment n r :=
  (actualWeighted_hasSum_actual_moments n hn W hW).tsum_eq

theorem actualMoment_nonneg (n r : ℕ) : 0 ≤ actualMoment n r := by
  unfold actualMoment
  exact tsum_nonneg (actualMomentSequence_nonneg n r)

theorem weightedCoefficientHeight_nonneg (n : ℕ) (W : ℚ[X]) :
    0 ≤ weightedCoefficientHeight n W := by
  unfold weightedCoefficientHeight
  apply Finset.sum_nonneg
  intro r hr
  positivity

theorem actualWeighted_uniform_bound (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    |∑' m : ℕ, actualWeightedSequence n W m| ≤
      analyticPrefactor n * weightedCoefficientHeight n W := by
  rw [actualWeighted_tsum_eq_actual_moment_sum n hn W hW]
  calc
    |∑ r ∈ range 5, (W.coeff r : ℝ) * actualMoment n r| ≤
        ∑ r ∈ range 5, |(W.coeff r : ℝ) * actualMoment n r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r ∈ range 5, |(W.coeff r : ℝ)| * actualMoment n r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [abs_mul, abs_of_nonneg (actualMoment_nonneg n r)]
    _ ≤ ∑ r ∈ range 5, |(W.coeff r : ℝ)| *
        (analyticPrefactor n * (n : ℝ) ^ (2 * r)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr4 : r ≤ 4 := by have := mem_range.mp hr; omega
      exact mul_le_mul_of_nonneg_left (actualMoment_uniform_bound n r hn hr4) (abs_nonneg _)
    _ = analyticPrefactor n * weightedCoefficientHeight n W := by
      unfold weightedCoefficientHeight
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- The bound holds pointwise for any family; its prefactor has no family input. -/
theorem changing_quartics_uniform_bound (W : ℕ → ℚ[X])
    (hW : ∀ n : ℕ, (W n).natDegree ≤ 4) :
    ∀ n : ℕ, 1 ≤ n → |∑' m : ℕ, actualWeightedSequence n (W n) m| ≤
      analyticPrefactor n * weightedCoefficientHeight n (W n) := by
  intro n hn
  exact actualWeighted_uniform_bound n hn (W n) (hW n)

theorem uniformError_tendsto_zero : Tendsto uniformError atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hplus : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 hnat
  have hlog := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hplus
  have hlog' : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
    convert hlog using 1
    funext n
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 2 <;> ring
  have hconst : Tendsto (fun n : ℕ => Real.log momentBoundConstant / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h := hconst.add (hlog'.const_mul 10)
  convert h using 1
  · funext n
    unfold uniformError
    rw [add_div]
    ring
  · norm_num

theorem analyticPrefactor_eq_uniform_exponent (n : ℕ) (hn : 1 ≤ n) :
    analyticPrefactor n = Real.exp ((-(2641 / 250 : ℝ) + uniformError n) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have he : (-(2641 / 250 : ℝ) + uniformError n) * n =
      -(2641 / 250 : ℝ) * n + Real.log momentBoundConstant +
        10 * Real.log ((n : ℝ) + 1) := by
    unfold uniformError
    field_simp [hn0.ne']
    ring
  rw [he]
  rw [show 10 * Real.log ((n : ℝ) + 1) = Real.log (((n : ℝ) + 1) ^ 10) by
    simpa only [Nat.cast_ofNat] using (Real.log_pow ((n : ℝ) + 1) 10).symm]
  unfold analyticPrefactor
  rw [Real.exp_add, Real.exp_add, Real.exp_log momentBoundConstant_pos,
    Real.exp_log (pow_pos hnp 10)]
  ring

/-- Actual weighted route A: an explicit error independent of all quartic coefficients. -/
theorem actual_weighted_uniform_o_one :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * weightedCoefficientHeight n W := by
  refine ⟨uniformError, uniformError_tendsto_zero, ?_⟩
  intro n hn W hW
  rw [← analyticPrefactor_eq_uniform_exponent n hn]
  exact actualWeighted_uniform_bound n hn W hW

end ZetaNine.AnalyticWeightedBound

#print axioms ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum
#print axioms ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments
#print axioms ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable
#print axioms ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound
#print axioms ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound
#print axioms ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero
#print axioms ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one
