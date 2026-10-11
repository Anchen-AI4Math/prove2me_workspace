-- UNCOMPILED INDEPENDENT SOURCE-ONLY CONTRACT: requires its own isolated context.
import Solutions.Sol_ZetaNine_AnalyticWeightedBound_actual_weighted_uniform_o_one
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine
open ZetaNine.AnalyticMomentBounds ZetaNine.AnalyticUniformMomentBound ZetaNine.AnalyticWeightedBound
namespace GAIRawContract

theorem raw_real_rational_quartic_bound (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    |∑' m : ℕ, ((CoefficientMap.actualR n ((m + 1 : ℕ) : ℚ) *
      W.eval (((m + 1 : ℕ) : ℚ) * (((m + 1 : ℕ) : ℚ) + (n : ℚ))) : ℚ) : ℝ)| ≤
      (5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7) *
        ((n : ℝ) + 1) ^ 10 * Real.exp (-(2641 / 250 : ℝ) * n) *
          (∑ r ∈ range 5, |(W.coeff r : ℝ)| * (n : ℝ) ^ (2 * r)) := by
  simpa only [actualWeightedSequence, CoefficientMap.weightedR, analyticPrefactor,
    weightedCoefficientHeight, momentBoundConstant] using actualWeighted_uniform_bound n hn W hW

theorem raw_real_rational_quartic_norm_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    Summable (fun m : ℕ => ‖((CoefficientMap.actualR n ((m + 1 : ℕ) : ℚ) *
      W.eval (((m + 1 : ℕ) : ℚ) * (((m + 1 : ℕ) : ℚ) + (n : ℚ))) : ℚ) : ℝ)‖) := by
  simpa only [actualWeightedSequence, CoefficientMap.weightedR] using actualWeighted_norm_summable n hn W hW

theorem raw_five_true_moments_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, (CoefficientMap.actualR n ((m + 1 : ℕ) : ℚ) : ℝ) *
      (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + (n : ℝ))) ^ r) ≤
      (5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7) *
        ((n : ℝ) + 1) ^ 10 * Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r) := by
  simpa only [actualMoment, actualMomentSequence, actualMomentTerm, momentBoundConstant] using
    actualMoment_uniform_bound n r hn hr

theorem explicit_error_limit : Tendsto
    (fun n : ℕ => (Real.log (5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7) +
      10 * Real.log ((n : ℝ) + 1)) / (n : ℝ)) atTop (𝓝 0) := by
  change Tendsto uniformError atTop (𝓝 0)
  exact uniformError_tendsto_zero

end GAIRawContract
