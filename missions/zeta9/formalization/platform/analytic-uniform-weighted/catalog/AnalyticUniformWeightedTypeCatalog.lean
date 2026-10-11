import Definitions.Def_ZetaNine_AnalyticUniformWeighted
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine
open ZetaNine.AnalyticMomentBounds ZetaNine.AnalyticUniformMomentBound
open ZetaNine.AnalyticWeightedBound

namespace ZetaNine.AnalyticUniformMomentBound
theorem actualMoment_uniform_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    actualMoment n r ≤ momentBoundConstant * ((n : ℝ) + 1) ^ 10 *
      Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r) := by sorry
end ZetaNine.AnalyticUniformMomentBound

namespace ZetaNine.AnalyticWeightedBound
theorem changing_quartics_uniform_bound (W : ℕ → ℚ[X])
    (hW : ∀ n : ℕ, (W n).natDegree ≤ 4) :
    ∀ n : ℕ, 1 ≤ n → |∑' m : ℕ, actualWeightedSequence n (W n) m| ≤
      analyticPrefactor n * weightedCoefficientHeight n (W n) := by sorry
end ZetaNine.AnalyticWeightedBound

namespace ZetaNine.AnalyticWeightedBound
theorem actual_weighted_uniform_o_one :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * weightedCoefficientHeight n W := by sorry
end ZetaNine.AnalyticWeightedBound
