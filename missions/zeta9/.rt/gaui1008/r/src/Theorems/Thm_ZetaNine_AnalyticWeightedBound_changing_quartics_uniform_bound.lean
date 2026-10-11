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

namespace ZetaNine.AnalyticWeightedBound
theorem changing_quartics_uniform_bound (W : ℕ → ℚ[X])
    (hW : ∀ n : ℕ, (W n).natDegree ≤ 4) :
    ∀ n : ℕ, 1 ≤ n → |∑' m : ℕ, actualWeightedSequence n (W n) m| ≤
      analyticPrefactor n * weightedCoefficientHeight n (W n) := by sorry
end ZetaNine.AnalyticWeightedBound
