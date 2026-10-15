import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSP299791_Defs4
import Theorems.Thm_ThreeSumSharpTail_pruned_cost_certificate
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open ThreeSumApsp Light.Sec4

theorem ThreeSumSharpTail.rational_cost_regime
    (c : ℕ) (η a s : ℚ) (hc : 10 < c)
    (hη0 : 0 < η) (hη9 : η < 9 / 10)
    (ha0 : 0 < a) (ha1 : (a : ℝ) < 1)
    (hs0 : 0 < s) (hs5 : (s : ℝ) < 1 / 2)
    (henc : (a : ℝ) * (ThreeSumSharpTail.encodingExponent c +
      ThreeSumSharpTail.sharpSaving c (η : ℝ)) < 1)
    (hprep : (s : ℝ) < ThreeSumSharpTail.sharpSaving c (η : ℝ))
    (hquery : (s : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent (η : ℝ)) :
    ∃ G : Light.Sec4.RatParams, ∃ C : ℝ, 0 ≤ C ∧
      ∀ N D₀ : ℕ, 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
        Light.Sec4.CostsWithinP G C N D₀
          ((N : ℝ) ^ 2 * (Real.log (D₀ : ℝ) + 1) ^ 2 / (D₀ : ℝ) ^ (s : ℝ))
          ((D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log (D₀ : ℝ) + 1)) := by sorry
