import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSPSource_RemainingDefinitions

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.retained_tiles_cost (c m nB : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    (Light.Sec4.tAllTiles (c * m) m ⌈θ * (m : ℝ)⌉₊ nB : ℝ) ≤
      1600 * ((c : ℝ) * m + 1) *
        ((nB : ℝ) ^ 2 * (((m : ℝ) + 1) *
          ((ThreeSumSharpTail.boxCount c m 0 : ℝ) *
            (((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
              Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ)) + 1)) +
          nB + 1) := by sorry
