import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.tangent_log_bounds :
    -Real.log (1 - tangentPoint) / Real.log 2 < (272298515211 / 1000000000000 : ℝ) ∧
    (-Real.log (1 - tangentPoint) - Real.log tangentPoint) / (2 * Real.log 2) <
      (140590616299 / 100000000000 : ℝ)  := by sorry
