import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.cleared_switch_equivalence (J s j q : ℕ) (hJ : 0 < J) (hs : 0 < s) (hj : j < J) :
    clearedSwitch J s j q ↔
      threshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / ((J - j) * s))  := by sorry
