import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.encoding_bound (c m : ℕ) (hc : 10 < c) (hm : 1 ≤ m) :
    (10 : ℝ) ^ (c * m) / Real.sqrt (ThreeSumSharpTail.boxCount c m 0 : ℝ) ≤
      Real.sqrt (c * m + 1 : ℝ) * (4 ^ m : ℝ) ^ ThreeSumSharpTail.encodingExponent c := by sorry
