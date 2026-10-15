import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.pruned_encoding_comparison (c : ℝ) (hc : 1 < c) :
    ((c / 2) * ThreeSumSharpTail.entropy (1 / c) + (c - 1) * Real.log 3) / Real.log 4
      ≤ ThreeSumSharpTail.encodingExponent c := by sorry
