import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators


theorem ThreeSumSharpTail.sharp_normalized_tail (c m : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    ((∑ d ∈ Finset.Icc (⌈θ * (m : ℝ)⌉₊) m, ThreeSumSharpTail.boxCount c m d : ℕ) : ℝ) /
        (ThreeSumSharpTail.boxCount c m 0 : ℝ) ≤
      ((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
        Real.rpow ((4 : ℝ) ^ m) (-ThreeSumSharpTail.sharpSaving c θ) := by sorry
