import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators


theorem ThreeSumSharpTail.sharp_saving_strict (c θ : ℝ) (hc : 10 < c)
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    0 < ThreeSumSharpTail.oldSaving c θ ∧
    ThreeSumSharpTail.oldSaving c θ < ThreeSumSharpTail.sharpSaving c θ := by sorry
