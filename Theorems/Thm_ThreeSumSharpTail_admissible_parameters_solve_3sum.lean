import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators


theorem ThreeSumSharpTail.admissible_parameters_solve_3sum
    (c : ℕ) (θ : ℝ) (a s r : ℚ) (hc : 10 < c)
    (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (henc : (a : ℝ) * (ThreeSumSharpTail.encodingExponent c + ThreeSumSharpTail.sharpSaving c θ) < 1)
    (hprep : (s : ℝ) < ThreeSumSharpTail.sharpSaving c θ)
    (hquery : (s : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent θ)
    (hprime : Real.log 7 / Real.log 2 + 3 * (a : ℝ) / 2 < 3 - (a : ℝ) * s / 2)
    (hbuild : 2 + (a : ℝ) * (1 + (s : ℝ) / 2) < 3 - (a : ℝ) * s / 2)
    (hr : 2 - a * s / 4 < r) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry
