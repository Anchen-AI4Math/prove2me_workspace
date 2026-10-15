import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators


theorem ThreeSumSharpTail.explicit_parameter_certificate :
    (0.05665 : ℝ) * (ThreeSumSharpTail.encodingExponent 21 + ThreeSumSharpTail.sharpSaving 21 0.11202) < 1 ∧
    (0.06945 : ℝ) < ThreeSumSharpTail.sharpSaving 21 0.11202 ∧
    (0.06945 : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent 0.11202 ∧
    Real.log 7 / Real.log 2 + 3 * (0.05665 : ℝ) / 2 < 3 - 0.05665 * 0.06945 / 2 ∧
    2 + (0.05665 : ℝ) * (1 + 0.06945 / 2) < 3 - 0.05665 * 0.06945 / 2 ∧
    (2 - (0.05665 : ℚ) * 0.06945 / 4) = 1.999016414375 ∧
    (1.999017 : ℚ) - (2 - 0.05665 * 0.06945 / 4) = 0.000000585625 := by sorry
