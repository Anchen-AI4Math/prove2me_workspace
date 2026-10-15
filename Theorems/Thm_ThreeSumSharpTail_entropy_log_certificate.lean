import Definitions.Def_ThreeSumSharpTail_Analysis
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.entropy_log_certificate :
    ((-3163328497 / 10^9 : ℝ) ≤ Real.log (44399 / 1050000) ∧ Real.log (44399 / 1050000) ≤ -3163328495 / 10^9) ∧
    ((-43204792 / 10^9 : ℝ) ≤ Real.log (1005601 / 1050000) ∧ Real.log (1005601 / 1050000) ≤ -43204790 / 10^9) ∧
    ((-2189077853 / 10^9 : ℝ) ≤ Real.log (5601 / 50000) ∧ Real.log (5601 / 50000) ≤ -2189077851 / 10^9) ∧
    ((-118806060 / 10^9 : ℝ) ≤ Real.log (44399 / 50000) ∧ Real.log (44399 / 50000) ≤ -118806057 / 10^9) := by sorry
