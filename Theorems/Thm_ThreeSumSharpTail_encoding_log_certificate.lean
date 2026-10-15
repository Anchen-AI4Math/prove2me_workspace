import Definitions.Def_ThreeSumSharpTail_Analysis
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.encoding_log_certificate :
    ((693147180559945 / 10^15 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 693147180559946 / 10^15) ∧
    ((2302585092 / 10^9 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ 2302585094 / 10^9) ∧
    ((1098612288 / 10^9 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1098612290 / 10^9) ∧
    ((2197224575 / 10^9 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ 2197224580 / 10^9) ∧
    ((-3044522438 / 10^9 : ℝ) ≤ Real.log (1 / 21) ∧ Real.log (1 / 21) ≤ -3044522436 / 10^9) ∧
    ((-48790165 / 10^9 : ℝ) ≤ Real.log (20 / 21) ∧ Real.log (20 / 21) ≤ -48790163 / 10^9) := by sorry
