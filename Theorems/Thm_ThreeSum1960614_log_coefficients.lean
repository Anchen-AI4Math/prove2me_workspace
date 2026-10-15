import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.log_coefficients :
    (693147180559945 / 10^15 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (693147180559946 / 10^15 : ℝ) ∧
    (785174904 / 100000000 : ℝ) * Real.log 2 < Real.log 231 ∧
    (2 * 72447023 / 100000000 : ℝ) * Real.log 2 ≤ 1 + (1 / 231 : ℝ) ∧
    (3 * 24044466 / 100000000 : ℝ) * Real.log 2 ≤ (1 - (1 / 231 : ℝ) ^ 2) / 2 ∧
    (4 * 12022459 / 100000000 : ℝ) * Real.log 2 ≤ (1 + (1 / 231 : ℝ) ^ 3) / 3  := by sorry
