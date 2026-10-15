import Definitions.Def_ThreeSum1960614_Scales

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614 ThreeSum1960614.Schedule

theorem ThreeSum1960614.executable_scale_rounding (m : ℕ) :
    2 ∣ microSize m ∧ 20 ∣ blockCount m ∧
    (0 < microSize m →
      0 ≤ epsilon * (m : ℝ) - totalSize m ∧
      epsilon * (m : ℝ) - totalSize m < 20 * microSize m) ∧
    0 ≤ (-beta) * (totalSize m : ℝ) - bandExponent m ∧
    (-beta) * (totalSize m : ℝ) - bandExponent m < 1 ∧
    0 < bandDivisor m  := by sorry
