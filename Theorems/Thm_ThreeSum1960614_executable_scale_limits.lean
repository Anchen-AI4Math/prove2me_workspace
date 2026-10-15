import Definitions.Def_ThreeSum1960614_Scales

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614 ThreeSum1960614.Schedule
open Filter
open scoped Topology

theorem ThreeSum1960614.executable_scale_limits :
    Tendsto (fun m : ℕ => (microSize m : ℝ) ^ 2 / m) atTop (𝓝 0) ∧
    Tendsto (fun m : ℕ => (totalSize m : ℝ) / m) atTop (𝓝 epsilon) ∧
    Tendsto (fun m : ℕ => (bandExponent m : ℝ) / m) atTop (𝓝 ((-beta) * epsilon)) ∧
    Tendsto (fun m : ℕ => Real.log (bandDivisor m : ℝ) / m) atTop
      (𝓝 (Real.log 2 * ((-beta) * epsilon)))  := by sorry
