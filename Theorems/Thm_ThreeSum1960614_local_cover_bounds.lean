import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614


theorem ThreeSum1960614.local_cover_bounds (c h : ℕ)
    (hc : 3 ≤ c) (hh : 0 < h) :
    Nat.choose (c * (2 * h)) h * Nat.choose (c * (2 * h) - h) h =
      Nat.choose (c * (2 * h)) (2 * h) * Nat.choose (2 * h) h ∧
    Nat.choose (c * (2 * h) - h) h ≤ Nat.choose (c * (2 * h)) h ∧
    Nat.choose (2 * h) h < 2 ^ (2 * h) ∧
    2 ^ (2 * h) < Nat.choose (c * (2 * h)) (2 * h) ∧
    Nat.choose (c * (2 * h) - h) h ^ 2 <
      Nat.choose (c * (2 * h)) (2 * h) * 2 ^ (2 * h) := by sorry
