import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614


theorem ThreeSum1960614.quartic_switch_bounds (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    phi t ≤ gamma 232 t ∧ 0 < phiDeriv t ∧ phiDeriv t < 9 ∧
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t := by sorry
