import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614


theorem ThreeSum1960614.uniform_entropy_bound (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    entropy t < rho * (1 + phi t) := by sorry
