import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614


theorem ThreeSum1960614.quartic_parameter_certificate :
    4648781151243719 / 1000000000000000 < E 232 ∧
    E 232 < 4648781151243720 / 1000000000000000 ∧
    1557987216578 / 1000000000000000 < kappa 232 ∧
    kappa 232 < 1557987216579 / 1000000000000000 ∧
    entropy theta < 244168414687344 / 1000000000000000 ∧
    v < phi theta ∧ threshold tau < phi (1 / 2) ∧
    0 < epsilon * (E 232 + beta) ∧ epsilon * (E 232 + beta) < 1 ∧
    (∀ z ∈ costs, z < principal) ∧ principal < (target : ℝ) := by sorry
