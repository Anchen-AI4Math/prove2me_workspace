import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614


theorem ThreeSum1960614.fixed_model_lower_bound
    (e b S th terminal ratio R : ℝ)
    (hmodel : ModelFeasible 232 e b S th terminal ratio R) :
    (196061349120 / 100000000000 : ℝ) < R := by sorry
