import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem Light.Sec3.realized_threeSum : ∀ (T : ℕ → ℝ → ℝ), Light.SolvedIn Light.s3Task T → ThreeSumApsp.WordRam.Realized EndStatement.ThreeSum T := by sorry
