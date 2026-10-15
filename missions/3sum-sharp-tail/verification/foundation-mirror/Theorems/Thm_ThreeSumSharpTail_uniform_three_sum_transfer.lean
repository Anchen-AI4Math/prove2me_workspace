import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_ThreeSumSource_ReductionClaims

theorem ThreeSumSharpTail.uniform_three_sum_transfer (δ : ℝ) (r : ℚ) (e : ℕ)
    (hδ : δ ≤ 1) (hr : 2 - δ / 2 < (r : ℝ))
    (hu : ThreeSumApsp.Claim.ExactTriangleUniform Light.lightModel δ e) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry
