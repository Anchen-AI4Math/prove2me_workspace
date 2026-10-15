import Definitions.Def_APSPSource_PaperStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ThreeSumApsp.WordRam

theorem ThreeSumApsp.WordRam.SolvedInTime.endStatement {Q : EndStatement.Problem} {a : ℝ} (h : SolvedInTime Q a 0)
    {r : ℚ} (hr : (r : ℝ) = a) (hr0 : 0 ≤ r) : Q.SolvedInTime r := by sorry
