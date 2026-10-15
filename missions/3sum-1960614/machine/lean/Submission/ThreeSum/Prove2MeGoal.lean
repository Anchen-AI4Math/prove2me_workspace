import Submission.ThreeSum.FinalSolver

namespace ThreeSum1960614

/-- The mission's exact decimal statement, from the complete rational machine bound. -/
theorem threeSum_1960614 : EndStatement.ThreeSum.SolvedInTime 1.960614 := by
  convert ThreeSum.solvedInTime_980307_500000 using 1 <;> norm_num

end ThreeSum1960614
