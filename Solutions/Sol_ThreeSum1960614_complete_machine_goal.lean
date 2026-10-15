import Submission.ThreeSum.FinalSolver

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- This root must compile and pass the axiom audit before any completion claim. -/
theorem solution : EndStatement.ThreeSum.SolvedInTime 1.960614 := by
  convert ThreeSum.solvedInTime_980307_500000 using 1 <;> norm_num

#print axioms solution
