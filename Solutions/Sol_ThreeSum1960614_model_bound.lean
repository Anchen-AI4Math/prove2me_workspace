import Submission.ThreeSum.ModelWitnessBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem solution (e b S th terminal ratio R : ℝ)
    (hmodel : ModelFeasible 232 e b S th terminal ratio R) :
    (196061349120/100000000000 : ℝ) < R :=
  FixedModel.complete_lower_bound e b S th terminal ratio R hmodel

#print axioms solution
