import Submission.ThreeSum.LightSwitchCosts

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum.LightSwitchCosts ThreeSum.Scales

theorem solution (n j : ℕ) :
    ThreeSum.LightSwitch.time (ThreeSum.Switch.residualSize n j) ≤ timeBudget n ∧
    ThreeSum.LightSwitch.word (blockCount (inputBits n)) (ThreeSum.Switch.residualSize n j) ≤
      wordBudget n ∧
    ThreeSum.StageBounds.PowerBound allTimeBudget 0 ∧
    ThreeSum.StageBounds.PowerBound wordBudget 0 := by
  exact ⟨time_le_budget n j,word_le_budget n j,all_time_powerBound,word_powerBound⟩

#print axioms solution
