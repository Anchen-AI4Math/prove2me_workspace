import Submission.ThreeSum.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch Set

theorem solution (n j : ℕ) (hmu : 0 < mu n) (hj : j ≤ terminalDepth n) :
    let a : ℝ := (j : ℝ)/blockCount (inputBits n)
    let t : ℝ := (actualSwitch n j : ℝ)/residualSize n j
    t ∈ Icc (0 : ℝ) (1/2) ∧
      boxSaving ≤ 2*bandShift-a+(1-a)*gamma t ∧
      (1-a)*entropy t < entropyRatio*(1+boxSaving-2*bandShift)+9*entropyRatio/mu n := by
  exact actual_switch_certified hmu hj

#print axioms solution
