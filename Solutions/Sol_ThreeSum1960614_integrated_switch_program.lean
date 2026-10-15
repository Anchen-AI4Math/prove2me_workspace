import Submission.ThreeSum.LightSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Light ThreeSum

theorem solution {lim : Limits} {μ : ℕ→ℤ} {n j d : ℕ}
    (hj : j ≤ Switch.terminalDepth n)
    (hword : (LightSwitch.word (Scales.blockCount (Scales.inputBits n))
      (Switch.residualSize n j) : ℤ) ≤ lim.word) :
    Meets lim LightSwitch.program 0 d
      [Scales.blockCount (Scales.inputBits n),j,Switch.residualSize n j] μ
      (LightSwitch.time (Switch.residualSize n j))
      (fun result ν => result=(Switch.actualSwitch n j : ℤ) ∧ ν=μ) := by
  exact LightSwitch.actual_meets hj hword

#print axioms solution
