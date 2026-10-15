import Submission.ThreeSum.ActualQuarticSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Light ThreeSum1960614.Schedule ThreeSum1960614.LightQuarticSwitch

theorem solution {lim : Limits} {μ : ℕ→ℤ} {n j d : ℕ}
    (hj : j ≤ terminalDepth n)
    (hword : (word (blockCount (inputBits n)) (residualSize n j) : ℤ) ≤ lim.word) :
    Meets lim program 0 d
      [blockCount (inputBits n),j,residualSize n j] μ (time (residualSize n j))
      (fun result ν => result=(actualIndex n j : ℤ) ∧ ν=μ) :=
  actual_meets hj hword

#print axioms solution
