import Submission.ThreeSum.QuarticSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Light ThreeSum1960614.LightQuarticSwitch

theorem solution {lim : Limits} {μ : ℕ→ℤ} {J j r d : ℕ}
    (hj : j ≤ J) (hne : (candidates J j r).Nonempty)
    (hword : (word J r : ℤ) ≤ lim.word) :
    Meets lim program 0 d [J,j,r] μ (time r)
      (fun result ν => result=(index J j r : ℤ) ∧ ν=μ) :=
  program_meets hj hne hword

#print axioms solution
