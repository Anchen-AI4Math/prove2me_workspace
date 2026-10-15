import Submission.ThreeSum.LightParameterInit

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Light ThreeSum.LightParameterInit

theorem solution {lim : Limits} {P : Program} {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ→ℤ} {n dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+464*half n+6 ≤ lim.depth)
    (hsep : dst+19 ≤ work) (hspace : space work n ≤ lim.space)
    (hword : (word n : ℤ) ≤ lim.word) :
    Meets lim P pMain d [n,dst,work] μ (time n)
      (fun r μ' => r=(ThreeSum.Scales.radix n : ℤ) ∧
        Seg μ' dst (values n) ∧ KeptBut μ μ' work dst 19) := by
  exact S.meets hw hd hsep hspace hword

#print axioms solution
