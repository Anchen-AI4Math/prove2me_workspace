import Definitions.Def_APSP299791_Defs5

theorem ThreeSumSharpTail.pruned_program_solves (G : Light.Sec4.RatParams) :
    ∃ need : List ℕ → Light.Need, Light.PolyNeedN need ∧
      ∀ (R : Light.Program) (lim : Light.Limits) (fr d : ℕ)
        (x : Light.ThinInst) (μ : ℕ → ℤ) (C tp tq : ℝ),
        0 ≤ C → Light.lopCountTask.Pre x μ fr →
        Light.Sec4.CostsWithinP G C x.N x.D tp tq →
        (need [x.N, x.D, x.w, x.U]).Ok lim fr d →
        Light.Meets lim (Light.Sec4.program31P G ++ R) Light.Sec4.Proc.offline32 (d + 1)
          [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
          (Light.Sec4.tOffline32P Light.Sec4.cShared30 G x.N x.D x.w)
          (fun r μ' => Light.lopCountTask.Post x μ fr r μ') := by sorry
