import Definitions.Def_APSP299791_Defs5

theorem ThreeSumSharpTail.full_d_parameter_host (a b c e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hab : a ≤ b) (hce : 2 * c ≤ e) :
    ThreeSumApsp.Claim.Theorem_17 Light.lightModel ThreeSumApsp.strassen
      (fun n => ThreeSumApsp.paramDr a b n)
      (fun n => ThreeSumApsp.paramGr c e (ThreeSumApsp.paramDr a b n)) ∧
      (∀ n, ThreeSumApsp.paramDr a b n = ⌊(n : ℝ) ^ ((a : ℝ) / b)⌋₊) ∧
      (∀ D, 1 ≤ D → ThreeSumApsp.paramGr c e D = ⌈(D : ℝ) ^ ((c : ℝ) / e)⌉₊) := by sorry
