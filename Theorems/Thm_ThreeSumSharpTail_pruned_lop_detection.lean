import Definitions.Def_APSP299791_Defs5

theorem ThreeSumSharpTail.pruned_lop_detection
    (G : Light.Sec4.RatParams) (a s : ℚ)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hsHalf : s < 1 / 2)
    (hcost : ∃ C : ℝ, 0 ≤ C ∧ ∀ N D : ℕ,
      1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      Light.Sec4.CostsWithinP G C N D
        ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ))
        ((D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1))) :
    ∃ (C : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧ Light.lightModel.lopDetect Td ∧
      ∀ n d w : ℕ, 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ (a : ℝ) →
        Td n d w ≤ C * ((n : ℝ) ^ 2 * (Real.log d + 1) ^ 2 / (d : ℝ) ^ (s : ℝ) +
          (w : ℝ) * (d : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log d + 1) + (n : ℝ) * d + w + 1) := by sorry
