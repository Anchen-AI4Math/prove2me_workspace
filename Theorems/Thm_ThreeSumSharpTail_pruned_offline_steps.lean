import Definitions.Def_APSP299791_Defs4

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.pruned_offline_steps (G : Light.Sec4.RatParams)
    (C : ℝ) (hC : 0 ≤ C) (c0 k : ℕ) :
    ∃ A : ℝ, ∀ N D : ℕ, ∀ tp tq : ℝ, ∀ w : ℕ,
      Light.Sec4.CostsWithinP G C N D tp tq →
        (Light.Sec4.tOffline32P c0 G N D w : ℝ) + (k : ℝ) ≤ A * (tp + (w : ℝ) * tq) := by sorry
