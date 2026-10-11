import Mathlib.NumberTheory.Real.Irrational

-- Local mirror of the private platform theorem
-- ZetaNine.irrational_of_two_small_integer_forms (Proved).  Not a proved
-- theorem locally: the body is a placeholder so that reduction modules can
-- resolve the import while the real proof lives on the platform.
namespace ZetaNine

theorem irrational_of_two_small_integer_forms (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b₁ a₁ b₂ a₂ : ℤ,
        b₁ * a₂ ≠ b₂ * a₁ ∧
        |(b₁ : ℝ) + (a₁ : ℝ) * x| < ε ∧
        |(b₂ : ℝ) + (a₂ : ℝ) * x| < ε) :
    Irrational x := by sorry

end ZetaNine
