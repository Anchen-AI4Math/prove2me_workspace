import Mathlib.NumberTheory.LSeries.RiemannZeta

-- Local mirror of the private platform theorem
-- ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine (Open).  The body is a
-- placeholder: this node is an open obligation of the mission, imported as a
-- child of the goal's one-form reduction.
namespace ZetaNine

theorem exponentially_small_nonzero_forms_of_zeta_nine :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by sorry

end ZetaNine
