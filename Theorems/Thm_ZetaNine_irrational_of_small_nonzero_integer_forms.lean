import Mathlib.NumberTheory.Real.Irrational

-- Local mirror of the private platform theorem
-- ZetaNine.irrational_of_small_nonzero_integer_forms.  Not a proved theorem
-- locally: the body is a placeholder so that reduction modules can resolve the
-- import while the real proof lives on the platform.
namespace ZetaNine

theorem irrational_of_small_nonzero_integer_forms (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b a : ℤ,
        (b : ℝ) + (a : ℝ) * x ≠ 0 ∧
        |(b : ℝ) + (a : ℝ) * x| < ε) :
    Irrational x := by sorry

end ZetaNine
