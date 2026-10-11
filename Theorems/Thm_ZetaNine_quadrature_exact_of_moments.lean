import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin

-- Local mirror of the private platform theorem
-- ZetaNine.quadrature_exact_of_moments (Proved).  The body is a placeholder so
-- that the five-sample nonvanishing reduction can resolve the import while the
-- real proof lives on the platform.
namespace ZetaNine

theorem quadrature_exact_of_moments
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m) :
    ∀ p : Polynomial ℝ, p.natDegree ≤ 4 →
      L p = ∑ j : Fin 5, w j * p.eval (y j) := by sorry

end ZetaNine
