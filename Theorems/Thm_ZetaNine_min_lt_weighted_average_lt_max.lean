import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- Local mirror of the private platform theorem
-- ZetaNine.min_lt_weighted_average_lt_max.  The body is a placeholder so that the
-- weighted-mediant reduction can resolve the import while the real proof lives on
-- the platform.
namespace ZetaNine

theorem min_lt_weighted_average_lt_max
    (w r : Fin 5 → ℝ) (hw : ∀ j : Fin 5, 0 < w j)
    (hsum : ∑ j : Fin 5, w j = 1)
    (hnd : ∃ j j' : Fin 5, r j ≠ r j') :
    (∃ j : Fin 5, r j < ∑ i : Fin 5, w i * r i) ∧
      (∃ j : Fin 5, (∑ i : Fin 5, w i * r i) < r j) := by sorry

end ZetaNine
