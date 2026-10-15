import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_Coloring
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace ThreeSum.Coloring
end ThreeSum.Coloring
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring
end ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring

namespace ThreeSum1960614.MachineScopeRegression

/-!
# A finite, deterministic three-color reduction

The family below enumerates two positions of the binary representation of an
array index and all 81 maps from their four patterns to three colors.  Its
parameter count is exactly `81 * d^2`.  In particular it never enumerates all
three-colorings of the input.  The final equivalence allows repeated input
values and deduplicates each color class into a finite set.
-/

namespace ThreeSum.Coloring

variable {α : Type*}

private theorem private_bbd17590ad_exists_coordinate_ne {s t : α → Bool} (h : s ≠ t) :
    ∃ i, s i ≠ t i := by
  classical
  by_contra hn
  push Not at hn
  exact h (funext hn)





















































end ThreeSum.Coloring

end ThreeSum1960614.MachineScopeRegression

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring

variable {α : Type*}
/-- Two coordinates suffice to distinguish any three different binary words. -/
theorem solution {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ i j, (s i, s j) ≠ (t i, t j) ∧
      (s i, s j) ≠ (u i, u j) ∧ (t i, t j) ≠ (u i, u j) := by
  obtain ⟨i, hi⟩ := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.private_bbd17590ad_exists_coordinate_ne hst
  have hui : u i = s i ∨ u i = t i := by
    cases hs : s i <;> cases ht : t i <;> cases hu : u i <;> simp_all
  rcases hui with hui | hui
  · obtain ⟨j, hj⟩ := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.private_bbd17590ad_exists_coordinate_ne hsu
    refine ⟨i, j, ?_, ?_, ?_⟩
    · exact fun he => hi (congrArg Prod.fst he)
    · exact fun he => hj (congrArg Prod.snd he)
    · intro he
      exact hi ((congrArg Prod.fst he).trans hui).symm
  · obtain ⟨j, hj⟩ := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.private_bbd17590ad_exists_coordinate_ne htu
    refine ⟨i, j, ?_, ?_, ?_⟩
    · exact fun he => hi (congrArg Prod.fst he)
    · intro he
      exact hi ((congrArg Prod.fst he).trans hui)
    · exact fun he => hj (congrArg Prod.snd he)

#print axioms solution
