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

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring

variable {α : Type*}

theorem ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.two_coordinates_separate {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ i j, (s i, s j) ≠ (t i, t j) ∧
      (s i, s j) ≠ (u i, u j) ∧ (t i, t j) ≠ (u i, u j) := by sorry
