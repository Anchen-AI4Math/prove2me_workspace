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
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_Coloring_two_coordinates_separate

namespace ThreeSum.Coloring
end ThreeSum.Coloring
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring
end ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring

variable {α : Type*}

theorem ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.reduction_correct {n : ℕ} (x : Fin n → ℤ) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.DistinctZeroSum x ↔ ∃ c ∈ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.family n,
      _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.ThreeSetWitness (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.values x c 0) (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.values x c 1) (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.negValues x c) := by sorry
