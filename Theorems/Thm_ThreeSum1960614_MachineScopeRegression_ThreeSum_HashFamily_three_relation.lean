import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace ThreeSum.HashFamily
end ThreeSum.HashFamily
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily
end ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

open scoped _root_.BigOperators
variable {α K : Type*}
open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

variable [Ring K]

theorem ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.three_relation {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) {a b c : K}
    (h : ∀ p, a * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot s p + b * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot t p + c * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot u p = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by sorry
