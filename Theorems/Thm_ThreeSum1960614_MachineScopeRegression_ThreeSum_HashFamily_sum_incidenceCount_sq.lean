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

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]

theorem ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.sum_incidenceCount_sq (events : E → Finset Ω) :
    (∑ w, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount events w ^ 2) =
      ∑ e, ∑ f, (events e ∩ events f).card := by sorry
