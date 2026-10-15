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

namespace ThreeSum1960614.MachineScopeRegression

/-!
# The actual one-hot hash family

This file develops the dependence classification of the binary one-hot hash
vectors used in the local cover. Hash weights are independent field elements
at coordinate/symbol pairs. The independence statements concern this concrete
family, not an assumed random oracle.
-/

namespace ThreeSum.HashFamily

open scoped _root_.BigOperators

variable {α K : Type*}





section Relations

variable [Ring K]







end Relations

section LinearIndependence

variable [Field K]







end LinearIndependence

section UniformFibers

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]











end UniformFibers

section ActualHashes

variable {ι : Type*} [Fintype α] [Field K]







end ActualHashes

section WordEvents

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





























end WordEvents

section IncidenceCounting

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]



theorem incidenceCount_eq_sum (events : E → Finset Ω) (w : Ω) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount events w = ∑ e, if w ∈ events e then (1 : ℕ) else 0 := by
  unfold _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]







end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]















end GraphMoments

section SeparableTrimming

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





















end SeparableTrimming

section TrimmedGraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





end TrimmedGraphMoments

end ThreeSum.HashFamily

end ThreeSum1960614.MachineScopeRegression

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

open scoped _root_.BigOperators
variable {α K : Type*}
open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
/-- Exact second-moment expansion over edge pairs, with no independence
assumption and no probabilistic approximation. -/
theorem solution (events : E → Finset Ω) :
    (∑ w, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount events w ^ 2) =
      ∑ e, ∑ f, (events e ∩ events f).card := by
  calc
    (∑ w, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount events w ^ 2) =
        ∑ w, ∑ e, ∑ f,
          if w ∈ events e ∧ w ∈ events f then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount_eq_sum, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      by_cases he : w ∈ events e <;> by_cases hf : w ∈ events f <;> simp [he, hf]
    _ = ∑ e, ∑ f, ∑ w,
          if w ∈ events e ∧ w ∈ events f then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_comm
    _ = ∑ e, ∑ f, (events e ∩ events f).card := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro f hf
      simp [← Finset.mem_inter]

#print axioms solution
