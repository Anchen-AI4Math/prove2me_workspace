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
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_raw_second_moment_five

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







theorem incidenceCount_mono {events events' : E → Finset Ω}
    (h : ∀ e, events e ⊆ events' e) (w : Ω) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount events w ≤ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount events' w := by
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, h e (Finset.mem_filter.mp he).2⟩



end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]















end GraphMoments

section SeparableTrimming

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

















theorem trimmedPairEvent_subset (s t : α → Bool) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool)) (B : ℕ) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.trimmedPairEvent s t a b leftVertices rightVertices B ⊆ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent s t a b :=
  Finset.filter_subset ..



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

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
theorem solution (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (Bbad : ℕ) (hB : ∀ e, (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.badPartners left right e).card ≤ Bbad)
    (hBp : Bbad ≤ 3 * Fintype.card K) (hEp : Fintype.card E ≤ Fintype.card K ^ 2)
    (a b : K) (leftVertices rightVertices : Finset (α → Bool)) (Bbucket : ℕ) :
    Fintype.card K ^ 2 * (∑ w, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount
        (fun e => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.trimmedPairEvent (left e) (right e) a b leftVertices rightVertices Bbucket) w ^ 2) ≤
      5 * Fintype.card E * Fintype.card (α × Bool → K) := by
  refine (Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun w hw => ?_))).trans
    (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.raw_second_moment_five left right hinj hcross Bbad hB hBp hEp a b)
  exact Nat.pow_le_pow_left (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount_mono
    (fun e => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.trimmedPairEvent_subset (left e) (right e) a b leftVertices rightVertices Bbucket) w) 2

#print axioms solution
