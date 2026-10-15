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
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_hashMap_surjective
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_linear_fiber_card
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_three_relation

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



theorem oneHot_three_independent {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    LinearIndependent K ![_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot (K := K) s, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot t, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot u] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.three_relation hst hsu htu (a := g 0) (b := g 1) (c := g 2) (fun p => by
    have hp := congrFun hg p
    simpa [Fin.sum_univ_succ, add_assoc] using hp)
  fin_cases i <;> simp_all



end LinearIndependence

section UniformFibers

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]









/-- The exact joint-output count for independent hash coefficient rows. -/
theorem hash_fiber_card [Fintype K] [DecidableEq K] [DecidableEq σ] [DecidableEq ι]
    {v : ι → σ → K}
    (hv : LinearIndependent K v) (target : ι → K) :
    Fintype.card K ^ Fintype.card ι *
        (Finset.univ.filter (fun w : σ → K => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap v w = target)).card =
      Fintype.card K ^ Fintype.card σ := by
  classical
  simpa using _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.linear_fiber_card (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap v) (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap_surjective hv) target

end UniformFibers

section ActualHashes

variable {ι : Type*} [Fintype α] [Field K]



theorem hashValue_eq_dotProduct (w : α × Bool → K) (s : α → Bool) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue w s = ∑ p, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot (K := K) s p * w p := by
  classical
  simp [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot, Fintype.sum_prod_type]

theorem hashValue_family (v : ι → α → Bool) (w : α × Bool → K)
    [Fintype ι] :
    (fun i => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue w (v i)) = _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap (fun i => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot (K := K) (v i)) w := by
  funext i
  exact _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue_eq_dotProduct w (v i)

end ActualHashes

section WordEvents

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]





theorem wordEvent_eq_linear_fiber {r : ℕ}
    (words : Fin r → α → Bool) (target : Fin r → K) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent words target =
      Finset.univ.filter (fun w => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap (fun i => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot (K := K) (words i)) w = target) := by
  ext w
  simp only [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashValue_family]
  exact funext_iff.symm

/-- Exact uniform joint count, instantiated with the actual one-hot family. -/
theorem wordEvent_card {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K)
    (hwords : LinearIndependent K (fun i => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot (K := K) (words i))) :
    Fintype.card K ^ r * (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent words target).card =
      Fintype.card (α × Bool → K) := by
  rw [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent_eq_linear_fiber]
  simpa using _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hash_fiber_card hwords target











theorem tripleEvent_card {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (a b c : K) :
    Fintype.card K ^ 3 * (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent ![s, t, u] ![a, b, c]).card =
      Fintype.card (α × Bool → K) := by
  apply _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent_card
  convert _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot_three_independent (K := K) hst hsu htu using 1
  funext i
  fin_cases i <;> rfl









end WordEvents

section IncidenceCounting

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]











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

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
/-- Two distinct edges always impose at least three independent hash tests
when the left and right vertex classes are disjoint. -/
theorem solution {s t u v : α → Bool}
    (hst : s ≠ t) (hsv : s ≠ v) (htu : t ≠ u) (huv : u ≠ v)
    (hpair : (s, t) ≠ (u, v)) (a b : K) :
    Fintype.card K ^ 3 * (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent s t a b ∩ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent u v a b).card ≤
      Fintype.card (α × Bool → K) := by
  by_cases hsu : s = u
  · have htv : t ≠ v := by
      intro htv
      exact hpair (Prod.ext hsu htv)
    have hsub : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent s t a b ∩ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent u v a b ⊆
        _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent ![s, t, v] ![a, b, b] := by
      intro w hw
      simpa [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent, Fin.forall_fin_succ] using
        And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).1
          (And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).2
            ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2).2)
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans_eq
      (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.tripleEvent_card hst hsv htv a b b)
  · have hsub : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent s t a b ∩ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent u v a b ⊆
        _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent ![s, t, u] ![a, b, a] := by
      intro w hw
      simpa [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.wordEvent, Fin.forall_fin_succ] using
        And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).1
          (And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).2
            ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2).1)
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans_eq
      (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.tripleEvent_card hst hsu htu a b a)

#print axioms solution
