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



theorem exists_coordinate_ne {s t : α → Bool} (hst : s ≠ t) :
    ∃ i, s i ≠ t i := by
  classical
  by_contra h
  push Not at h
  exact hst (funext h)

section Relations

variable [Ring K]

/-- Two distinct one-hot words have no nontrivial linear relation. -/
theorem two_relation {s t : α → Bool} (hst : s ≠ t) {a b : K}
    (h : ∀ p, a * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot s p + b * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot t p = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨i, hi⟩ := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.exists_coordinate_ne hst
  have ha := h (i, s i)
  have hb := h (i, t i)
  simpa [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot, hi, Ne.symm hi] using And.intro ha hb





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

variable [Ring K]
/-- Any three pairwise distinct binary one-hot words are independent.
At a coordinate separating the first two words, the third agrees with one
of them, leaving one coefficient isolated. -/
theorem solution {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) {a b c : K}
    (h : ∀ p, a * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot s p + b * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot t p + c * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot u p = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨i, hi⟩ := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.exists_coordinate_ne hst
  have hu : u i = s i ∨ u i = t i := by
    cases hs : s i <;> cases ht : t i <;> cases hu : u i <;> simp_all
  rcases hu with hu | hu
  · have hb : b = 0 := by
      simpa [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot, hi, Ne.symm hi, hu] using h (i, t i)
    have hac : a = 0 ∧ c = 0 := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.two_relation hsu fun p => by simpa [hb] using h p
    exact ⟨hac.1, hb, hac.2⟩
  · have ha : a = 0 := by
      simpa [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot, hi, Ne.symm hi, hu] using h (i, s i)
    have hbc : b = 0 ∧ c = 0 := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.two_relation htu fun p => by simpa [ha] using h p
    exact ⟨ha, hbc.1, hbc.2⟩

#print axioms solution
