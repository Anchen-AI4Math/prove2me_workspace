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

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]
/-- Independent concrete coefficient rows give a surjective hash map.
This supplies every target vector; it is not an assumed uniformity property. -/
theorem solution {v : ι → σ → K} (hv : LinearIndependent K v) :
    Function.Surjective (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap v) := by
  classical
  let f := Fintype.linearCombination K v
  let B : (ι → K) →ₗ[K] (σ → K) →ₗ[K] K :=
    (dotProductEquiv K σ).toLinearMap.comp f
  have hi : Function.Injective B :=
    (dotProductEquiv K σ).injective.comp hv.fintypeLinearCombination_injective
  have hs : Function.Surjective B.flip := (LinearMap.flip_surjective_iff₁).mpr hi
  intro target
  obtain ⟨w, hw⟩ := hs (dotProductEquiv K ι target)
  refine ⟨w, ?_⟩
  funext i
  have he := congrArg (fun φ : Module.Dual K (ι → K) => φ (Pi.single i 1)) hw
  change dotProduct (v i) w = target i
  simpa [B, f, Fintype.linearCombination_apply] using he

#print axioms solution
