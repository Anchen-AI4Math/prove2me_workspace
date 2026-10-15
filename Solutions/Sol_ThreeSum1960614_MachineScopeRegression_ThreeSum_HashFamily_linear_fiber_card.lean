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
/-- Equal-sized fibers of a surjective linear map, with the full sample
space cardinality on the right. This exact integer equality is the finite
uniform-distribution statement used in the hash moments. -/
theorem solution {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype V] [Fintype W] [DecidableEq W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (target : W) :
    Fintype.card W * (Finset.univ.filter (fun x => f x = target)).card =
      Fintype.card V := by
  classical
  have heq : ∀ y : W, (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = target)).card := by
    intro y
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf target)
  calc
    Fintype.card W * (Finset.univ.filter (fun x => f x = target)).card =
        ∑ y : W, (Finset.univ.filter (fun x => f x = y)).card := by
      simp [heq]
    _ = ∑ y : W, ∑ x : V, if f x = y then (1 : ℕ) else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x : V, ∑ y : W, if f x = y then (1 : ℕ) else 0 := Finset.sum_comm
    _ = Fintype.card V := by simp

#print axioms solution
