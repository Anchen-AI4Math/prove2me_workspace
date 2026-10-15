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
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_raw_second_moment

namespace ThreeSum.HashFamily
end ThreeSum.HashFamily
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily
end ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

open scoped _root_.BigOperators
variable {α K : Type*}
open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
/-- The paper's coarse `5 lambda` raw second-moment bound follows from
explicit graph-size and exceptional-partner inequalities. -/
theorem solution (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (B : ℕ) (hB : ∀ e, (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.badPartners left right e).card ≤ B)
    (hBp : B ≤ 3 * Fintype.card K) (hEp : Fintype.card E ≤ Fintype.card K ^ 2)
    (a b : K) :
    Fintype.card K ^ 2 *
        (∑ w, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount (fun e => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left e) (right e) a b) w ^ 2) ≤
      5 * Fintype.card E * Fintype.card (α × Bool → K) := by
  have hp : 0 < Fintype.card K ^ 2 := pow_pos Fintype.card_pos _
  have hs := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.raw_second_moment left right hinj hcross B hB a b
  have hE : Fintype.card E ^ 2 ≤ Fintype.card E * Fintype.card K ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left (Fintype.card E) hEp
  have hBB : Fintype.card E * B * Fintype.card K ≤
      3 * Fintype.card E * Fintype.card K ^ 2 := by
    have h := Nat.mul_le_mul_right (Fintype.card K)
      (Nat.mul_le_mul_left (Fintype.card E) hBp)
    convert h using 1 <;> ring
  have hs' : Fintype.card K ^ 4 *
      (∑ w, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.incidenceCount (fun e => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.pairEvent (left e) (right e) a b) w ^ 2) ≤
        Fintype.card (α × Bool → K) * (5 * Fintype.card E * Fintype.card K ^ 2) := by
    refine hs.trans (Nat.mul_le_mul_left _ ?_)
    nlinarith only [hE, hBB]
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card K ^ 2) ?_ hp
  convert hs' using 1 <;> ring

#print axioms solution
