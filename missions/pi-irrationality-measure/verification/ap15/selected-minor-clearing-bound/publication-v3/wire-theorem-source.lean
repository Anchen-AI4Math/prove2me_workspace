import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_entry_truncatedLog_cleared_gaussian

open OAI.PiExponent OAI.PiExponent.MatrixArithmetic
open scoped BigOperators

theorem OAI.PiExponent.MatrixArithmetic.selectedMinor_clearing_bound {m K : ℕ} {w0 v0 θ F H : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (hw0 : 0 < w0)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H)
    (hdet : (selectedMinor K w0 v0 θ F H p q selection).det ≠ 0) :
    -(Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) *
      Real.log (denominator q (truncationOrders q F v0) H) -
      columnCost q selection + rowCost K v0 θ q H ≤
      Real.log ‖(selectedMinor K w0 v0 θ F H p q selection).det‖ := by
  sorry
