import Solutions.Sol_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_actual_HasSum_and_absolute


set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Matrix BigOperators
open Polynomial

namespace ZetaNine.MatrixAuthorAudit
open CoefficientMapAggregate CoefficientMapKernelBridge CoefficientMapMatrix

theorem exact_row_action (n : ℕ) (c : Fin 5 → ℚ) :
    quarticAggregateLinearMap n c = c ᵥ* actualFMatrix n :=
  quarticAggregate_eq_row_vector n c

theorem exact_column_action (n : ℕ) :
    LinearMap.toMatrix' (quarticAggregateLinearMap n) = (actualFMatrix n)ᵀ :=
  column_action_matrix_is_transpose n

theorem exact_determinant (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    (actualFMatrix n).det ≠ 0 := actualFMatrix_det_ne_zero n hn2 hn

theorem exact_inverse_row (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    polynomialCoordinates (inverseMultiplier n hn2 hn b) = b ᵥ* (actualFMatrix n)⁻¹ :=
  inverseMultiplier_coordinates_eq_row_inverse n hn2 hn b

theorem exact_integer_selection (b a : ℤ) :
    selectedIntegerPair b a ᵥ* selectionMatrix =
      (fun j : Fin 5 => if j = 0 then (b : ℚ) else if j = 4 then (a : ℚ) else 0) :=
  selectedIntegerPair_mul_selection b a

theorem exact_actual_sum (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n
      (selectedIntegerMultiplier n hn2 hn b a) ((t + 1 : ℕ) : ℚ) : ℝ))
        ((b : ℝ) + (a : ℝ) * CoefficientMapSummation.zetaReal 9) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n
      (selectedIntegerMultiplier n hn2 hn b a) ((t + 1 : ℕ) : ℚ) : ℝ)‖) :=
  checked_selectedIntegerMultiplier_actual_HasSum_and_absolute n hn2 hn b a

theorem actual_matrix_complete_value (n : ℕ) :
    actualFMatrix n = fun i j => aggregate n (X ^ i.val) j := rfl

theorem selection_complete_value : selectionMatrix =
    fun i j => if i = 0 then (if j = 0 then 1 else 0) else (if j = 4 then 1 else 0) := rfl

theorem pair_complete_value (b a : ℤ) : selectedIntegerPair b a =
    fun i => if i = 0 then (b : ℚ) else (a : ℚ) := rfl

theorem output_complete_value (b a : ℤ) : selectedIntegerOutput b a =
    fun j => if j = 0 then (b : ℚ) else if j = 4 then (a : ℚ) else 0 := rfl

theorem multiplier_complete_value (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ) :
    selectedIntegerMultiplier n hn2 hn b a =
      inverseMultiplier n hn2 hn (selectedIntegerOutput b a) := rfl

theorem pure_nine_multiplier_nonzero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    selectedIntegerMultiplier n hn2 hn 0 1 ≠ 0 := by
  intro hzero
  have h := selectedIntegerMultiplier_actual_output n hn2 hn 0 1
  have hmap : aggregate n (0 : ℚ[X]) = 0 := by
    change (aggregateLinearMap n) 0 = 0
    exact map_zero (aggregateLinearMap n)
  rw [hzero, hmap] at h
  have h4 := congrFun h (4 : Fin 5)
  norm_num [selectedIntegerOutput, Fin.ext_iff] at h4

end ZetaNine.MatrixAuthorAudit

#print axioms ZetaNine.MatrixAuthorAudit.exact_row_action
#print axioms ZetaNine.MatrixAuthorAudit.exact_column_action
#print axioms ZetaNine.MatrixAuthorAudit.exact_determinant
#print axioms ZetaNine.MatrixAuthorAudit.exact_inverse_row
#print axioms ZetaNine.MatrixAuthorAudit.exact_integer_selection
#print axioms ZetaNine.MatrixAuthorAudit.exact_actual_sum
#print axioms ZetaNine.MatrixAuthorAudit.actual_matrix_complete_value
#print axioms ZetaNine.MatrixAuthorAudit.selection_complete_value
#print axioms ZetaNine.MatrixAuthorAudit.pair_complete_value
#print axioms ZetaNine.MatrixAuthorAudit.output_complete_value
#print axioms ZetaNine.MatrixAuthorAudit.multiplier_complete_value
#print axioms ZetaNine.MatrixAuthorAudit.pure_nine_multiplier_nonzero
