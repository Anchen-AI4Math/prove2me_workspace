import Solutions.Sol_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_coordinates_product
import Lean

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped Matrix BigOperators
open Polynomial
namespace IndependentMatrixExpected
open ZetaNine CoefficientMapAggregate CoefficientMapKernelBridge CoefficientMapMatrix

theorem actualFMatrix_value : actualFMatrix =
    fun (n : Nat) (i j : Fin 5) => aggregate n ((X : Rat[X]) ^ i.val) j := rfl
theorem selectionMatrix_value : selectionMatrix =
    fun (i : Fin 2) (j : Fin 5) => if i = 0 then (if j = 0 then 1 else 0) else (if j = 4 then 1 else 0) := rfl
theorem selectedIntegerPair_value : selectedIntegerPair =
    fun (b a : Int) (i : Fin 2) => if i = 0 then (b : Rat) else (a : Rat) := rfl
theorem selectedIntegerOutput_value : selectedIntegerOutput =
    fun (b a : Int) (j : Fin 5) => if j = 0 then (b : Rat) else if j = 4 then (a : Rat) else 0 := rfl
theorem selectedIntegerMultiplier_value : selectedIntegerMultiplier =
    fun (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b a : Int) =>
      inverseMultiplier n hn2 hn (selectedIntegerOutput b a) := rfl

theorem expected_quarticAggregate_eq_row_vector : ∀ (n : Nat) (c : Fin 5 → Rat),
    quarticAggregateLinearMap n c = c ᵥ* actualFMatrix n := quarticAggregate_eq_row_vector
theorem expected_coordinatePolynomial_single_one : ∀ i : Fin 5,
    coordinatePolynomial (Pi.single i 1) = (X : Rat[X]) ^ i.val := coordinatePolynomial_single_one
theorem expected_column_action_matrix_is_transpose : ∀ n : Nat,
    LinearMap.toMatrix' (quarticAggregateLinearMap n) = (actualFMatrix n)ᵀ := column_action_matrix_is_transpose
theorem expected_actualFMatrix_row_action_bijective : ∀ n : Nat, 2 ≤ n → Even n →
    Function.Bijective (actualFMatrix n).vecMul := actualFMatrix_row_action_bijective
theorem expected_actualFMatrix_det_isUnit : ∀ n : Nat, 2 ≤ n → Even n →
    IsUnit (actualFMatrix n).det := actualFMatrix_det_isUnit
theorem expected_actualFMatrix_det_ne_zero : ∀ n : Nat, 2 ≤ n → Even n →
    (actualFMatrix n).det ≠ 0 := actualFMatrix_det_ne_zero
theorem expected_inverseMultiplier_coordinates_eq_row_inverse :
    ∀ (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → Rat),
      polynomialCoordinates (inverseMultiplier n hn2 hn b) = b ᵥ* (actualFMatrix n)⁻¹ :=
  inverseMultiplier_coordinates_eq_row_inverse
theorem expected_inverseMultiplier_eq_coordinatePolynomial_row_inverse :
    ∀ (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → Rat),
      inverseMultiplier n hn2 hn b = coordinatePolynomial (b ᵥ* (actualFMatrix n)⁻¹) :=
  inverseMultiplier_eq_coordinatePolynomial_row_inverse
theorem expected_selectedIntegerPair_mul_selection : ∀ b a : Int,
    selectedIntegerPair b a ᵥ* selectionMatrix = selectedIntegerOutput b a := selectedIntegerPair_mul_selection
theorem expected_selectedIntegerMultiplier_coordinates :
    ∀ (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b a : Int),
      polynomialCoordinates (selectedIntegerMultiplier n hn2 hn b a) =
        (selectedIntegerPair b a ᵥ* selectionMatrix) ᵥ* (actualFMatrix n)⁻¹ := selectedIntegerMultiplier_coordinates
theorem expected_selectedIntegerMultiplier_coordinates_product :
    ∀ (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b a : Int),
      polynomialCoordinates (selectedIntegerMultiplier n hn2 hn b a) =
        selectedIntegerPair b a ᵥ* (selectionMatrix * (actualFMatrix n)⁻¹) := checked_selectedIntegerMultiplier_coordinates_product
theorem expected_selectedIntegerMultiplier_natDegree_le :
    ∀ (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b a : Int),
      (selectedIntegerMultiplier n hn2 hn b a).natDegree ≤ 4 := selectedIntegerMultiplier_natDegree_le
theorem expected_selectedIntegerMultiplier_actual_output :
    ∀ (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b a : Int),
      aggregate n (selectedIntegerMultiplier n hn2 hn b a) = selectedIntegerOutput b a := selectedIntegerMultiplier_actual_output
theorem expected_selectedIntegerMultiplier_five_actual_coordinates :
    ∀ (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b a : Int),
      CoefficientMapFiniteSum.constantTerm n (selectedIntegerMultiplier n hn2 hn b a) = (b : Rat) ∧
      CoefficientMapFiniteSum.rho n 3 (selectedIntegerMultiplier n hn2 hn b a) = 0 ∧
      CoefficientMapFiniteSum.rho n 5 (selectedIntegerMultiplier n hn2 hn b a) = 0 ∧
      CoefficientMapFiniteSum.rho n 7 (selectedIntegerMultiplier n hn2 hn b a) = 0 ∧
      CoefficientMapFiniteSum.rho n 9 (selectedIntegerMultiplier n hn2 hn b a) = (a : Rat) := selectedIntegerMultiplier_five_actual_coordinates
theorem expected_selected_prescribed_L : ∀ b a : Int,
    prescribedL (selectedIntegerOutput b a) = (b : Real) + (a : Real) * CoefficientMapSummation.zetaReal 9 := selected_prescribed_L
theorem expected_selectedIntegerMultiplier_actual_exact_L :
    ∀ (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b a : Int),
      CoefficientMapSummation.exactL n (selectedIntegerMultiplier n hn2 hn b a) =
        (b : Real) + (a : Real) * CoefficientMapSummation.zetaReal 9 := selectedIntegerMultiplier_actual_exact_L
theorem expected_selectedIntegerMultiplier_actual_HasSum_and_absolute :
    ∀ (n : Nat) (hn2 : 2 ≤ n) (hn : Even n) (b a : Int),
      HasSum (fun t : Nat => (CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
        ((t + 1 : Nat) : Rat) : Real)) ((b : Real) + (a : Real) * CoefficientMapSummation.zetaReal 9) ∧
      Summable (fun t : Nat => ‖(CoefficientMap.weightedR n (selectedIntegerMultiplier n hn2 hn b a)
        ((t + 1 : Nat) : Rat) : Real)‖) := selectedIntegerMultiplier_actual_HasSum_and_absolute
end IndependentMatrixExpected
open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    unless name.getPrefix == `IndependentMatrixExpected do continue
    let .thmInfo _ := ci | continue
    let axs ← collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress


open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  for (label,actual,expectedName) in [("ZetaNine.CoefficientMapMatrix.quarticAggregate_eq_row_vector", `ZetaNine.CoefficientMapMatrix.quarticAggregate_eq_row_vector, `IndependentMatrixExpected.expected_quarticAggregate_eq_row_vector), ("ZetaNine.CoefficientMapMatrix.coordinatePolynomial_single_one", `ZetaNine.CoefficientMapMatrix.coordinatePolynomial_single_one, `IndependentMatrixExpected.expected_coordinatePolynomial_single_one), ("ZetaNine.CoefficientMapMatrix.column_action_matrix_is_transpose", `ZetaNine.CoefficientMapMatrix.column_action_matrix_is_transpose, `IndependentMatrixExpected.expected_column_action_matrix_is_transpose), ("ZetaNine.CoefficientMapMatrix.actualFMatrix_row_action_bijective", `ZetaNine.CoefficientMapMatrix.actualFMatrix_row_action_bijective, `IndependentMatrixExpected.expected_actualFMatrix_row_action_bijective), ("ZetaNine.CoefficientMapMatrix.actualFMatrix_det_isUnit", `ZetaNine.CoefficientMapMatrix.actualFMatrix_det_isUnit, `IndependentMatrixExpected.expected_actualFMatrix_det_isUnit), ("ZetaNine.CoefficientMapMatrix.actualFMatrix_det_ne_zero", `ZetaNine.CoefficientMapMatrix.actualFMatrix_det_ne_zero, `IndependentMatrixExpected.expected_actualFMatrix_det_ne_zero), ("ZetaNine.CoefficientMapMatrix.inverseMultiplier_coordinates_eq_row_inverse", `ZetaNine.CoefficientMapMatrix.inverseMultiplier_coordinates_eq_row_inverse, `IndependentMatrixExpected.expected_inverseMultiplier_coordinates_eq_row_inverse), ("ZetaNine.CoefficientMapMatrix.inverseMultiplier_eq_coordinatePolynomial_row_inverse", `ZetaNine.CoefficientMapMatrix.inverseMultiplier_eq_coordinatePolynomial_row_inverse, `IndependentMatrixExpected.expected_inverseMultiplier_eq_coordinatePolynomial_row_inverse), ("ZetaNine.CoefficientMapMatrix.selectedIntegerPair_mul_selection", `ZetaNine.CoefficientMapMatrix.selectedIntegerPair_mul_selection, `IndependentMatrixExpected.expected_selectedIntegerPair_mul_selection), ("ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates", `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates, `IndependentMatrixExpected.expected_selectedIntegerMultiplier_coordinates), ("ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates_product", `ZetaNine.CoefficientMapMatrix.checked_selectedIntegerMultiplier_coordinates_product, `IndependentMatrixExpected.expected_selectedIntegerMultiplier_coordinates_product), ("ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_natDegree_le", `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_natDegree_le, `IndependentMatrixExpected.expected_selectedIntegerMultiplier_natDegree_le), ("ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_output", `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_output, `IndependentMatrixExpected.expected_selectedIntegerMultiplier_actual_output), ("ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_five_actual_coordinates", `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_five_actual_coordinates, `IndependentMatrixExpected.expected_selectedIntegerMultiplier_five_actual_coordinates), ("ZetaNine.CoefficientMapMatrix.selected_prescribed_L", `ZetaNine.CoefficientMapMatrix.selected_prescribed_L, `IndependentMatrixExpected.expected_selected_prescribed_L), ("ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_exact_L", `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_exact_L, `IndependentMatrixExpected.expected_selectedIntegerMultiplier_actual_exact_L), ("ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute", `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute, `IndependentMatrixExpected.expected_selectedIntegerMultiplier_actual_HasSum_and_absolute)] do
    let a ← getConstInfo actual
    let b ← getConstInfo expectedName
    let equal ← isDefEq a.type b.type
    unless equal do throwError "Actual staged complete type differs from independent expected: {actual}"
    IO.println (Json.mkObj [("kind",Json.str "actual_whole_type_kernel_comparison"),
      ("label",Json.str label),("actual",Json.str actual.toString),("expected",Json.str expectedName.toString),
      ("type_kernel_equal",toJson equal),("actual_full_type_expression",Json.str (reprStr a.type)),
      ("expected_full_type_expression",Json.str (reprStr b.type))]).compress
