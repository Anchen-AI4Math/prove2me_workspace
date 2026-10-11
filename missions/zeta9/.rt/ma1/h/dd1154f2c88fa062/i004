import missions.zeta9.formalization.CoefficientMapMatrix
import Lean
open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  for name in [`ZetaNine.CoefficientMapMatrix.actualFMatrix, `ZetaNine.CoefficientMapMatrix.quarticAggregate_eq_row_vector, `ZetaNine.CoefficientMapMatrix.coordinatePolynomial_single_one, `ZetaNine.CoefficientMapMatrix.column_action_matrix_is_transpose, `ZetaNine.CoefficientMapMatrix.actualFMatrix_row_action_bijective, `ZetaNine.CoefficientMapMatrix.actualFMatrix_det_isUnit, `ZetaNine.CoefficientMapMatrix.actualFMatrix_det_ne_zero, `ZetaNine.CoefficientMapMatrix.inverseMultiplier_coordinates_eq_row_inverse, `ZetaNine.CoefficientMapMatrix.inverseMultiplier_eq_coordinatePolynomial_row_inverse, `ZetaNine.CoefficientMapMatrix.selectionMatrix, `ZetaNine.CoefficientMapMatrix.selectedIntegerPair, `ZetaNine.CoefficientMapMatrix.selectedIntegerOutput, `ZetaNine.CoefficientMapMatrix.selectedIntegerPair_mul_selection, `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier, `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates, `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates_product, `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_natDegree_le, `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_output, `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_five_actual_coordinates, `ZetaNine.CoefficientMapMatrix.selected_prescribed_L, `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_exact_L, `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← collectAxioms name
    let value := match ci with | .defnInfo d => some d.value | _ => none
    let kind := match ci with | .defnInfo _ => "def" | .thmInfo _ => "theorem" | _ => "other"
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("kind",Json.str kind),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),("type_pp_diagnostic",Json.str typ.pretty),
      ("full_definition_value_expression_repr",value.map (fun x => Json.str (reprStr x)) |>.getD Json.null),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
