import missions.zeta9.formalization.CoefficientMapParameterShift
import Lean
open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  for name in [`ZetaNine.CoefficientMapParameterShift.parameterScale, `ZetaNine.CoefficientMapParameterShift.connectionRemainder, `ZetaNine.CoefficientMapParameterShift.positiveProduct_add_two, `ZetaNine.CoefficientMapParameterShift.positiveProduct_parameter_shift, `ZetaNine.CoefficientMapParameterShift.negativeProduct_add_two_sub_one, `ZetaNine.CoefficientMapParameterShift.negativeProduct_parameter_shift, `ZetaNine.CoefficientMapParameterShift.poleProduct_parameter_shift, `ZetaNine.CoefficientMapParameterShift.factorial_parameter_shift, `ZetaNine.CoefficientMapParameterShift.connectionZ_eval_factors, `ZetaNine.CoefficientMapParameterShift.numerator_parameter_shift, `ZetaNine.CoefficientMapParameterShift.connectionD_eval_factors, `ZetaNine.CoefficientMapParameterShift.shifted_regular_conditions, `ZetaNine.CoefficientMapParameterShift.actual_R_parameter_shift, `ZetaNine.CoefficientMapParameterShift.connectionRemainder_successor, `ZetaNine.CoefficientMapParameterShift.connectionRemainder_difference, `ZetaNine.CoefficientMapParameterShift.actual_original_connection_transport, `ZetaNine.CoefficientMapParameterShift.five_actual_connection_transports_exist_unique] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let valueExpr := match ci with
      | .defnInfo d => some d.value
      | _ => none
    let valuePP ← match valueExpr with
      | some value => do pure (Json.str (← ppExpr value).pretty)
      | none => pure Json.null
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),
      ("type_pp_diagnostic",Json.str typ.pretty),
      ("full_definition_value_expression_repr",valueExpr.map (fun x => Json.str (reprStr x)) |>.getD Json.null),
      ("definition_value_pp_diagnostic",valuePP),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
