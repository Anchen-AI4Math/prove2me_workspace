import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean

open Lean Meta
run_meta do
  let names := (← getEnv).constants.toList.filterMap fun (name, ci) =>
    if name.getPrefix == `ZetaNine.CoefficientMapFormalTransportNumerators ||
        name.toString.endsWith "ZetaNine.CoefficientMapFormalTransportNumerators.three_denominator_combination" then
      match ci with | .thmInfo _ => some name | _ => none
    else none
  unless names.length == 15 do throwError "Expected all fifteen actual source theorems"
  for name in names do
    let ci ← getConstInfo name
    let axioms ← collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("full_type_expression_repr", Json.str (reprStr ci.type)),
      ("axioms", toJson (axioms.toList.map Name.toString))]).compress
