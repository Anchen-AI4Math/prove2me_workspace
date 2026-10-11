import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
open Lean Meta
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let specs : List (String × String) := [("ZetaNine.CoefficientMapFormalTransportNumerators.positiveProduct_remainder_cancellation", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.remainderNumerator_eval", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.remainderNumerator_actual_cancellation", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_as_actual_numerator", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_successor_eval", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_successor_shift_eval", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_add_two_shift_eval", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_successor_shift", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_add_two_shift", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_shifted_as_actual_numerator", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_eval_two", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_connection_transport_positive", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.three_denominator_combination", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_cleared_numerator_transport_eval", "theorem"),
    ("ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_cleared_numerator_transport", "theorem")]
  let env ← getEnv
  let constants := env.constants.toList
  for (wanted, sourceKind) in specs do
    let found := constants.filter fun (name, _) =>
      name.toString == wanted || name.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Exact source declaration resolution failed {wanted}"
    let (name, ci) := found.head!
    let actualKind := match ci with
      | .defnInfo _ => "definition"
      | .thmInfo _ => "proof"
      | _ => "other"
    let expectedKind := if sourceKind == "def" || sourceKind == "abbrev" then "definition" else "proof"
    unless actualKind == expectedKind do throwError "Source declaration kind mismatch {name}"
    let axioms ← collectAxioms name
    unless axioms.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard source axiom {name}"
    let typePP ← ppExpr ci.type
    let value := ci.value? (allowOpaque := true)
    IO.println (Json.mkObj [("kind",Json.str "actual_source_declaration"),
      ("source_kind",Json.str sourceKind),("source_name",Json.str wanted),
      ("actual_name",Json.str name.toString),("full_type_expr",Json.str (reprStr ci.type)),
      ("full_value_expr",Json.str (reprStr value)),("full_type_pp_diagnostic",Json.str typePP.pretty),
      ("axioms",toJson (axioms.toList.map Name.toString))]).compress
