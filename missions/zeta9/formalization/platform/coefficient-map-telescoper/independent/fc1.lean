import Solutions.Sol_ZetaNine_CoefficientMapTelescoper_actual_weightedR_is_difference
import Lean
open Lean Meta
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true
run_meta do
  for name in [`ZetaNine.CoefficientMapAggregate.aggregateLinearMap, `ZetaNine.CoefficientMapAggregate.coordinateLinearMap, `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap] do
    let ci ← getConstInfo name
    let .defnInfo d := ci | throwError "Expected actual staged map"
    let typ ← ppExpr d.type
    let val ← ppExpr d.value
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("type",Json.str typ.pretty),
      ("full_expression_repr",Json.str (reprStr d.value)),("raw_value",Json.str val.pretty),
      ("pp_proofs",toJson true),("axioms",toJson (axs.toList.map Name.toString))]).compress
