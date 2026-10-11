import Solutions.Sol_ZetaNine_CoefficientMapConnection_connectionLinearMap_bijective
import Lean
open Lean
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true
run_meta do
  let emit (label : String) (name : Name) : Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let type ← Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo d => pure (some (← Meta.ppExpr d.value).pretty)
      | _ => pure none
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("label",Json.str label),("declaration",Json.str name.toString),
      ("type",Json.str type.pretty),("type_expression_repr",Json.str (reprStr ci.type)),
      ("value",toJson value),("axioms",toJson (axs.toList.map Name.toString))]).compress
  emit "ZetaNine.CoefficientMapConnection.connectionU" `ZetaNine.CoefficientMapConnection.connectionU
  emit "ZetaNine.CoefficientMapConnection.connectionV" `ZetaNine.CoefficientMapConnection.connectionV
  emit "ZetaNine.CoefficientMapConnection.connectionD" `ZetaNine.CoefficientMapConnection.connectionD
  emit "ZetaNine.CoefficientMapConnection.connectionH" `ZetaNine.CoefficientMapConnection.connectionH
  emit "ZetaNine.CoefficientMapConnection.connectionReflection" `ZetaNine.CoefficientMapConnection.connectionReflection
  emit "ZetaNine.CoefficientMapConnection.coefficientPolynomial" `ZetaNine.CoefficientMapConnection.coefficientPolynomial
  emit "ZetaNine.CoefficientMapConnection.inputP" `ZetaNine.CoefficientMapConnection.inputP
  emit "ZetaNine.CoefficientMapConnection.inputQ" `ZetaNine.CoefficientMapConnection.inputQ
  emit "ZetaNine.CoefficientMapConnection.connectionOperator" `ZetaNine.CoefficientMapConnection.connectionOperator
  emit "ZetaNine.CoefficientMapConnection.connectionLinearMap" `ZetaNine.CoefficientMapConnection.connectionLinearMap
  emit "ZetaNine.CoefficientMapConnection.connectionZ" `ZetaNine.CoefficientMapConnection.connectionZ
  emit "ZetaNine.CoefficientMapConnection.connectionTarget" `ZetaNine.CoefficientMapConnection.connectionTarget
  emit "ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective" `solution
