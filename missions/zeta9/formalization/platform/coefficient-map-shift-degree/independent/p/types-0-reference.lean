import Theorems.Thm_ZetaNine_CoefficientMapShiftDegree_actual_shift_difference_coefficient
import Lean
open Lean
set_option pp.fullNames true
set_option pp.universes false

run_meta do
  let emit (label : String) (name : Name) : Lean.Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← Lean.Meta.ppExpr ci.type
    let (val, raw) ← match ci with
      | .defnInfo d => pure (some (← Lean.Meta.ppExpr d.value).pretty, some (reprStr d.value))
      | _ => pure (none, none)
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("label",Json.str label),("declaration",Json.str name.toString),
      ("type",Json.str typ.pretty),("type_expression_repr",Json.str (reprStr ci.type)),
      ("value",toJson val),("definition_expression_repr",toJson raw),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  emit "ZetaNine.CoefficientMapShiftDegree.shiftA" `ZetaNine.CoefficientMapShiftDegree.shiftA
  emit "ZetaNine.CoefficientMapShiftDegree.shiftB" `ZetaNine.CoefficientMapShiftDegree.shiftB
  emit "ZetaNine.CoefficientMapShiftDegree.shiftDifference" `ZetaNine.CoefficientMapShiftDegree.shiftDifference
  emit "ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient" `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient
