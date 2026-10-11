import Theorems.Thm_ZetaNine_CoefficientMapShiftDegree_actual_shift_difference_coefficient
import Lean
open Lean
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  let emit (label : String) (name : Name) : Lean.Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← Lean.Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo d => pure (some (← Lean.Meta.ppExpr d.value).pretty)
      | _ => pure none
    let axioms ← Lean.collectAxioms name
    IO.println (Json.mkObj [("label", Json.str label), ("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("value", toJson value), ("axioms", toJson (axioms.toList.map Name.toString))]).compress
  emit "ZetaNine.CoefficientMapShiftDegree.shiftB" `ZetaNine.CoefficientMapShiftDegree.shiftB
  emit "ZetaNine.CoefficientMapShiftDegree.shiftA" `ZetaNine.CoefficientMapShiftDegree.shiftA
  emit "ZetaNine.CoefficientMapShiftDegree.shiftDifference" `ZetaNine.CoefficientMapShiftDegree.shiftDifference
  emit "ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient" `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient
