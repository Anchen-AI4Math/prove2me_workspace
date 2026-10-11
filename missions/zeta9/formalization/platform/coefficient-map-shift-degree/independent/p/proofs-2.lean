import Solutions.Sol_ZetaNine_CoefficientMapShiftDegree_actual_shift_difference_small_degree_implies_zero
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
  emit "ZetaNine.CoefficientMapShiftDegree.actual_nextCoeff_mul" `ZetaNine.CoefficientMapShiftDegree.actual_nextCoeff_mul
  emit "ZetaNine.CoefficientMapShiftDegree.actual_shift_nextCoeff" `ZetaNine.CoefficientMapShiftDegree.actual_shift_nextCoeff
  emit "ZetaNine.CoefficientMapShiftDegree.shiftA_monic" `ZetaNine.CoefficientMapShiftDegree.shiftA_monic
  emit "ZetaNine.CoefficientMapShiftDegree.shiftB_monic" `ZetaNine.CoefficientMapShiftDegree.shiftB_monic
  emit "ZetaNine.CoefficientMapShiftDegree.shiftA_natDegree" `ZetaNine.CoefficientMapShiftDegree.shiftA_natDegree
  emit "ZetaNine.CoefficientMapShiftDegree.shiftB_natDegree" `ZetaNine.CoefficientMapShiftDegree.shiftB_natDegree
  emit "ZetaNine.CoefficientMapShiftDegree.shiftA_nextCoeff" `ZetaNine.CoefficientMapShiftDegree.shiftA_nextCoeff
  emit "ZetaNine.CoefficientMapShiftDegree.shiftB_nextCoeff" `ZetaNine.CoefficientMapShiftDegree.shiftB_nextCoeff
  emit "ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient" `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient
  emit "ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient_ne_zero" `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient_ne_zero
  emit "ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_degree_lower_bound" `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_degree_lower_bound
  emit "ZetaNine.CoefficientMapShiftDegree.checked_actual_shift_difference_small_degree_implies_zero" `ZetaNine.CoefficientMapShiftDegree.checked_actual_shift_difference_small_degree_implies_zero
  emit "solution" `solution
