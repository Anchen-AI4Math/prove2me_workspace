import Solutions.Sol_ZetaNine_CoefficientMapShiftDegree_actual_shift_difference_coefficient
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
  emit "ZetaNine.CoefficientMapShiftDegree.actual_nextCoeff_mul" `ZetaNine.CoefficientMapShiftDegree.actual_nextCoeff_mul
  emit "ZetaNine.CoefficientMapShiftDegree.shiftA_natDegree" `ZetaNine.CoefficientMapShiftDegree.shiftA_natDegree
  emit "ZetaNine.CoefficientMapShiftDegree.shiftB_nextCoeff" `ZetaNine.CoefficientMapShiftDegree.shiftB_nextCoeff
  emit "ZetaNine.CoefficientMapShiftDegree.shiftA_monic" `ZetaNine.CoefficientMapShiftDegree.shiftA_monic
  emit "ZetaNine.CoefficientMapShiftDegree.shiftB_natDegree" `ZetaNine.CoefficientMapShiftDegree.shiftB_natDegree
  emit "ZetaNine.CoefficientMapShiftDegree.shiftB_monic" `ZetaNine.CoefficientMapShiftDegree.shiftB_monic
  emit "ZetaNine.CoefficientMapShiftDegree.actual_shift_nextCoeff" `ZetaNine.CoefficientMapShiftDegree.actual_shift_nextCoeff
  emit "ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_degree_lower_bound" `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_degree_lower_bound
  emit "ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_small_degree_implies_zero" `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_small_degree_implies_zero
  emit "ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient_ne_zero" `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient_ne_zero
  emit "ZetaNine.CoefficientMapShiftDegree.shiftA_nextCoeff" `ZetaNine.CoefficientMapShiftDegree.shiftA_nextCoeff
  emit "ZetaNine.CoefficientMapShiftDegree.checked_actual_shift_difference_coefficient" `ZetaNine.CoefficientMapShiftDegree.checked_actual_shift_difference_coefficient
  emit "solution" `solution
