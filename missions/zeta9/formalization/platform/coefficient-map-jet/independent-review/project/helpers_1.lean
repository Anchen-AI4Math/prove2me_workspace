import Solutions.Sol_ZetaNine_CoefficientMapJet_coefficient_convolution_explicit
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
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero
  emit "ZetaNine.CoefficientMapJet.coefficient_convolution" `ZetaNine.CoefficientMapJet.coefficient_convolution
  emit "ZetaNine.CoefficientMapJet.integer_coefficient_convolution" `ZetaNine.CoefficientMapJet.integer_coefficient_convolution
  emit "ZetaNine.CoefficientMapJet.clearedSeries_constant" `ZetaNine.CoefficientMapJet.clearedSeries_constant
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval
  emit "ZetaNine.CoefficientMapJet.clearedSeries_unique" `ZetaNine.CoefficientMapJet.clearedSeries_unique
  emit "ZetaNine.CoefficientMapJet.actual_weighted_local_rational_expression" `ZetaNine.CoefficientMapJet.actual_weighted_local_rational_expression
  emit "ZetaNine.CoefficientMapJet.weightedClearedSeries_denominator_identity" `ZetaNine.CoefficientMapJet.weightedClearedSeries_denominator_identity
  emit "ZetaNine.CoefficientMapJet.localCoefficient_nine" `ZetaNine.CoefficientMapJet.localCoefficient_nine
  emit "ZetaNine.CoefficientMapJet.integerLocalU_map" `ZetaNine.CoefficientMapJet.integerLocalU_map
  emit "ZetaNine.CoefficientMapJet.actual_local_rational_expression" `ZetaNine.CoefficientMapJet.actual_local_rational_expression
  emit "ZetaNine.CoefficientMapJet.localU_eq" `ZetaNine.CoefficientMapJet.localU_eq
  emit "ZetaNine.CoefficientMapJet.weightedLocalCoefficient_nine" `ZetaNine.CoefficientMapJet.weightedLocalCoefficient_nine
  emit "ZetaNine.CoefficientMapJet.clearedSeries_denominator_identity" `ZetaNine.CoefficientMapJet.clearedSeries_denominator_identity
  emit "ZetaNine.CoefficientMapJet.shiftedNumerator_eval" `ZetaNine.CoefficientMapJet.shiftedNumerator_eval
  emit "ZetaNine.CoefficientMapJet.shiftedVariable_eval" `ZetaNine.CoefficientMapJet.shiftedVariable_eval
  emit "ZetaNine.CoefficientMapJet.localU_eval" `ZetaNine.CoefficientMapJet.localU_eval
  emit "ZetaNine.CoefficientMapJet.checked_coefficient_convolution_explicit" `ZetaNine.CoefficientMapJet.checked_coefficient_convolution_explicit
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant
  emit "ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero" `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero
  emit "solution" `solution
