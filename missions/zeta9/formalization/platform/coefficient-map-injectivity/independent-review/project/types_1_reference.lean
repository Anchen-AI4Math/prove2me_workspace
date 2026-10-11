import Theorems.Thm_ZetaNine_CoefficientMapInjectivity_fullLocalCoefficientMap_injective
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
  emit "ZetaNine.CoefficientMapInjectivity.AllLocalCoefficientsZero" `ZetaNine.CoefficientMapInjectivity.AllLocalCoefficientsZero
  emit "ZetaNine.CoefficientMap.actualR" `ZetaNine.CoefficientMap.actualR
  emit "ZetaNine.CoefficientMapJet.localU" `ZetaNine.CoefficientMapJet.localU
  emit "ZetaNine.CoefficientMapJet.shiftedNumerator" `ZetaNine.CoefficientMapJet.shiftedNumerator
  emit "ZetaNine.CoefficientMapJet.clearedSeries" `ZetaNine.CoefficientMapJet.clearedSeries
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator
  emit "ZetaNine.CoefficientMap.poleProduct" `ZetaNine.CoefficientMap.poleProduct
  emit "ZetaNine.CoefficientMapJet.localCoefficient" `ZetaNine.CoefficientMapJet.localCoefficient
  emit "ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap" `ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap
  emit "ZetaNine.CoefficientMapInjectivity.baseU" `ZetaNine.CoefficientMapInjectivity.baseU
  emit "ZetaNine.CoefficientMap.clearedWeightedR" `ZetaNine.CoefficientMap.clearedWeightedR
  emit "ZetaNine.CoefficientMap.clearedPoleProduct" `ZetaNine.CoefficientMap.clearedPoleProduct
  emit "ZetaNine.CoefficientMapJet.integerLocalU" `ZetaNine.CoefficientMapJet.integerLocalU
  emit "ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient" `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient
  emit "ZetaNine.CoefficientMapInjectivity.baseNumerator" `ZetaNine.CoefficientMapInjectivity.baseNumerator
  emit "ZetaNine.CoefficientMapJet.weightedLocalCoefficient" `ZetaNine.CoefficientMapJet.weightedLocalCoefficient
  emit "ZetaNine.CoefficientMap.weightedR" `ZetaNine.CoefficientMap.weightedR
  emit "ZetaNine.CoefficientMapInjectivity.ProperMultiplier" `ZetaNine.CoefficientMapInjectivity.ProperMultiplier
  emit "ZetaNine.CoefficientMapJet.weightedClearedSeries" `ZetaNine.CoefficientMapJet.weightedClearedSeries
  emit "ZetaNine.CoefficientMap.leadingPoleCoefficient" `ZetaNine.CoefficientMap.leadingPoleCoefficient
  emit "ZetaNine.CoefficientMap.clearedR" `ZetaNine.CoefficientMap.clearedR
  emit "ZetaNine.CoefficientMap.numerator" `ZetaNine.CoefficientMap.numerator
  emit "ZetaNine.CoefficientMapInjectivity.polePolynomial" `ZetaNine.CoefficientMapInjectivity.polePolynomial
  emit "ZetaNine.CoefficientMapJet.shiftedVariable" `ZetaNine.CoefficientMapJet.shiftedVariable
  emit "ZetaNine.CoefficientMapInjectivity.weightedNumerator" `ZetaNine.CoefficientMapInjectivity.weightedNumerator
  emit "ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap_injective" `ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap_injective
