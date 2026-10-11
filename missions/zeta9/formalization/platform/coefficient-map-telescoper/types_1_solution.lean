import Solutions.Sol_ZetaNine_CoefficientMapTelescoper_telescoper_actual_rational_representation
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
  emit "ZetaNine.CoefficientMapAggregate.coordinatePolynomial" `ZetaNine.CoefficientMapAggregate.coordinatePolynomial
  emit "ZetaNine.CoefficientMapPartialFractions.partialBlock" `ZetaNine.CoefficientMapPartialFractions.partialBlock
  emit "ZetaNine.CoefficientMap.actualR" `ZetaNine.CoefficientMap.actualR
  emit "ZetaNine.CoefficientMapJet.localU" `ZetaNine.CoefficientMapJet.localU
  emit "ZetaNine.CoefficientMapJet.shiftedNumerator" `ZetaNine.CoefficientMapJet.shiftedNumerator
  emit "ZetaNine.CoefficientMapJet.clearedSeries" `ZetaNine.CoefficientMapJet.clearedSeries
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator
  emit "ZetaNine.CoefficientMap.poleProduct" `ZetaNine.CoefficientMap.poleProduct
  emit "ZetaNine.CoefficientMapJet.localCoefficient" `ZetaNine.CoefficientMapJet.localCoefficient
  emit "ZetaNine.CoefficientMapAggregate.polynomialCoordinates" `ZetaNine.CoefficientMapAggregate.polynomialCoordinates
  emit "ZetaNine.CoefficientMapFiniteSum.shiftedTail" `ZetaNine.CoefficientMapFiniteSum.shiftedTail
  emit "ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap" `ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap
  emit "ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient" `ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient
  emit "ZetaNine.CoefficientMapInjectivity.baseU" `ZetaNine.CoefficientMapInjectivity.baseU
  emit "ZetaNine.CoefficientMapFiniteSum.finiteL" `ZetaNine.CoefficientMapFiniteSum.finiteL
  emit "ZetaNine.CoefficientMap.clearedWeightedR" `ZetaNine.CoefficientMap.clearedWeightedR
  emit "ZetaNine.CoefficientMap.clearedPoleProduct" `ZetaNine.CoefficientMap.clearedPoleProduct
  emit "ZetaNine.CoefficientMapFiniteSum.rho" `ZetaNine.CoefficientMapFiniteSum.rho
  emit "ZetaNine.CoefficientMapAggregate.aggregate" `ZetaNine.CoefficientMapAggregate.aggregate
  emit "ZetaNine.CoefficientMapAggregate.aggregateLinearMap" `ZetaNine.CoefficientMapAggregate.aggregateLinearMap
  emit "ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial" `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial
  emit "ZetaNine.CoefficientMapPartialFractions.localTruncation" `ZetaNine.CoefficientMapPartialFractions.localTruncation
  emit "ZetaNine.CoefficientMapJet.integerLocalU" `ZetaNine.CoefficientMapJet.integerLocalU
  emit "ZetaNine.CoefficientMapSummation.zetaReal" `ZetaNine.CoefficientMapSummation.zetaReal
  emit "ZetaNine.CoefficientMapReflection.partialBasis" `ZetaNine.CoefficientMapReflection.partialBasis
  emit "ZetaNine.CoefficientMapFiniteSum.constantTerm" `ZetaNine.CoefficientMapFiniteSum.constantTerm
  emit "ZetaNine.CoefficientMapTelescoper.telescoperNumerator" `ZetaNine.CoefficientMapTelescoper.telescoperNumerator
  emit "ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient" `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient
  emit "ZetaNine.CoefficientMapTelescoper.prefixSum" `ZetaNine.CoefficientMapTelescoper.prefixSum
  emit "ZetaNine.CoefficientMapTelescoper.rootPolynomial" `ZetaNine.CoefficientMapTelescoper.rootPolynomial
  emit "ZetaNine.CoefficientMapReflection.StrongProperMultiplier" `ZetaNine.CoefficientMapReflection.StrongProperMultiplier
  emit "ZetaNine.CoefficientMapPartialFractions.partialNumerator" `ZetaNine.CoefficientMapPartialFractions.partialNumerator
  emit "ZetaNine.CoefficientMapInjectivity.baseNumerator" `ZetaNine.CoefficientMapInjectivity.baseNumerator
  emit "ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap" `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap
  emit "ZetaNine.CoefficientMapJet.weightedLocalCoefficient" `ZetaNine.CoefficientMapJet.weightedLocalCoefficient
  emit "ZetaNine.CoefficientMap.weightedR" `ZetaNine.CoefficientMap.weightedR
  emit "ZetaNine.CoefficientMapSummation.actualSeries" `ZetaNine.CoefficientMapSummation.actualSeries
  emit "ZetaNine.CoefficientMapSummation.exactL" `ZetaNine.CoefficientMapSummation.exactL
  emit "ZetaNine.CoefficientMapInjectivity.ProperMultiplier" `ZetaNine.CoefficientMapInjectivity.ProperMultiplier
  emit "ZetaNine.HarmonicStability.logDen" `ZetaNine.HarmonicStability.logDen
  emit "ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries" `ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries
  emit "ZetaNine.CoefficientMapReflection.rho" `ZetaNine.CoefficientMapReflection.rho
  emit "ZetaNine.CoefficientMapReflection.reflectionVariable" `ZetaNine.CoefficientMapReflection.reflectionVariable
  emit "ZetaNine.CoefficientMapJet.weightedClearedSeries" `ZetaNine.CoefficientMapJet.weightedClearedSeries
  emit "ZetaNine.CoefficientMap.leadingPoleCoefficient" `ZetaNine.CoefficientMap.leadingPoleCoefficient
  emit "ZetaNine.CoefficientMap.clearedR" `ZetaNine.CoefficientMap.clearedR
  emit "ZetaNine.CoefficientMap.numerator" `ZetaNine.CoefficientMap.numerator
  emit "ZetaNine.HarmonicStability.harmonicPower" `ZetaNine.HarmonicStability.harmonicPower
  emit "ZetaNine.CoefficientMapInjectivity.polePolynomial" `ZetaNine.CoefficientMapInjectivity.polePolynomial
  emit "ZetaNine.CoefficientMapJet.shiftedVariable" `ZetaNine.CoefficientMapJet.shiftedVariable
  emit "ZetaNine.CoefficientMapTelescoper.telescoper" `ZetaNine.CoefficientMapTelescoper.telescoper
  emit "ZetaNine.CoefficientMapAggregate.coordinateLinearMap" `ZetaNine.CoefficientMapAggregate.coordinateLinearMap
  emit "ZetaNine.CoefficientMapInjectivity.weightedNumerator" `ZetaNine.CoefficientMapInjectivity.weightedNumerator
  emit "ZetaNine.CoefficientMapTelescoper.rootNode" `ZetaNine.CoefficientMapTelescoper.rootNode
  emit "ZetaNine.CoefficientMapTelescoper.telescoper_actual_rational_representation" `solution
