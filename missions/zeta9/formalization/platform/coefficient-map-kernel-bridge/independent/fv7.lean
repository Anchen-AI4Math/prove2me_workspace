import Theorems.Thm_ZetaNine_CoefficientMapKernelBridge_inverseMultiplier_actual_HasSum_and_absolute
-- Independent runtime audit helper; prepared but never compiled in this batch.
-- The caller supplies imports and constant lists from frozen inputs plus actual
-- official graph/parser facts. PP is diagnostic, never the kernel equality gate.
import Lean
open Lean Meta
set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true

private def emitIndependentDefinition (name : Name) : MetaM Unit := do
  let .defnInfo d ← getConstInfo name | throwError "Expected an actual definition: {name}"
  let typ ← ppExpr d.type
  let val ← ppExpr d.value
  let axs ← Lean.collectAxioms name
  IO.println (Json.mkObj [("kind",Json.str "definition_full_expression"),
    ("declaration",Json.str name.toString),
    ("level_parameters",toJson (d.levelParams.map Name.toString)),
    ("type_expression_repr",Json.str (reprStr d.type)),
    ("full_value_expression_repr",Json.str (reprStr d.value)),
    ("type_pp_diagnostic",Json.str typ.pretty),
    ("value_pp_with_proofs_diagnostic",Json.str val.pretty),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

private def checkIndependentNativeAlias (name aliasName : Name) : MetaM Unit := do
  let .defnInfo d ← getConstInfo name | throwError "Expected native definition"
  let .defnInfo a ← getConstInfo aliasName | throwError "Expected actual staged-byte alias definition"
  let typeEq ← isDefEq d.type a.type
  let fullValueEq ← isDefEq d.value a.value
  unless typeEq && fullValueEq do
    throwError "Whole definition kernel equality failed: {name} / {aliasName}"
  let axs ← Lean.collectAxioms aliasName
  IO.println (Json.mkObj [("kind",Json.str "native_alias_whole_value_kernel"),
    ("declaration",Json.str name.toString),("alias_declaration",Json.str aliasName.toString),
    ("type_kernel_equal",toJson typeEq),("full_value_kernel_equal",toJson fullValueEq),
    ("original_type_expression_repr",Json.str (reprStr d.type)),
    ("alias_type_expression_repr",Json.str (reprStr a.type)),
    ("original_full_value_expression_repr",Json.str (reprStr d.value)),
    ("alias_full_value_expression_repr",Json.str (reprStr a.value)),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

private def emitIndependentProof (name : Name) : MetaM Unit := do
  let ci ← getConstInfo name
  let typ ← ppExpr ci.type
  let axs ← Lean.collectAxioms name
  IO.println (Json.mkObj [("kind",Json.str "proof_full_type"),
    ("declaration",Json.str name.toString),
    ("full_type_expression_repr",Json.str (reprStr ci.type)),
    ("type_pp_diagnostic",Json.str typ.pretty),
    ("axioms",toJson (axs.toList.map Name.toString))]).compress

-- No run_meta block: no guessed declarations or silent claims of execution.

run_meta do
  for name in [`ZetaNine.CoefficientMapInjectivity.AllLocalCoefficientsZero, `ZetaNine.CoefficientMapAggregate.coordinatePolynomial, `ZetaNine.CoefficientMapPartialFractions.partialBlock, `ZetaNine.CoefficientMap.actualR, `ZetaNine.CoefficientMapJet.localU, `ZetaNine.CoefficientMapKernelBridge.prescribedL, `ZetaNine.CoefficientMapJet.shiftedNumerator, `ZetaNine.CoefficientMapKernelBridge.inverseMultiplier, `ZetaNine.CoefficientMapJet.clearedSeries, `ZetaNine.CoefficientMapJet.shiftedClearedDenominator, `ZetaNine.CoefficientMap.poleProduct, `ZetaNine.CoefficientMapJet.localCoefficient, `ZetaNine.CoefficientMapAggregate.polynomialCoordinates, `ZetaNine.CoefficientMapFiniteSum.shiftedTail, `ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap, `ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient, `ZetaNine.CoefficientMapInjectivity.baseU, `ZetaNine.CoefficientMapShiftDegree.shiftB, `ZetaNine.CoefficientMapFiniteSum.finiteL, `ZetaNine.CoefficientMap.clearedWeightedR, `ZetaNine.CoefficientMap.clearedPoleProduct, `ZetaNine.CoefficientMapFiniteSum.rho, `ZetaNine.CoefficientMapAggregate.aggregate, `ZetaNine.CoefficientMapAggregate.aggregateLinearMap, `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial, `ZetaNine.CoefficientMapPartialFractions.localTruncation, `ZetaNine.CoefficientMapJet.integerLocalU, `ZetaNine.CoefficientMapSummation.zetaReal, `ZetaNine.CoefficientMapKernelBridge.negativeProduct, `ZetaNine.CoefficientMapReflection.partialBasis, `ZetaNine.CoefficientMapFiniteSum.constantTerm, `ZetaNine.CoefficientMapTelescoper.telescoperNumerator, `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient, `ZetaNine.CoefficientMapTelescoper.prefixSum, `ZetaNine.CoefficientMapTelescoper.rootPolynomial, `ZetaNine.CoefficientMapKernelBridge.positiveProduct, `ZetaNine.CoefficientMapReflection.StrongProperMultiplier, `ZetaNine.CoefficientMapPartialFractions.partialNumerator, `ZetaNine.CoefficientMapInjectivity.baseNumerator, `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap, `ZetaNine.CoefficientMapJet.weightedLocalCoefficient, `ZetaNine.CoefficientMapKernelBridge.aValue, `ZetaNine.CoefficientMap.weightedR, `ZetaNine.CoefficientMapSummation.actualSeries, `ZetaNine.CoefficientMapSummation.exactL, `ZetaNine.CoefficientMapInjectivity.ProperMultiplier, `ZetaNine.HarmonicStability.logDen, `ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries, `ZetaNine.CoefficientMapReflection.rho, `ZetaNine.CoefficientMapReflection.reflectionVariable, `ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv, `ZetaNine.CoefficientMapJet.weightedClearedSeries, `ZetaNine.CoefficientMap.leadingPoleCoefficient, `ZetaNine.CoefficientMap.clearedR, `ZetaNine.CoefficientMap.numerator, `ZetaNine.HarmonicStability.harmonicPower, `ZetaNine.CoefficientMapInjectivity.polePolynomial, `ZetaNine.CoefficientMapShiftDegree.shiftA, `ZetaNine.CoefficientMapJet.shiftedVariable, `ZetaNine.CoefficientMapTelescoper.telescoper, `ZetaNine.CoefficientMapKernelBridge.bValue, `ZetaNine.CoefficientMapAggregate.coordinateLinearMap, `ZetaNine.CoefficientMapShiftDegree.shiftDifference, `ZetaNine.CoefficientMapInjectivity.weightedNumerator, `ZetaNine.CoefficientMapTelescoper.rootNode] do
    emitIndependentDefinition name
