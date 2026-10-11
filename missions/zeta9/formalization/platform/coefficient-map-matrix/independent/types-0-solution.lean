import Solutions.Sol_ZetaNine_CoefficientMapMatrix_actualFMatrix_det_ne_zero
import Lean
open Lean
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true
run_meta do
  let emit (label : String) (name : Name) : Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo d => pure (some (← Meta.ppExpr d.value).pretty)
      | _ => pure none
    let fullvalue := match ci with | .defnInfo d => some (reprStr d.value) | _ => none
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("label",Json.str label),("declaration",Json.str name.toString),
      ("type",Json.str typ.pretty),("type_expression_repr",Json.str (reprStr ci.type)),
      ("value",toJson value),("value_expression_repr",toJson fullvalue),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  emit "ZetaNine.HarmonicStability.logDen" `ZetaNine.HarmonicStability.logDen
  emit "ZetaNine.HarmonicStability.harmonicPower" `ZetaNine.HarmonicStability.harmonicPower
  emit "ZetaNine.CoefficientMap.numerator" `ZetaNine.CoefficientMap.numerator
  emit "ZetaNine.CoefficientMap.poleProduct" `ZetaNine.CoefficientMap.poleProduct
  emit "ZetaNine.CoefficientMap.actualR" `ZetaNine.CoefficientMap.actualR
  emit "ZetaNine.CoefficientMap.clearedPoleProduct" `ZetaNine.CoefficientMap.clearedPoleProduct
  emit "ZetaNine.CoefficientMap.clearedR" `ZetaNine.CoefficientMap.clearedR
  emit "ZetaNine.CoefficientMap.leadingPoleCoefficient" `ZetaNine.CoefficientMap.leadingPoleCoefficient
  emit "ZetaNine.CoefficientMap.weightedR" `ZetaNine.CoefficientMap.weightedR
  emit "ZetaNine.CoefficientMap.clearedWeightedR" `ZetaNine.CoefficientMap.clearedWeightedR
  emit "ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient" `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient
  emit "ZetaNine.CoefficientMapAggregate.aggregate" `ZetaNine.CoefficientMapAggregate.aggregate
  emit "ZetaNine.CoefficientMapAggregate.coordinatePolynomial" `ZetaNine.CoefficientMapAggregate.coordinatePolynomial
  emit "ZetaNine.CoefficientMapAggregate.polynomialCoordinates" `ZetaNine.CoefficientMapAggregate.polynomialCoordinates
  emit "ZetaNine.CoefficientMapAggregate.aggregateLinearMap" `ZetaNine.CoefficientMapAggregate.aggregateLinearMap
  emit "ZetaNine.CoefficientMapAggregate.coordinateLinearMap" `ZetaNine.CoefficientMapAggregate.coordinateLinearMap
  emit "ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap" `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap
  emit "ZetaNine.CoefficientMapFiniteSum.rho" `ZetaNine.CoefficientMapFiniteSum.rho
  emit "ZetaNine.CoefficientMapFiniteSum.constantTerm" `ZetaNine.CoefficientMapFiniteSum.constantTerm
  emit "ZetaNine.CoefficientMapFiniteSum.finiteL" `ZetaNine.CoefficientMapFiniteSum.finiteL
  emit "ZetaNine.CoefficientMapFiniteSum.shiftedTail" `ZetaNine.CoefficientMapFiniteSum.shiftedTail
  emit "ZetaNine.CoefficientMapInjectivity.baseNumerator" `ZetaNine.CoefficientMapInjectivity.baseNumerator
  emit "ZetaNine.CoefficientMapInjectivity.baseU" `ZetaNine.CoefficientMapInjectivity.baseU
  emit "ZetaNine.CoefficientMapInjectivity.weightedNumerator" `ZetaNine.CoefficientMapInjectivity.weightedNumerator
  emit "ZetaNine.CoefficientMapInjectivity.polePolynomial" `ZetaNine.CoefficientMapInjectivity.polePolynomial
  emit "ZetaNine.CoefficientMapInjectivity.AllLocalCoefficientsZero" `ZetaNine.CoefficientMapInjectivity.AllLocalCoefficientsZero
  emit "ZetaNine.CoefficientMapInjectivity.ProperMultiplier" `ZetaNine.CoefficientMapInjectivity.ProperMultiplier
  emit "ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap" `ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap
  emit "ZetaNine.CoefficientMapJet.shiftedVariable" `ZetaNine.CoefficientMapJet.shiftedVariable
  emit "ZetaNine.CoefficientMapJet.shiftedNumerator" `ZetaNine.CoefficientMapJet.shiftedNumerator
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator
  emit "ZetaNine.CoefficientMapJet.localU" `ZetaNine.CoefficientMapJet.localU
  emit "ZetaNine.CoefficientMapJet.integerLocalU" `ZetaNine.CoefficientMapJet.integerLocalU
  emit "ZetaNine.CoefficientMapJet.clearedSeries" `ZetaNine.CoefficientMapJet.clearedSeries
  emit "ZetaNine.CoefficientMapJet.weightedClearedSeries" `ZetaNine.CoefficientMapJet.weightedClearedSeries
  emit "ZetaNine.CoefficientMapJet.localCoefficient" `ZetaNine.CoefficientMapJet.localCoefficient
  emit "ZetaNine.CoefficientMapJet.weightedLocalCoefficient" `ZetaNine.CoefficientMapJet.weightedLocalCoefficient
  emit "ZetaNine.CoefficientMapKernelBridge.positiveProduct" `ZetaNine.CoefficientMapKernelBridge.positiveProduct
  emit "ZetaNine.CoefficientMapKernelBridge.negativeProduct" `ZetaNine.CoefficientMapKernelBridge.negativeProduct
  emit "ZetaNine.CoefficientMapKernelBridge.aValue" `ZetaNine.CoefficientMapKernelBridge.aValue
  emit "ZetaNine.CoefficientMapKernelBridge.bValue" `ZetaNine.CoefficientMapKernelBridge.bValue
  emit "ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv" `ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv
  emit "ZetaNine.CoefficientMapKernelBridge.inverseMultiplier" `ZetaNine.CoefficientMapKernelBridge.inverseMultiplier
  emit "ZetaNine.CoefficientMapKernelBridge.prescribedL" `ZetaNine.CoefficientMapKernelBridge.prescribedL
  emit "ZetaNine.CoefficientMapMatrix.actualFMatrix" `ZetaNine.CoefficientMapMatrix.actualFMatrix
  emit "ZetaNine.CoefficientMapMatrix.selectionMatrix" `ZetaNine.CoefficientMapMatrix.selectionMatrix
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerPair" `ZetaNine.CoefficientMapMatrix.selectedIntegerPair
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerOutput" `ZetaNine.CoefficientMapMatrix.selectedIntegerOutput
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier" `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier
  emit "ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial" `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial
  emit "ZetaNine.CoefficientMapPartialFractions.localTruncation" `ZetaNine.CoefficientMapPartialFractions.localTruncation
  emit "ZetaNine.CoefficientMapPartialFractions.partialBlock" `ZetaNine.CoefficientMapPartialFractions.partialBlock
  emit "ZetaNine.CoefficientMapPartialFractions.partialNumerator" `ZetaNine.CoefficientMapPartialFractions.partialNumerator
  emit "ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries" `ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries
  emit "ZetaNine.CoefficientMapReflection.reflectionVariable" `ZetaNine.CoefficientMapReflection.reflectionVariable
  emit "ZetaNine.CoefficientMapReflection.rho" `ZetaNine.CoefficientMapReflection.rho
  emit "ZetaNine.CoefficientMapReflection.StrongProperMultiplier" `ZetaNine.CoefficientMapReflection.StrongProperMultiplier
  emit "ZetaNine.CoefficientMapReflection.partialBasis" `ZetaNine.CoefficientMapReflection.partialBasis
  emit "ZetaNine.CoefficientMapShiftDegree.shiftA" `ZetaNine.CoefficientMapShiftDegree.shiftA
  emit "ZetaNine.CoefficientMapShiftDegree.shiftB" `ZetaNine.CoefficientMapShiftDegree.shiftB
  emit "ZetaNine.CoefficientMapShiftDegree.shiftDifference" `ZetaNine.CoefficientMapShiftDegree.shiftDifference
  emit "ZetaNine.CoefficientMapSummation.zetaReal" `ZetaNine.CoefficientMapSummation.zetaReal
  emit "ZetaNine.CoefficientMapSummation.exactL" `ZetaNine.CoefficientMapSummation.exactL
  emit "ZetaNine.CoefficientMapSummation.actualSeries" `ZetaNine.CoefficientMapSummation.actualSeries
  emit "ZetaNine.CoefficientMapTelescoper.prefixSum" `ZetaNine.CoefficientMapTelescoper.prefixSum
  emit "ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient" `ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient
  emit "ZetaNine.CoefficientMapTelescoper.telescoper" `ZetaNine.CoefficientMapTelescoper.telescoper
  emit "ZetaNine.CoefficientMapTelescoper.telescoperNumerator" `ZetaNine.CoefficientMapTelescoper.telescoperNumerator
  emit "ZetaNine.CoefficientMapTelescoper.rootNode" `ZetaNine.CoefficientMapTelescoper.rootNode
  emit "ZetaNine.CoefficientMapTelescoper.rootPolynomial" `ZetaNine.CoefficientMapTelescoper.rootPolynomial
  emit "ZetaNine.CoefficientMapMatrix.quarticAggregate_eq_row_vector" `ZetaNine.CoefficientMapMatrix.quarticAggregate_eq_row_vector
  emit "ZetaNine.CoefficientMapMatrix.coordinatePolynomial_single_one" `ZetaNine.CoefficientMapMatrix.coordinatePolynomial_single_one
  emit "ZetaNine.CoefficientMapMatrix.column_action_matrix_is_transpose" `ZetaNine.CoefficientMapMatrix.column_action_matrix_is_transpose
  emit "ZetaNine.CoefficientMapMatrix.actualFMatrix_row_action_bijective" `ZetaNine.CoefficientMapMatrix.actualFMatrix_row_action_bijective
  emit "ZetaNine.CoefficientMapMatrix.actualFMatrix_det_isUnit" `ZetaNine.CoefficientMapMatrix.actualFMatrix_det_isUnit
  emit "ZetaNine.CoefficientMapMatrix.actualFMatrix_det_ne_zero" `ZetaNine.CoefficientMapMatrix.checked_actualFMatrix_det_ne_zero
  emit "ZetaNine.CoefficientMapMatrix.inverseMultiplier_coordinates_eq_row_inverse" `ZetaNine.CoefficientMapMatrix.inverseMultiplier_coordinates_eq_row_inverse
  emit "ZetaNine.CoefficientMapMatrix.inverseMultiplier_eq_coordinatePolynomial_row_inverse" `ZetaNine.CoefficientMapMatrix.inverseMultiplier_eq_coordinatePolynomial_row_inverse
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerPair_mul_selection" `ZetaNine.CoefficientMapMatrix.selectedIntegerPair_mul_selection
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates" `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates_product" `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates_product
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_natDegree_le" `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_natDegree_le
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_output" `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_output
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_five_actual_coordinates" `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_five_actual_coordinates
  emit "ZetaNine.CoefficientMapMatrix.selected_prescribed_L" `ZetaNine.CoefficientMapMatrix.selected_prescribed_L
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_exact_L" `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_exact_L
  emit "ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute" `ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_actual_HasSum_and_absolute
  emit "solution" `solution
