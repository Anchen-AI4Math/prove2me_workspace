import OutputsIndependentAssertionsV1
import IndependentExprDagV3
import Lean
open Lean Meta IndependentLosslessExprDagV1
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
private def standard (n : Name) : MetaM (Array Name) := do
  let axioms ← collectAxioms n
  unless axioms.toList.all (fun a => ([`propext,`Classical.choice,`Quot.sound] : List Name).contains a) do
    throwError "Non-Std3 actual declaration: {n}"
  return axioms
private def closed (n : Name) (ty val : Expr) : MetaM Unit := do
  unless !(ty.hasFVar || ty.hasMVar || val.hasFVar || val.hasMVar) do throwError "Unclosed actual declaration: {n}"
private def full (n : Name) (kind : String) : MetaM Unit := do
  let info ← getConstInfo n
  let val ← match info with
    | .defnInfo actual => pure actual.value
    | .thmInfo actual => pure actual.value
    | .opaqueInfo actual => pure actual.value
    | _ => throwError "Expected actual definition/proof/opaque: {n}"
  closed n info.type val
  let axioms ← standard n
  let payload ← ofExcept (persistedRoundTrip info.type val)
  let (restoredType,restoredValue) ← ofExcept (decode payload)
  let typeKernel ← isDefEq info.type restoredType
  let valueKernel ← isDefEq val restoredValue
  unless typeKernel && valueKernel && Expr.equal info.type restoredType && Expr.equal val restoredValue do
    throwError "Lossless full SOURCE reconstruction failed: {n}"
  IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str n.toString),
    ("closed",toJson true),("axioms",toJson (axioms.toList.map Name.toString)),
    ("complete_type_and_value_expression_dag",payload),("full_type_raw_Expr",Json.str (reprStr info.type)),
    ("all_fields_Expr_equal_roundtrip",toJson true),("type_roundtrip_kernel_equal",toJson typeKernel),
    ("value_roundtrip_kernel_equal",toJson valueKernel)]).compress
private def wholeDefinition (actual expected : Name) : MetaM Unit := do
  let .defnInfo a ← getConstInfo actual | throwError "Actual definition kind differs"
  let .defnInfo e ← getConstInfo expected | throwError "Expected definition kind differs"
  let typeKernel ← isDefEq a.type e.type
  let valueKernel ← isDefEq a.value e.value
  unless typeKernel && valueKernel do throwError "Full type/value kernel mismatch: {actual}"
  IO.println (Json.mkObj [("kind",Json.str "independent_full_definition_kernel_comparison"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("type_kernel_equal",toJson typeKernel),("value_kernel_equal",toJson valueKernel),
    ("type_Expr_equal_diagnostic",toJson (Expr.equal a.type e.type)),
    ("value_Expr_equal_diagnostic",toJson (Expr.equal a.value e.value)),
    ("full_actual_type_and_value_dag",← ofExcept (persistedRoundTrip a.type a.value)),
    ("full_expected_type_and_value_dag",← ofExcept (persistedRoundTrip e.type e.value))]).compress
private def wholeType (actual expected : Name) : MetaM Unit := do
  let a ← getConstInfo actual
  let e ← getConstInfo expected
  let same ← isDefEq a.type e.type
  unless same do throwError "Complete original forall type mismatch: {actual}"
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_forall_kernel_comparison"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("whole_type_kernel_equal",toJson same),("type_Expr_equal_diagnostic",toJson (Expr.equal a.type e.type)),
    ("full_actual_type_raw_Expr",Json.str (reprStr a.type)),("full_expected_type_raw_Expr",Json.str (reprStr e.type))]).compress
private def internalHelpers (modules : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut found : List Name := []
  for (name,info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[index.toNat]? | continue
    if modules.contains moduleName && (name.isInternal || (privateToUserName? name).isSome || name.toString.endsWith ".eq_1") then
      found := name :: found
      full name "independent_generated_or_internal_helper"
  IO.println (Json.mkObj [("kind",Json.str "independent_actual_helper_inventory"),
    ("modules",toJson (modules.map Name.toString)),("names",toJson (found.map Name.toString))]).compress
run_meta do
  full `ZetaNine.CoefficientMapFormalTransportOutputs.weightedR_eval_one_zero "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_weightedR_eval_one_zero "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.weightedR_eval_one_zero `OutputsIndependentExpected.expected_weightedR_eval_one_zero
  full `ZetaNine.CoefficientMapFormalTransportOutputs.quartic_properMultiplier "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_quartic_properMultiplier "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.quartic_properMultiplier `OutputsIndependentExpected.expected_quartic_properMultiplier
  full `ZetaNine.CoefficientMapFormalTransportOutputs.weighted_boundary_sum_zero "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_weighted_boundary_sum_zero "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.weighted_boundary_sum_zero `OutputsIndependentExpected.expected_weighted_boundary_sum_zero
  full `ZetaNine.CoefficientMapFormalTransportOutputs.remainder_boundary_sum_zero "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_remainder_boundary_sum_zero "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.remainder_boundary_sum_zero `OutputsIndependentExpected.expected_remainder_boundary_sum_zero
  full `ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedOldCoefficient_harmonic "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_sum_extendedOldCoefficient_harmonic "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedOldCoefficient_harmonic `OutputsIndependentExpected.expected_sum_extendedOldCoefficient_harmonic
  full `ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedRemainderCoefficient_harmonic "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_sum_extendedRemainderCoefficient_harmonic "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedRemainderCoefficient_harmonic `OutputsIndependentExpected.expected_sum_extendedRemainderCoefficient_harmonic
  full `ZetaNine.CoefficientMapFormalTransportOutputs.sum_previousRemainderCoefficient_harmonic "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_sum_previousRemainderCoefficient_harmonic "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.sum_previousRemainderCoefficient_harmonic `OutputsIndependentExpected.expected_sum_previousRemainderCoefficient_harmonic
  full `ZetaNine.CoefficientMapFormalTransportOutputs.sum_harmonic_succ "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_sum_harmonic_succ "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.sum_harmonic_succ `OutputsIndependentExpected.expected_sum_harmonic_succ
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_harmonic_order_transport "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_actual_chosen_harmonic_order_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_harmonic_order_transport `OutputsIndependentExpected.expected_actual_chosen_harmonic_order_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_correction "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_actual_chosen_constantTerm_correction "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_correction `OutputsIndependentExpected.expected_actual_chosen_constantTerm_correction
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_actual_chosen_constantTerm_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport `OutputsIndependentExpected.expected_actual_chosen_constantTerm_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_five_output_transport "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_actual_chosen_five_output_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_five_output_transport `OutputsIndependentExpected.expected_actual_chosen_five_output_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_Gamma_row_transport "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_actual_chosen_Gamma_row_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_Gamma_row_transport `OutputsIndependentExpected.expected_actual_chosen_Gamma_row_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_actual_five_output_matrix_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport `OutputsIndependentExpected.expected_actual_five_output_matrix_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.n_one_five_output_transport "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_n_one_five_output_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.n_one_five_output_transport `OutputsIndependentExpected.expected_n_one_five_output_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.n_one_matrix_transport "independent_actual_original_forall"
  full `OutputsIndependentExpected.expected_n_one_matrix_transport "independent_expected_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.n_one_matrix_transport `OutputsIndependentExpected.expected_n_one_matrix_transport
  full `ZetaNine.CoefficientMapFormalTransportData.connectionPair "independent_actual_related_definition"
  full `OutputsIndependentFormula.connectionPair "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.connectionPair `OutputsIndependentFormula.connectionPair
  full `OutputsIndependentWhole.whole_connectionPair "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.connectionP "independent_actual_related_definition"
  full `OutputsIndependentFormula.connectionP "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.connectionP `OutputsIndependentFormula.connectionP
  full `OutputsIndependentWhole.whole_connectionP "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.connectionQ "independent_actual_related_definition"
  full `OutputsIndependentFormula.connectionQ "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.connectionQ `OutputsIndependentFormula.connectionQ
  full `OutputsIndependentWhole.whole_connectionQ "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.connectionGamma "independent_actual_related_definition"
  full `OutputsIndependentFormula.connectionGamma "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.connectionGamma `OutputsIndependentFormula.connectionGamma
  full `OutputsIndependentWhole.whole_connectionGamma "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.remainderNumerator "independent_actual_related_definition"
  full `OutputsIndependentFormula.remainderNumerator "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.remainderNumerator `OutputsIndependentFormula.remainderNumerator
  full `OutputsIndependentWhole.whole_remainderNumerator "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator "independent_actual_related_definition"
  full `OutputsIndependentFormula.shiftedRemainderNumerator "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator `OutputsIndependentFormula.shiftedRemainderNumerator
  full `OutputsIndependentWhole.whole_shiftedRemainderNumerator "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries "independent_actual_related_definition"
  full `OutputsIndependentFormula.numeratorClearedSeries "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries `OutputsIndependentFormula.numeratorClearedSeries
  full `OutputsIndependentWhole.whole_numeratorClearedSeries "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient "independent_actual_related_definition"
  full `OutputsIndependentFormula.numeratorLocalCoefficient "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient `OutputsIndependentFormula.numeratorLocalCoefficient
  full `OutputsIndependentWhole.whole_numeratorLocalCoefficient "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient "independent_actual_related_definition"
  full `OutputsIndependentFormula.remainderCoefficient "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient `OutputsIndependentFormula.remainderCoefficient
  full `OutputsIndependentWhole.whole_remainderCoefficient "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient "independent_actual_related_definition"
  full `OutputsIndependentFormula.extendedOldCoefficient "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient `OutputsIndependentFormula.extendedOldCoefficient
  full `OutputsIndependentWhole.whole_extendedOldCoefficient "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient "independent_actual_related_definition"
  full `OutputsIndependentFormula.extendedRemainderCoefficient "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient `OutputsIndependentFormula.extendedRemainderCoefficient
  full `OutputsIndependentWhole.whole_extendedRemainderCoefficient "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient "independent_actual_related_definition"
  full `OutputsIndependentFormula.previousRemainderCoefficient "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient `OutputsIndependentFormula.previousRemainderCoefficient
  full `OutputsIndependentWhole.whole_previousRemainderCoefficient "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFiniteSum.rho "independent_actual_related_definition"
  full `OutputsIndependentFormula.rho "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFiniteSum.rho `OutputsIndependentFormula.rho
  full `OutputsIndependentWhole.whole_rho "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapFiniteSum.constantTerm "independent_actual_related_definition"
  full `OutputsIndependentFormula.constantTerm "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapFiniteSum.constantTerm `OutputsIndependentFormula.constantTerm
  full `OutputsIndependentWhole.whole_constantTerm "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapAggregate.aggregate "independent_actual_related_definition"
  full `OutputsIndependentFormula.aggregate "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapAggregate.aggregate `OutputsIndependentFormula.aggregate
  full `OutputsIndependentWhole.whole_aggregate "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapAggregate.aggregateLinearMap "independent_actual_related_definition"
  full `OutputsIndependentFormula.aggregateLinearMap "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapAggregate.aggregateLinearMap `OutputsIndependentFormula.aggregateLinearMap
  full `OutputsIndependentWhole.whole_aggregateLinearMap "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap "independent_actual_related_definition"
  full `OutputsIndependentFormula.quarticAggregateLinearMap "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap `OutputsIndependentFormula.quarticAggregateLinearMap
  full `OutputsIndependentWhole.whole_quarticAggregateLinearMap "independent_whole_function_rfl"
  full `ZetaNine.CoefficientMapMatrix.actualFMatrix "independent_actual_related_definition"
  full `OutputsIndependentFormula.actualFMatrix "independent_expected_related_definition"
  wholeDefinition `ZetaNine.CoefficientMapMatrix.actualFMatrix `OutputsIndependentFormula.actualFMatrix
  full `OutputsIndependentWhole.whole_actualFMatrix "independent_whole_function_rfl"
  full `OutputsIndependentBoundary.minimum_B "independent_typed_boundary"
  full `OutputsIndependentBoundary.minimum_all_coordinates "independent_typed_boundary"
  full `OutputsIndependentBoundary.minimum_LEFT_matrix "independent_typed_boundary"
  full `OutputsIndependentBoundary.even_LEFT_matrix "independent_typed_boundary"
  full `OutputsIndependentBoundary.odd_LEFT_matrix "independent_typed_boundary"
  full `OutputsIndependentBoundary.maximum_remainder_degree "independent_typed_boundary"
  full `OutputsIndependentBoundary.excluded_zero_parameter "independent_typed_boundary"
  full `OutputsIndependentBoundary.empty_harmonic_successor "independent_typed_boundary"
  full `OutputsIndependentBoundary.maximum_quartic_degree "independent_typed_boundary"
  internalHelpers [`missions.zeta9.formalization.CoefficientMap, `missions.zeta9.formalization.CoefficientMapJet, `missions.zeta9.formalization.CoefficientMapInjectivity, `missions.zeta9.formalization.CoefficientMapPartialFractions, `missions.zeta9.formalization.CoefficientMapReflection, `Definitions.Def_ZetaNine_HarmonicStability, `missions.zeta9.formalization.CoefficientMapFiniteSum, `missions.zeta9.formalization.CoefficientMapSummation, `missions.zeta9.formalization.CoefficientMapAggregate, `missions.zeta9.formalization.CoefficientMapTelescoper, `missions.zeta9.formalization.CoefficientMapShiftDegree, `missions.zeta9.formalization.CoefficientMapKernelBridge, `missions.zeta9.formalization.CoefficientMapConnection, `missions.zeta9.formalization.CoefficientMapParameterShift, `missions.zeta9.formalization.CoefficientMapFormalTransportData, `missions.zeta9.formalization.CoefficientMapFormalTransportBounds, `missions.zeta9.formalization.CoefficientMapFormalTransportNumerators, `missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions, `missions.zeta9.formalization.CoefficientMapFormalTransportJets, `missions.zeta9.formalization.CoefficientMapMatrix, `missions.zeta9.formalization.CoefficientMapFormalTransportOutputs, `OutputsIndependentAssertionsV1]
