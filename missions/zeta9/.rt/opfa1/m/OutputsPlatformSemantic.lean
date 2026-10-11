import OutputsPlatformAssertions
import OutputsPlatformExprDagV1
import Lean
open Lean Meta IndependentLosslessExprDagV1
set_option maxRecDepth 20000
set_option maxHeartbeats 0
private def standard (name : Name) : MetaM (Array Name) := do
  let axioms ← collectAxioms name
  unless axioms.toList.all (fun a => ([`propext,`Classical.choice,`Quot.sound] : List Name).contains a) do
    throwError "Non-Std3 actual declaration: {name}"
  return axioms
private def full (name : Name) (kind : String) : MetaM Unit := do
  let info ← getConstInfo name
  let value ← match info with
    | .thmInfo a => pure a.value
    | .defnInfo a => pure a.value
    | .opaqueInfo a => pure a.value
    | _ => throwError "Actual definition or proof value absent: {name}"
  unless !(info.type.hasFVar || info.type.hasMVar || value.hasFVar || value.hasMVar) do
    throwError "Actual complete type/value is not closed: {name}"
  let axioms ← standard name
  let inferred ← inferType value
  let typed ← isDefEq info.type inferred
  unless typed do throwError "Actual value inferType mismatch: {name}"
  let payload ← ofExcept (persistedRoundTrip info.type value)
  let (rt,rv) ← ofExcept (decode payload)
  let sameType ← isDefEq info.type rt
  let sameValue ← isDefEq value rv
  unless sameType && sameValue && Expr.equal info.type rt && Expr.equal value rv do
    throwError "Lossless whole type/value reconstruction mismatch: {name}"
  IO.println (Json.mkObj [("kind",Json.str kind),("declaration",Json.str name.toString),
    ("axioms",toJson (axioms.toList.map Name.toString)),("closed_complete_type_and_value",toJson true),
    ("actual_value_inferType_kernel_equal",toJson typed),("actual_inferred_type_raw_Expr",Json.str (reprStr inferred)),
    ("full_type_raw_Expr",Json.str (reprStr info.type)),("complete_type_and_value_expression_dag",payload),
    ("all_fields_Expr_equal_roundtrip",toJson true),("type_roundtrip_kernel_equal",toJson sameType),
    ("value_roundtrip_kernel_equal",toJson sameValue)]).compress
  (← IO.getStdout).flush
private def wholeType (actual expected : Name) : MetaM Unit := do
  let a ← getConstInfo actual
  let e ← getConstInfo expected
  let same ← isDefEq a.type e.type
  unless same do throwError "Complete original forall kernel type differs: {actual}"
  IO.println (Json.mkObj [("kind",Json.str "platform_author_complete_forall_kernel_comparison"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("whole_type_kernel_equal",toJson same),("type_Expr_equal_diagnostic",toJson (Expr.equal a.type e.type)),
    ("full_actual_type_raw_Expr",Json.str (reprStr a.type)),("full_expected_type_raw_Expr",Json.str (reprStr e.type))]).compress
private def definitionKernel (actual expected : Name) : MetaM Unit := do
  let .defnInfo a ← getConstInfo actual | throwError "Expected actual definition"
  let .defnInfo e ← getConstInfo expected | throwError "Expected independently defined function"
  let sameType ← isDefEq a.type e.type
  let sameValue ← isDefEq a.value e.value
  unless sameType && sameValue do throwError "Complete actual definition type/value differs: {actual}"
  IO.println (Json.mkObj [("kind",Json.str "platform_author_full_definition_kernel_comparison"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("type_kernel_equal",toJson sameType),("value_kernel_equal",toJson sameValue),
    ("type_Expr_equal_diagnostic",toJson (Expr.equal a.type e.type)),
    ("value_Expr_equal_diagnostic",toJson (Expr.equal a.value e.value)),
    ("full_actual_type_and_value_dag",← ofExcept (persistedRoundTrip a.type a.value)),
    ("full_expected_type_and_value_dag",← ofExcept (persistedRoundTrip e.type e.value))]).compress
run_meta do
  full `ZetaNine.CoefficientMapFormalTransportOutputs.weightedR_eval_one_zero "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.weightedR_eval_one_zero "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.weightedR_eval_one_zero `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.weightedR_eval_one_zero
  full `ZetaNine.CoefficientMapFormalTransportOutputs.quartic_properMultiplier "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.quartic_properMultiplier "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.quartic_properMultiplier `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.quartic_properMultiplier
  full `ZetaNine.CoefficientMapFormalTransportOutputs.weighted_boundary_sum_zero "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.weighted_boundary_sum_zero "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.weighted_boundary_sum_zero `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.weighted_boundary_sum_zero
  full `ZetaNine.CoefficientMapFormalTransportOutputs.remainder_boundary_sum_zero "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.remainder_boundary_sum_zero "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.remainder_boundary_sum_zero `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.remainder_boundary_sum_zero
  full `ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedOldCoefficient_harmonic "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.sum_extendedOldCoefficient_harmonic "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedOldCoefficient_harmonic `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.sum_extendedOldCoefficient_harmonic
  full `ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedRemainderCoefficient_harmonic "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.sum_extendedRemainderCoefficient_harmonic "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.sum_extendedRemainderCoefficient_harmonic `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.sum_extendedRemainderCoefficient_harmonic
  full `ZetaNine.CoefficientMapFormalTransportOutputs.sum_previousRemainderCoefficient_harmonic "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.sum_previousRemainderCoefficient_harmonic "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.sum_previousRemainderCoefficient_harmonic `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.sum_previousRemainderCoefficient_harmonic
  full `ZetaNine.CoefficientMapFormalTransportOutputs.sum_harmonic_succ "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.sum_harmonic_succ "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.sum_harmonic_succ `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.sum_harmonic_succ
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_harmonic_order_transport "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_chosen_harmonic_order_transport "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_harmonic_order_transport `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_chosen_harmonic_order_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_correction "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_correction "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_correction `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_correction
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_five_output_transport "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_chosen_five_output_transport "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_five_output_transport `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_chosen_five_output_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_Gamma_row_transport "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_chosen_Gamma_row_transport "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_Gamma_row_transport `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_chosen_Gamma_row_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.n_one_five_output_transport "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.n_one_five_output_transport "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.n_one_five_output_transport `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.n_one_five_output_transport
  full `ZetaNine.CoefficientMapFormalTransportOutputs.n_one_matrix_transport "platform_author_actual_original_forall"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.n_one_matrix_transport "platform_author_fresh_native_original_forall"
  wholeType `ZetaNine.CoefficientMapFormalTransportOutputs.n_one_matrix_transport `OutputsPlatformOracle.CoefficientMapFormalTransportOutputs.n_one_matrix_transport
  full `solution "platform_author_actual_complete_solution"
  wholeType `solution `ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport
  full `ZetaNine.CoefficientMapFormalTransportData.connectionPair "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionPair "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.connectionPair `OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionPair
  full `OutputsPlatformWhole.whole_00_connectionPair "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.connectionP "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionP "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.connectionP `OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionP
  full `OutputsPlatformWhole.whole_01_connectionP "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.connectionQ "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionQ "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.connectionQ `OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionQ
  full `OutputsPlatformWhole.whole_02_connectionQ "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.connectionGamma "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionGamma "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.connectionGamma `OutputsPlatformOracle.CoefficientMapFormalTransportData.connectionGamma
  full `OutputsPlatformWhole.whole_03_connectionGamma "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.remainderNumerator "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.remainderNumerator "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.remainderNumerator `OutputsPlatformOracle.CoefficientMapFormalTransportData.remainderNumerator
  full `OutputsPlatformWhole.whole_04_remainderNumerator "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.shiftedRemainderNumerator "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator `OutputsPlatformOracle.CoefficientMapFormalTransportData.shiftedRemainderNumerator
  full `OutputsPlatformWhole.whole_05_shiftedRemainderNumerator "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.numeratorClearedSeries "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries `OutputsPlatformOracle.CoefficientMapFormalTransportData.numeratorClearedSeries
  full `OutputsPlatformWhole.whole_06_numeratorClearedSeries "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.numeratorLocalCoefficient "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient `OutputsPlatformOracle.CoefficientMapFormalTransportData.numeratorLocalCoefficient
  full `OutputsPlatformWhole.whole_07_numeratorLocalCoefficient "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.remainderCoefficient "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient `OutputsPlatformOracle.CoefficientMapFormalTransportData.remainderCoefficient
  full `OutputsPlatformWhole.whole_08_remainderCoefficient "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.extendedOldCoefficient "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient `OutputsPlatformOracle.CoefficientMapFormalTransportData.extendedOldCoefficient
  full `OutputsPlatformWhole.whole_09_extendedOldCoefficient "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.extendedRemainderCoefficient "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient `OutputsPlatformOracle.CoefficientMapFormalTransportData.extendedRemainderCoefficient
  full `OutputsPlatformWhole.whole_10_extendedRemainderCoefficient "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFormalTransportData.previousRemainderCoefficient "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient `OutputsPlatformOracle.CoefficientMapFormalTransportData.previousRemainderCoefficient
  full `OutputsPlatformWhole.whole_11_previousRemainderCoefficient "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFiniteSum.rho "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFiniteSum.rho "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFiniteSum.rho `OutputsPlatformOracle.CoefficientMapFiniteSum.rho
  full `OutputsPlatformWhole.whole_12_rho "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapFiniteSum.constantTerm "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapFiniteSum.constantTerm "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapFiniteSum.constantTerm `OutputsPlatformOracle.CoefficientMapFiniteSum.constantTerm
  full `OutputsPlatformWhole.whole_13_constantTerm "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapAggregate.aggregate "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapAggregate.aggregate "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapAggregate.aggregate `OutputsPlatformOracle.CoefficientMapAggregate.aggregate
  full `OutputsPlatformWhole.whole_14_aggregate "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapAggregate.aggregateLinearMap "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapAggregate.aggregateLinearMap "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapAggregate.aggregateLinearMap `OutputsPlatformOracle.CoefficientMapAggregate.aggregateLinearMap
  full `OutputsPlatformWhole.whole_15_aggregateLinearMap "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapAggregate.quarticAggregateLinearMap "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap `OutputsPlatformOracle.CoefficientMapAggregate.quarticAggregateLinearMap
  full `OutputsPlatformWhole.whole_16_quarticAggregateLinearMap "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapMatrix.actualFMatrix "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapMatrix.actualFMatrix "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapMatrix.actualFMatrix `OutputsPlatformOracle.CoefficientMapMatrix.actualFMatrix
  full `OutputsPlatformWhole.whole_17_actualFMatrix "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapParameterShift.parameterScale "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapParameterShift.parameterScale "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapParameterShift.parameterScale `OutputsPlatformOracle.CoefficientMapParameterShift.parameterScale
  full `OutputsPlatformWhole.whole_18_parameterScale "platform_author_whole_function_rfl"
  full `ZetaNine.CoefficientMapParameterShift.connectionRemainder "platform_author_actual_whole_definition"
  full `OutputsPlatformOracle.CoefficientMapParameterShift.connectionRemainder "platform_author_fresh_native_whole_definition"
  definitionKernel `ZetaNine.CoefficientMapParameterShift.connectionRemainder `OutputsPlatformOracle.CoefficientMapParameterShift.connectionRemainder
  full `OutputsPlatformWhole.whole_19_connectionRemainder "platform_author_whole_function_rfl"
  full `OutputsPlatformBoundary.minimum_B "platform_author_actual_typed_boundary"
  full `OutputsPlatformBoundary.minimum_all_coordinates "platform_author_actual_typed_boundary"
  full `OutputsPlatformBoundary.minimum_LEFT_matrix "platform_author_actual_typed_boundary"
  full `OutputsPlatformBoundary.even_LEFT_matrix "platform_author_actual_typed_boundary"
  full `OutputsPlatformBoundary.odd_LEFT_matrix "platform_author_actual_typed_boundary"
  full `OutputsPlatformBoundary.maximum_remainder_degree "platform_author_actual_typed_boundary"
  full `OutputsPlatformBoundary.excluded_zero_parameter "platform_author_actual_typed_boundary"
  full `OutputsPlatformBoundary.empty_harmonic_successor "platform_author_actual_typed_boundary"
  full `OutputsPlatformBoundary.maximum_quartic_degree "platform_author_actual_typed_boundary"
