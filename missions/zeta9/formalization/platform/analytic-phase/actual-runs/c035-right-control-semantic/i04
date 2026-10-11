import PhasePlatformAssertions
import PhasePlatformExprDagV1
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
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_forall_kernel_comparison"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("whole_type_kernel_equal",toJson same),("type_Expr_equal_diagnostic",toJson (Expr.equal a.type e.type)),
    ("full_actual_type_raw_Expr",Json.str (reprStr a.type)),("full_expected_type_raw_Expr",Json.str (reprStr e.type))]).compress
private def definitionKernel (actual expected : Name) : MetaM Unit := do
  let .defnInfo a ← getConstInfo actual | throwError "Expected actual definition"
  let .defnInfo e ← getConstInfo expected | throwError "Expected independently defined function"
  let sameType ← isDefEq a.type e.type
  let sameValue ← isDefEq a.value e.value
  unless sameType && sameValue do throwError "Complete actual definition type/value differs: {actual}"
  IO.println (Json.mkObj [("kind",Json.str "independent_full_definition_kernel_comparison"),
    ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
    ("type_kernel_equal",toJson sameType),("value_kernel_equal",toJson sameValue),
    ("type_Expr_equal_diagnostic",toJson (Expr.equal a.type e.type)),
    ("value_Expr_equal_diagnostic",toJson (Expr.equal a.value e.value)),
    ("full_actual_type_and_value_dag",← ofExcept (persistedRoundTrip a.type a.value)),
    ("full_expected_type_and_value_dag",← ofExcept (persistedRoundTrip e.type e.value))]).compress
private def completeActualModuleInventory (modules : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut allNames : List Name := []
  let mut helpers : List Name := []
  for (name,info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[index.toNat]? | continue
    if modules.contains moduleName then
      let axioms ← standard name
      unless !(info.type.hasFVar || info.type.hasMVar) do throwError "Unclosed actual declaration type: {name}"
      allNames := name :: allNames
      IO.println (Json.mkObj [("kind",Json.str "independent_all_actual_declaration_Std3"),
        ("declaration",Json.str name.toString),("module",Json.str moduleName.toString),
        ("axioms",toJson (axioms.toList.map Name.toString)),("closed_complete_type",toJson true)]).compress
      if name.isInternalDetail || (privateToUserName? name).isSome then
        helpers := name :: helpers
        full name "independent_all_generated_complete_type_and_value"
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_generated_closure_inventory"),
    ("modules",toJson (modules.map Name.toString)),("all_declarations",toJson (allNames.map Name.toString)),
    ("all_generated_helpers",toJson (helpers.map Name.toString)),
    ("predicate",Json.str "isInternalDetail or actual privateToUserName; covers every public eq_N/match_N/proof_N/omega_N, internal and numbered helper")]).compress
run_meta do
  full `ZetaNine.AnalyticPhase.phaseGap_identity "actual_original_forall"
  full `PhasePlatformNativeOracle.phaseGap_identity "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phaseGap_identity `PhasePlatformNativeOracle.phaseGap_identity
  full `ZetaNine.AnalyticPhase.phaseGap_pos "actual_original_forall"
  full `PhasePlatformNativeOracle.phaseGap_pos "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phaseGap_pos `PhasePlatformNativeOracle.phaseGap_pos
  full `ZetaNine.AnalyticPhase.phaseRatio_pos "actual_original_forall"
  full `PhasePlatformNativeOracle.phaseRatio_pos "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phaseRatio_pos `PhasePlatformNativeOracle.phaseRatio_pos
  full `ZetaNine.AnalyticPhase.phaseRatio_lt_one "actual_original_forall"
  full `PhasePlatformNativeOracle.phaseRatio_lt_one "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phaseRatio_lt_one `PhasePlatformNativeOracle.phaseRatio_lt_one
  full `ZetaNine.AnalyticPhase.phaseSlope_eq_log_ratio "actual_original_forall"
  full `PhasePlatformNativeOracle.phaseSlope_eq_log_ratio "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phaseSlope_eq_log_ratio `PhasePlatformNativeOracle.phaseSlope_eq_log_ratio
  full `ZetaNine.AnalyticPhase.phaseSlope_neg_right "actual_original_forall"
  full `PhasePlatformNativeOracle.phaseSlope_neg_right "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phaseSlope_neg_right `PhasePlatformNativeOracle.phaseSlope_neg_right
  full `ZetaNine.AnalyticPhase.hasDerivAt_mul_log_shift "actual_original_forall"
  full `PhasePlatformNativeOracle.hasDerivAt_mul_log_shift "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.hasDerivAt_mul_log_shift `PhasePlatformNativeOracle.hasDerivAt_mul_log_shift
  full `ZetaNine.AnalyticPhase.phase_hasDerivAt "actual_original_forall"
  full `PhasePlatformNativeOracle.phase_hasDerivAt "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phase_hasDerivAt `PhasePlatformNativeOracle.phase_hasDerivAt
  full `ZetaNine.AnalyticPhase.deriv_phase "actual_original_forall"
  full `PhasePlatformNativeOracle.deriv_phase "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.deriv_phase `PhasePlatformNativeOracle.deriv_phase
  full `ZetaNine.AnalyticPhase.phase_strictAntiOn_right "actual_original_forall"
  full `PhasePlatformNativeOracle.phase_strictAntiOn_right "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phase_strictAntiOn_right `PhasePlatformNativeOracle.phase_strictAntiOn_right
  full `ZetaNine.AnalyticPhase.phase_le_right_endpoint "actual_original_forall"
  full `PhasePlatformNativeOracle.phase_le_right_endpoint "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phase_le_right_endpoint `PhasePlatformNativeOracle.phase_le_right_endpoint
  full `ZetaNine.AnalyticPhase.upperSlopeConstant_pos "actual_original_forall"
  full `PhasePlatformNativeOracle.upperSlopeConstant_pos "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.upperSlopeConstant_pos `PhasePlatformNativeOracle.upperSlopeConstant_pos
  full `ZetaNine.AnalyticPhase.upperSlopeConstant_eq "actual_original_forall"
  full `PhasePlatformNativeOracle.upperSlopeConstant_eq "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.upperSlopeConstant_eq `PhasePlatformNativeOracle.upperSlopeConstant_eq
  full `ZetaNine.AnalyticPhase.phaseRatio_small_interval_le "actual_original_forall"
  full `PhasePlatformNativeOracle.phaseRatio_small_interval_le "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phaseRatio_small_interval_le `PhasePlatformNativeOracle.phaseRatio_small_interval_le
  full `ZetaNine.AnalyticPhase.phaseSlope_small_interval_le "actual_original_forall"
  full `PhasePlatformNativeOracle.phaseSlope_small_interval_le "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phaseSlope_small_interval_le `PhasePlatformNativeOracle.phaseSlope_small_interval_le
  full `ZetaNine.AnalyticPhase.phase_one_eq "actual_original_forall"
  full `PhasePlatformNativeOracle.phase_one_eq "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phase_one_eq `PhasePlatformNativeOracle.phase_one_eq
  full `ZetaNine.AnalyticPhase.smoothPhaseGap_one "actual_original_forall"
  full `PhasePlatformNativeOracle.smoothPhaseGap_one "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.smoothPhaseGap_one `PhasePlatformNativeOracle.smoothPhaseGap_one
  full `ZetaNine.AnalyticPhase.smoothPhaseGap_hasDerivAt "actual_original_forall"
  full `PhasePlatformNativeOracle.smoothPhaseGap_hasDerivAt "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.smoothPhaseGap_hasDerivAt `PhasePlatformNativeOracle.smoothPhaseGap_hasDerivAt
  full `ZetaNine.AnalyticPhase.smoothPhaseRatio_pos "actual_original_forall"
  full `PhasePlatformNativeOracle.smoothPhaseRatio_pos "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.smoothPhaseRatio_pos `PhasePlatformNativeOracle.smoothPhaseRatio_pos
  full `ZetaNine.AnalyticPhase.smoothPhaseRatio_le_upperSlopeConstant "actual_original_forall"
  full `PhasePlatformNativeOracle.smoothPhaseRatio_le_upperSlopeConstant "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.smoothPhaseRatio_le_upperSlopeConstant `PhasePlatformNativeOracle.smoothPhaseRatio_le_upperSlopeConstant
  full `ZetaNine.AnalyticPhase.smoothPhaseSlope_eq_log_ratio "actual_original_forall"
  full `PhasePlatformNativeOracle.smoothPhaseSlope_eq_log_ratio "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.smoothPhaseSlope_eq_log_ratio `PhasePlatformNativeOracle.smoothPhaseSlope_eq_log_ratio
  full `ZetaNine.AnalyticPhase.smoothPhaseSlope_nonpos "actual_original_forall"
  full `PhasePlatformNativeOracle.smoothPhaseSlope_nonpos "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.smoothPhaseSlope_nonpos `PhasePlatformNativeOracle.smoothPhaseSlope_nonpos
  full `ZetaNine.AnalyticPhase.smoothPhaseGap_antitoneOn "actual_original_forall"
  full `PhasePlatformNativeOracle.smoothPhaseGap_antitoneOn "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.smoothPhaseGap_antitoneOn `PhasePlatformNativeOracle.smoothPhaseGap_antitoneOn
  full `ZetaNine.AnalyticPhase.smoothPhaseGap_le_zero "actual_original_forall"
  full `PhasePlatformNativeOracle.smoothPhaseGap_le_zero "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.smoothPhaseGap_le_zero `PhasePlatformNativeOracle.smoothPhaseGap_le_zero
  full `ZetaNine.AnalyticPhase.mul_one_add_log_div_le "actual_original_forall"
  full `PhasePlatformNativeOracle.mul_one_add_log_div_le "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.mul_one_add_log_div_le `PhasePlatformNativeOracle.mul_one_add_log_div_le
  full `ZetaNine.AnalyticPhase.phase_small_interval_identity "actual_original_forall"
  full `PhasePlatformNativeOracle.phase_small_interval_identity "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phase_small_interval_identity `PhasePlatformNativeOracle.phase_small_interval_identity
  full `ZetaNine.AnalyticPhase.phase_small_interval_le_one_add_constant "actual_original_forall"
  full `PhasePlatformNativeOracle.phase_small_interval_le_one_add_constant "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phase_small_interval_le_one_add_constant `PhasePlatformNativeOracle.phase_small_interval_le_one_add_constant
  full `ZetaNine.AnalyticPhase.phase_global_le_one_add_constant "actual_original_forall"
  full `PhasePlatformNativeOracle.phase_global_le_one_add_constant "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phase_global_le_one_add_constant `PhasePlatformNativeOracle.phase_global_le_one_add_constant
  full `ZetaNine.AnalyticPhase.log_two_lower_rational "actual_original_forall"
  full `PhasePlatformNativeOracle.log_two_lower_rational "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.log_two_lower_rational `PhasePlatformNativeOracle.log_two_lower_rational
  full `ZetaNine.AnalyticPhase.log_three_upper_rational "actual_original_forall"
  full `PhasePlatformNativeOracle.log_three_upper_rational "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.log_three_upper_rational `PhasePlatformNativeOracle.log_three_upper_rational
  full `ZetaNine.AnalyticPhase.upperSlopeConstant_lt_rational "actual_original_forall"
  full `PhasePlatformNativeOracle.upperSlopeConstant_lt_rational "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.upperSlopeConstant_lt_rational `PhasePlatformNativeOracle.upperSlopeConstant_lt_rational
  full `ZetaNine.AnalyticPhase.phase_one_add_constant_lt_certified "actual_original_forall"
  full `PhasePlatformNativeOracle.phase_one_add_constant_lt_certified "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phase_one_add_constant_lt_certified `PhasePlatformNativeOracle.phase_one_add_constant_lt_certified
  full `ZetaNine.AnalyticPhase.phase_global_lt_certified "actual_original_forall"
  full `PhasePlatformNativeOracle.phase_global_lt_certified "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phase_global_lt_certified `PhasePlatformNativeOracle.phase_global_lt_certified
  full `ZetaNine.AnalyticPhase.phase_global_upper_bound "actual_original_forall"
  full `PhasePlatformNativeOracle.phase_global_upper_bound "oracle_original_forall"
  wholeType `ZetaNine.AnalyticPhase.phase_global_upper_bound `PhasePlatformNativeOracle.phase_global_upper_bound
  full `solution "actual_complete_solution"
  wholeType `solution `ZetaNine.AnalyticPhase.phase_strictAntiOn_right
  full `ZetaNine.AnalyticPhase.phase "actual_full_definition"
  full `PhasePlatformNativeOracle.phase "oracle_full_definition"
  definitionKernel `ZetaNine.AnalyticPhase.phase `PhasePlatformNativeOracle.phase
  full `PhasePlatformWhole.whole_phase "actual_whole_function_rfl"
  full `ZetaNine.AnalyticPhase.phaseRatio "actual_full_definition"
  full `PhasePlatformNativeOracle.phaseRatio "oracle_full_definition"
  definitionKernel `ZetaNine.AnalyticPhase.phaseRatio `PhasePlatformNativeOracle.phaseRatio
  full `PhasePlatformWhole.whole_phaseRatio "actual_whole_function_rfl"
  full `ZetaNine.AnalyticPhase.phaseSlope "actual_full_definition"
  full `PhasePlatformNativeOracle.phaseSlope "oracle_full_definition"
  definitionKernel `ZetaNine.AnalyticPhase.phaseSlope `PhasePlatformNativeOracle.phaseSlope
  full `PhasePlatformWhole.whole_phaseSlope "actual_whole_function_rfl"
  full `ZetaNine.AnalyticPhase.upperSlopeConstant "actual_full_definition"
  full `PhasePlatformNativeOracle.upperSlopeConstant "oracle_full_definition"
  definitionKernel `ZetaNine.AnalyticPhase.upperSlopeConstant `PhasePlatformNativeOracle.upperSlopeConstant
  full `PhasePlatformWhole.whole_upperSlopeConstant "actual_whole_function_rfl"
  full `ZetaNine.AnalyticPhase.smoothPhaseGap "actual_full_definition"
  full `PhasePlatformNativeOracle.smoothPhaseGap "oracle_full_definition"
  definitionKernel `ZetaNine.AnalyticPhase.smoothPhaseGap `PhasePlatformNativeOracle.smoothPhaseGap
  full `PhasePlatformWhole.whole_smoothPhaseGap "actual_whole_function_rfl"
  full `ZetaNine.AnalyticPhase.smoothPhaseSlope "actual_full_definition"
  full `PhasePlatformNativeOracle.smoothPhaseSlope "oracle_full_definition"
  definitionKernel `ZetaNine.AnalyticPhase.smoothPhaseSlope `PhasePlatformNativeOracle.smoothPhaseSlope
  full `PhasePlatformWhole.whole_smoothPhaseSlope "actual_whole_function_rfl"
  full `ZetaNine.AnalyticPhase.smoothPhaseRatio "actual_full_definition"
  full `PhasePlatformNativeOracle.smoothPhaseRatio "oracle_full_definition"
  definitionKernel `ZetaNine.AnalyticPhase.smoothPhaseRatio `PhasePlatformNativeOracle.smoothPhaseRatio
  full `PhasePlatformWhole.whole_smoothPhaseRatio "actual_whole_function_rfl"
  full `PhasePlatformBoundary.phase_endpoint_one "actual_typed_boundary"
  full `PhasePlatformBoundary.gap_endpoint_one "actual_typed_boundary"
  full `PhasePlatformBoundary.ratio_endpoint_one "actual_typed_boundary"
  full `PhasePlatformBoundary.slope_constant_exact "actual_typed_boundary"
  full `PhasePlatformBoundary.slope_constant_small "actual_typed_boundary"
  full `PhasePlatformBoundary.universal_cap_attained "actual_typed_boundary"
  full `PhasePlatformBoundary.gap_endpoint_right "actual_typed_boundary"
  full `PhasePlatformBoundary.phase_endpoint_right "actual_typed_boundary"
  full `PhasePlatformBoundary.phase_inside_left "actual_typed_boundary"
  full `PhasePlatformBoundary.phase_in_right "actual_typed_boundary"
  full `PhasePlatformBoundary.phase_zero_exact "actual_typed_boundary"
  full `PhasePlatformBoundary.phase_zero_exceeds_cap "actual_typed_boundary"
  full `PhasePlatformBoundary.excluded_endpoint_one "actual_typed_boundary"
  full `PhasePlatformBoundary.excluded_zero "actual_typed_boundary"
  full `PhasePlatformBoundary.global_stronger_margin "actual_typed_boundary"
  completeActualModuleInventory [`Definitions.Def_ZetaNine_AnalyticPhase, `Native.AnalyticPhase, `Native.AnalyticPhaseUpperBound, `PhasePlatformAssertions, `Solutions.Sol_ZetaNine_AnalyticPhase_phase_strictAntiOn_right]
