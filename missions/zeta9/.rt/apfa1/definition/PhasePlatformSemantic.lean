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
  completeActualModuleInventory [`Definitions.Def_ZetaNine_AnalyticPhase, `Native.AnalyticPhase, `Native.AnalyticPhaseUpperBound, `PhasePlatformAssertions]
