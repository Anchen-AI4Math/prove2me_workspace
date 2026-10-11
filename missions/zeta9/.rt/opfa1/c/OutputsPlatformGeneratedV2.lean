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
      IO.println (Json.mkObj [("kind",Json.str "platform_author_all_actual_declaration_Std3"),
        ("declaration",Json.str name.toString),("module",Json.str moduleName.toString),
        ("axioms",toJson (axioms.toList.map Name.toString)),("closed_complete_type",toJson true)]).compress
      match info with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        full name "platform_author_all_actual_complete_type_and_value"
      | _ => pure ()
      if name.isInternalDetail || (privateToUserName? name).isSome then
        helpers := name :: helpers
  IO.println (Json.mkObj [("kind",Json.str "platform_author_complete_generated_closure_inventory"),
    ("modules",toJson (modules.map Name.toString)),("all_declarations",toJson (allNames.map Name.toString)),
    ("all_generated_helpers",toJson (helpers.map Name.toString)),
    ("predicate",Json.str "isInternalDetail or actual privateToUserName; covers every public eq_N/match_N/proof_N/omega_N, internal and numbered helper")]).compress
run_meta do
  completeActualModuleInventory [`Definitions.Def_ZetaNine_CoefficientMap, `Definitions.Def_ZetaNine_CoefficientMapJet, `Definitions.Def_ZetaNine_CoefficientMapInjectivity, `Definitions.Def_ZetaNine_CoefficientMapPartialFractions, `Definitions.Def_ZetaNine_CoefficientMapReflection, `Definitions.Def_ZetaNine_HarmonicStability, `Definitions.Def_ZetaNine_CoefficientMapFiniteSum, `Definitions.Def_ZetaNine_CoefficientMapSummation, `Definitions.Def_ZetaNine_CoefficientMapAggregate, `Definitions.Def_ZetaNine_CoefficientMapTelescoper, `Definitions.Def_ZetaNine_CoefficientMapShiftDegree, `Definitions.Def_ZetaNine_CoefficientMapKernelBridge, `Definitions.Def_ZetaNine_CoefficientMapMatrix, `Definitions.Def_ZetaNine_CoefficientMapConnection, `Definitions.Def_ZetaNine_CoefficientMapNumeratorPF, `Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs, `Oracle.CoefficientMap, `Oracle.CoefficientMapJet, `Oracle.CoefficientMapInjectivity, `Oracle.CoefficientMapPartialFractions, `Oracle.CoefficientMapReflection, `Oracle.HarmonicStability, `Oracle.CoefficientMapFiniteSum, `Oracle.CoefficientMapSummation, `Oracle.CoefficientMapAggregate, `Oracle.CoefficientMapTelescoper, `Oracle.CoefficientMapShiftDegree, `Oracle.CoefficientMapKernelBridge, `Oracle.CoefficientMapConnection, `Oracle.CoefficientMapParameterShift, `Oracle.CoefficientMapFormalTransportData, `Oracle.CoefficientMapFormalTransportBounds, `Oracle.CoefficientMapFormalTransportNumerators, `Oracle.CoefficientMapNumeratorPartialFractions, `Oracle.CoefficientMapFormalTransportJets, `Oracle.CoefficientMapMatrix, `Oracle.CoefficientMapFormalTransportOutputs, `Solutions.Sol_ZetaNine_CoefficientMapFormalTransportOutputs_constant, `OutputsPlatformAssertions]
