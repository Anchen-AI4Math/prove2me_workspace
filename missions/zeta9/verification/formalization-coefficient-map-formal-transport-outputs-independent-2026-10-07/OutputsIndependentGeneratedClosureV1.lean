import OutputsIndependentSemanticV3
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
private def helperProof (name : Name) : MetaM Unit := do
  let info ← getConstInfo name
  let value ← match info with
    | .thmInfo actual => pure actual.value
    | .defnInfo actual => pure actual.value
    | .opaqueInfo actual => pure actual.value
    | _ => throwError "Expected actual proof helper"
  closed name info.type value
  let axioms ← standard name
  let payload ← ofExcept (persistedRoundTrip info.type info.type)
  let (first,second) ← ofExcept (decode payload)
  let same ← isDefEq info.type first
  unless same && Expr.equal info.type first && Expr.equal info.type second do throwError "Full helper type reconstruction failed"
  IO.println (Json.mkObj [("kind",Json.str "independent_generated_helper_proof_type"),
    ("declaration",Json.str name.toString),("closed_type_and_actual_proof",toJson true),
    ("axioms",toJson (axioms.toList.map Name.toString)),("complete_type_expression_dag",payload),
    ("full_type_raw_Expr",Json.str (reprStr info.type)),("all_fields_Expr_equal_roundtrip",toJson true),
    ("whole_type_roundtrip_kernel_equal",toJson same)]).compress
private def everyOwnDeclarationAndGeneratedHelper (modules : List Name) : MetaM Unit := do
  let env ← getEnv
  let mut declarations : List Name := []
  let mut generated : List Name := []
  for (name,info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[index.toNat]? | continue
    if modules.contains moduleName then
      let axioms ← standard name
      unless !(info.type.hasFVar || info.type.hasMVar) do throwError "Actual declaration has free metavariables: {name}"
      declarations := name :: declarations
      IO.println (Json.mkObj [("kind",Json.str "independent_all_actual_declaration_Std3"),
        ("declaration",Json.str name.toString),("module",Json.str moduleName.toString),
        ("axioms",toJson (axioms.toList.map Name.toString)),("closed_complete_type",toJson true)]).compress
      if name.isInternalDetail || (privateToUserName? name).isSome then
        generated := name :: generated
        if ← isProp info.type then
          helperProof name
        else
          full name "independent_all_generated_definition"
  IO.println (Json.mkObj [("kind",Json.str "independent_complete_generated_closure_inventory"),
    ("modules",toJson (modules.map Name.toString)),("all_declarations",toJson (declarations.map Name.toString)),
    ("all_generated_helpers",toJson (generated.map Name.toString)),
    ("predicate",Json.str "isInternalDetail or actual privateToUserName; covers eq_N, match_N, proof_N, omega_N, internal and numerical components")]).compress
run_meta do
  everyOwnDeclarationAndGeneratedHelper [`missions.zeta9.formalization.CoefficientMap, `missions.zeta9.formalization.CoefficientMapJet, `missions.zeta9.formalization.CoefficientMapInjectivity, `missions.zeta9.formalization.CoefficientMapPartialFractions, `missions.zeta9.formalization.CoefficientMapReflection, `Definitions.Def_ZetaNine_HarmonicStability, `missions.zeta9.formalization.CoefficientMapFiniteSum, `missions.zeta9.formalization.CoefficientMapSummation, `missions.zeta9.formalization.CoefficientMapAggregate, `missions.zeta9.formalization.CoefficientMapTelescoper, `missions.zeta9.formalization.CoefficientMapShiftDegree, `missions.zeta9.formalization.CoefficientMapKernelBridge, `missions.zeta9.formalization.CoefficientMapConnection, `missions.zeta9.formalization.CoefficientMapParameterShift, `missions.zeta9.formalization.CoefficientMapFormalTransportData, `missions.zeta9.formalization.CoefficientMapFormalTransportBounds, `missions.zeta9.formalization.CoefficientMapFormalTransportNumerators, `missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions, `missions.zeta9.formalization.CoefficientMapFormalTransportJets, `missions.zeta9.formalization.CoefficientMapMatrix, `missions.zeta9.formalization.CoefficientMapFormalTransportOutputs, `OutputsIndependentAssertionsV2]
