import NativeKernelValueComparisonDefinition
import Lean

open Lean Meta
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true

theorem native_kernel_value_positiveProduct_eq : ZetaNine.CoefficientMapKernelBridgeValueComparison.positiveProduct = ZetaNine.CoefficientMapKernelBridge.positiveProduct := rfl

theorem native_kernel_value_negativeProduct_eq : ZetaNine.CoefficientMapKernelBridgeValueComparison.negativeProduct = ZetaNine.CoefficientMapKernelBridge.negativeProduct := rfl

theorem native_kernel_value_aValue_eq : ZetaNine.CoefficientMapKernelBridgeValueComparison.aValue = ZetaNine.CoefficientMapKernelBridge.aValue := rfl

theorem native_kernel_value_bValue_eq : ZetaNine.CoefficientMapKernelBridgeValueComparison.bValue = ZetaNine.CoefficientMapKernelBridge.bValue := rfl

theorem native_kernel_value_actualAggregateEquiv_eq : ZetaNine.CoefficientMapKernelBridgeValueComparison.actualAggregateEquiv = ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv := rfl

theorem native_kernel_value_inverseMultiplier_eq : ZetaNine.CoefficientMapKernelBridgeValueComparison.inverseMultiplier = ZetaNine.CoefficientMapKernelBridge.inverseMultiplier := rfl

theorem native_kernel_value_prescribedL_eq : ZetaNine.CoefficientMapKernelBridgeValueComparison.prescribedL = ZetaNine.CoefficientMapKernelBridge.prescribedL := rfl

run_meta do
  for (name, aliasName) in [(`ZetaNine.CoefficientMapKernelBridge.positiveProduct, `ZetaNine.CoefficientMapKernelBridgeValueComparison.positiveProduct), (`ZetaNine.CoefficientMapKernelBridge.negativeProduct, `ZetaNine.CoefficientMapKernelBridgeValueComparison.negativeProduct), (`ZetaNine.CoefficientMapKernelBridge.aValue, `ZetaNine.CoefficientMapKernelBridgeValueComparison.aValue), (`ZetaNine.CoefficientMapKernelBridge.bValue, `ZetaNine.CoefficientMapKernelBridgeValueComparison.bValue), (`ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv, `ZetaNine.CoefficientMapKernelBridgeValueComparison.actualAggregateEquiv), (`ZetaNine.CoefficientMapKernelBridge.inverseMultiplier, `ZetaNine.CoefficientMapKernelBridgeValueComparison.inverseMultiplier), (`ZetaNine.CoefficientMapKernelBridge.prescribedL, `ZetaNine.CoefficientMapKernelBridgeValueComparison.prescribedL)] do
    let ci ← getConstInfo name
    let ai ← getConstInfo aliasName
    let .defnInfo d := ci | throwError "Original is not a definition"
    let .defnInfo a := ai | throwError "Comparison is not a definition"
    let typeEq ← isDefEq d.type a.type
    let valueEq ← isDefEq d.value a.value
    unless typeEq && valueEq do throwError "Original/comparison definition mismatch: {name}"
    let nt ← ppExpr d.type
    let nv ← ppExpr d.value
    let av ← ppExpr a.value
    let axs ← Lean.collectAxioms aliasName
    IO.println (Json.mkObj [("kind", Json.str "kernel_definition_value"),
      ("declaration", Json.str name.toString), ("alias_declaration", Json.str aliasName.toString),
      ("type", Json.str nt.pretty), ("type_kernel_equal", toJson typeEq),
      ("full_value_kernel_equal", toJson valueEq),
      ("pp_proofs_enabled", toJson true),
      ("original_expression_repr", Json.str (reprStr d.value)),
      ("comparison_expression_repr", Json.str (reprStr a.value)),
      ("original_raw_value", Json.str nv.pretty), ("comparison_raw_value", Json.str av.pretty),
      ("axioms", toJson (axs.toList.map Name.toString))]).compress
  for name in [`native_kernel_value_positiveProduct_eq, `native_kernel_value_negativeProduct_eq, `native_kernel_value_aValue_eq, `native_kernel_value_bValue_eq, `native_kernel_value_actualAggregateEquiv_eq, `native_kernel_value_inverseMultiplier_eq, `native_kernel_value_prescribedL_eq] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("kind", Json.str "rfl_or_data_equality"),
      ("declaration", Json.str name.toString), ("type", Json.str typ.pretty),
      ("axioms", toJson (axs.toList.map Name.toString))]).compress

run_meta do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut records : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let some m := modules[idx.toNat]? | continue
    unless m == `missions.zeta9.formalization.CoefficientMapKernelBridge || m == `Definitions.Def_ZetaNine_CoefficientMapKernelBridge do continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | _ => "other"
    let range ← findDeclarationRanges? n
    let line := match range with | some r => r.range.pos.line | none => 0
    records := records.push (Json.mkObj [("name", toJson n.toString),("module", toJson m.toString),("kind", toJson kind),("startLine", toJson line)])
  let context := if (env.find? `ZetaNine.CoefficientMapKernelBridge.original_five_dimensional_map_bijective).isSome then "native" else "staged"
  IO.FS.writeFile ("../kernel-" ++ context ++ "-global-declarations.json") ((toJson records).compress)
