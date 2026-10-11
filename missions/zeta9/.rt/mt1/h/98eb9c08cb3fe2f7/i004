import StagedValueComparisonDefinition
import Lean
open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
theorem native_value_actualFMatrix_eq : ZetaNine.CoefficientMapMatrixValueComparison.actualFMatrix = ZetaNine.CoefficientMapMatrix.actualFMatrix := rfl
theorem native_value_selectionMatrix_eq : ZetaNine.CoefficientMapMatrixValueComparison.selectionMatrix = ZetaNine.CoefficientMapMatrix.selectionMatrix := rfl
theorem native_value_selectedIntegerPair_eq : ZetaNine.CoefficientMapMatrixValueComparison.selectedIntegerPair = ZetaNine.CoefficientMapMatrix.selectedIntegerPair := rfl
theorem native_value_selectedIntegerOutput_eq : ZetaNine.CoefficientMapMatrixValueComparison.selectedIntegerOutput = ZetaNine.CoefficientMapMatrix.selectedIntegerOutput := rfl
theorem native_value_selectedIntegerMultiplier_eq : ZetaNine.CoefficientMapMatrixValueComparison.selectedIntegerMultiplier = ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier := rfl

run_meta do
  for (name,aliasName) in [(`ZetaNine.CoefficientMapMatrix.actualFMatrix, `ZetaNine.CoefficientMapMatrixValueComparison.actualFMatrix), (`ZetaNine.CoefficientMapMatrix.selectionMatrix, `ZetaNine.CoefficientMapMatrixValueComparison.selectionMatrix), (`ZetaNine.CoefficientMapMatrix.selectedIntegerPair, `ZetaNine.CoefficientMapMatrixValueComparison.selectedIntegerPair), (`ZetaNine.CoefficientMapMatrix.selectedIntegerOutput, `ZetaNine.CoefficientMapMatrixValueComparison.selectedIntegerOutput), (`ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier, `ZetaNine.CoefficientMapMatrixValueComparison.selectedIntegerMultiplier)] do
    let .defnInfo d ← getConstInfo name | throwError "Original is not a Definition"
    let .defnInfo a ← getConstInfo aliasName | throwError "Alias is not a Definition"
    let te ← isDefEq d.type a.type
    let ve ← isDefEq d.value a.value
    unless te && ve do throwError "Whole Matrix Definition differs: {name}"
    let axs ← Lean.collectAxioms aliasName
    IO.println (Json.mkObj [("kind",Json.str "whole_definition_kernel_equality"),
      ("declaration",Json.str name.toString),("type_kernel_equal",toJson te),
      ("full_value_kernel_equal",toJson ve),("original_type_expression_repr",Json.str (reprStr d.type)),
      ("alias_type_expression_repr",Json.str (reprStr a.type)),
      ("original_value_expression_repr",Json.str (reprStr d.value)),
      ("alias_value_expression_repr",Json.str (reprStr a.value)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  for name in [`native_value_actualFMatrix_eq, `native_value_selectionMatrix_eq, `native_value_selectedIntegerPair_eq, `native_value_selectedIntegerOutput_eq, `native_value_selectedIntegerMultiplier_eq] do
    let ci ← getConstInfo name
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("kind",Json.str "whole_function_rfl"),("declaration",Json.str name.toString),
      ("type_expression_repr",Json.str (reprStr ci.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
