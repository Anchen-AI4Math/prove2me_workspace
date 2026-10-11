import StagedValueComparisonDefinition
import Lean

open Lean Meta
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true

theorem native_value_connectionU_eq : ZetaNine.CoefficientMapConnectionValueComparison.connectionU = ZetaNine.CoefficientMapConnection.connectionU := rfl

theorem native_value_connectionV_eq : ZetaNine.CoefficientMapConnectionValueComparison.connectionV = ZetaNine.CoefficientMapConnection.connectionV := rfl

theorem native_value_connectionD_eq : ZetaNine.CoefficientMapConnectionValueComparison.connectionD = ZetaNine.CoefficientMapConnection.connectionD := rfl

theorem native_value_connectionH_eq : ZetaNine.CoefficientMapConnectionValueComparison.connectionH = ZetaNine.CoefficientMapConnection.connectionH := rfl

theorem native_value_connectionReflection_eq : ZetaNine.CoefficientMapConnectionValueComparison.connectionReflection = ZetaNine.CoefficientMapConnection.connectionReflection := rfl

theorem native_value_coefficientPolynomial_eq : ZetaNine.CoefficientMapConnectionValueComparison.coefficientPolynomial = ZetaNine.CoefficientMapConnection.coefficientPolynomial := rfl

theorem native_value_inputP_eq : ZetaNine.CoefficientMapConnectionValueComparison.inputP = ZetaNine.CoefficientMapConnection.inputP := rfl

theorem native_value_inputQ_eq : ZetaNine.CoefficientMapConnectionValueComparison.inputQ = ZetaNine.CoefficientMapConnection.inputQ := rfl

theorem native_value_connectionOperator_eq : ZetaNine.CoefficientMapConnectionValueComparison.connectionOperator = ZetaNine.CoefficientMapConnection.connectionOperator := rfl

theorem native_value_connectionLinearMap_eq : ZetaNine.CoefficientMapConnectionValueComparison.connectionLinearMap = ZetaNine.CoefficientMapConnection.connectionLinearMap := rfl

theorem native_value_connectionZ_eq : ZetaNine.CoefficientMapConnectionValueComparison.connectionZ = ZetaNine.CoefficientMapConnection.connectionZ := rfl

theorem native_value_connectionTarget_eq : ZetaNine.CoefficientMapConnectionValueComparison.connectionTarget = ZetaNine.CoefficientMapConnection.connectionTarget := rfl

theorem native_data_connectionLinearMap (n : Nat) (c : Fin 15 → Rat) (i : Fin 15) :
  ZetaNine.CoefficientMapConnectionValueComparison.connectionLinearMap n c i = (ZetaNine.CoefficientMapConnection.connectionOperator n (ZetaNine.CoefficientMapConnection.inputP c) (ZetaNine.CoefficientMapConnection.inputQ c)).coeff (2 * i.val) := rfl

run_meta do
  for (name,aliasName) in [(`ZetaNine.CoefficientMapConnection.connectionU, `ZetaNine.CoefficientMapConnectionValueComparison.connectionU), (`ZetaNine.CoefficientMapConnection.connectionV, `ZetaNine.CoefficientMapConnectionValueComparison.connectionV), (`ZetaNine.CoefficientMapConnection.connectionD, `ZetaNine.CoefficientMapConnectionValueComparison.connectionD), (`ZetaNine.CoefficientMapConnection.connectionH, `ZetaNine.CoefficientMapConnectionValueComparison.connectionH), (`ZetaNine.CoefficientMapConnection.connectionReflection, `ZetaNine.CoefficientMapConnectionValueComparison.connectionReflection), (`ZetaNine.CoefficientMapConnection.coefficientPolynomial, `ZetaNine.CoefficientMapConnectionValueComparison.coefficientPolynomial), (`ZetaNine.CoefficientMapConnection.inputP, `ZetaNine.CoefficientMapConnectionValueComparison.inputP), (`ZetaNine.CoefficientMapConnection.inputQ, `ZetaNine.CoefficientMapConnectionValueComparison.inputQ), (`ZetaNine.CoefficientMapConnection.connectionOperator, `ZetaNine.CoefficientMapConnectionValueComparison.connectionOperator), (`ZetaNine.CoefficientMapConnection.connectionLinearMap, `ZetaNine.CoefficientMapConnectionValueComparison.connectionLinearMap), (`ZetaNine.CoefficientMapConnection.connectionZ, `ZetaNine.CoefficientMapConnectionValueComparison.connectionZ), (`ZetaNine.CoefficientMapConnection.connectionTarget, `ZetaNine.CoefficientMapConnectionValueComparison.connectionTarget)] do
    let .defnInfo d ← getConstInfo name | throwError "Native constant is not a def"
    let .defnInfo a ← getConstInfo aliasName | throwError "Alias constant is not a def"
    let typeEq ← isDefEq d.type a.type
    let valueEq ← isDefEq d.value a.value
    unless typeEq && valueEq do throwError "Actual native/alias whole definition differs: {name}"
    let nv ← ppExpr d.value
    let av ← ppExpr a.value
    let axs ← Lean.collectAxioms aliasName
    IO.println (Json.mkObj [("kind",Json.str "native_alias_full_kernel_equality"),
      ("declaration",Json.str name.toString),("alias_declaration",Json.str aliasName.toString),
      ("type_kernel_equal",toJson typeEq),("full_value_kernel_equal",toJson valueEq),
      ("original_expression_repr",Json.str (reprStr d.value)),
      ("alias_expression_repr",Json.str (reprStr a.value)),
      ("original_value_pp_with_proofs",Json.str nv.pretty),
      ("alias_value_pp_with_proofs",Json.str av.pretty),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  for name in [`native_value_connectionU_eq, `native_value_connectionV_eq, `native_value_connectionD_eq, `native_value_connectionH_eq, `native_value_connectionReflection_eq, `native_value_coefficientPolynomial_eq, `native_value_inputP_eq, `native_value_inputQ_eq, `native_value_connectionOperator_eq, `native_value_connectionLinearMap_eq, `native_value_connectionZ_eq, `native_value_connectionTarget_eq, `native_data_connectionLinearMap] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("kind",Json.str "rfl_or_data_equality"),
      ("declaration",Json.str name.toString),("type",Json.str typ.pretty),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
