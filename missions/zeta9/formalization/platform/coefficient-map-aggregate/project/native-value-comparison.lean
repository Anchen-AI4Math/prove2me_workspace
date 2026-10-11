import NativeValueComparisonDefinition
import Lean

open Lean Meta
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false

theorem native_value_aggregate_eq : ZetaNine.CoefficientMapAggregateValueComparison.aggregate = ZetaNine.CoefficientMapAggregate.aggregate := rfl

theorem native_value_coordinatePolynomial_eq : ZetaNine.CoefficientMapAggregateValueComparison.coordinatePolynomial = ZetaNine.CoefficientMapAggregate.coordinatePolynomial := rfl

theorem native_value_polynomialCoordinates_eq : ZetaNine.CoefficientMapAggregateValueComparison.polynomialCoordinates = ZetaNine.CoefficientMapAggregate.polynomialCoordinates := rfl

theorem native_value_aggregateLinearMap_eq : ZetaNine.CoefficientMapAggregateValueComparison.aggregateLinearMap = ZetaNine.CoefficientMapAggregate.aggregateLinearMap := rfl

theorem native_value_coordinateLinearMap_eq : ZetaNine.CoefficientMapAggregateValueComparison.coordinateLinearMap = ZetaNine.CoefficientMapAggregate.coordinateLinearMap := rfl

theorem native_value_quarticAggregateLinearMap_eq : ZetaNine.CoefficientMapAggregateValueComparison.quarticAggregateLinearMap = ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap := rfl

theorem native_data_aggregateLinearMap (n : Nat) (W : Polynomial Rat) :
  ZetaNine.CoefficientMapAggregateValueComparison.aggregateLinearMap n W = ZetaNine.CoefficientMapAggregate.aggregate n W := rfl

theorem native_data_coordinateLinearMap (a : Fin 5 → Rat) :
  ZetaNine.CoefficientMapAggregateValueComparison.coordinateLinearMap a = ZetaNine.CoefficientMapAggregate.coordinatePolynomial a := rfl

theorem native_data_quarticAggregateLinearMap (n : Nat) (a : Fin 5 → Rat) :
  ZetaNine.CoefficientMapAggregateValueComparison.quarticAggregateLinearMap n a = ZetaNine.CoefficientMapAggregate.aggregate n (ZetaNine.CoefficientMapAggregate.coordinatePolynomial a) := rfl

run_meta do
  for (name, aliasName) in [(`ZetaNine.CoefficientMapAggregate.aggregate, `ZetaNine.CoefficientMapAggregateValueComparison.aggregate), (`ZetaNine.CoefficientMapAggregate.coordinatePolynomial, `ZetaNine.CoefficientMapAggregateValueComparison.coordinatePolynomial), (`ZetaNine.CoefficientMapAggregate.polynomialCoordinates, `ZetaNine.CoefficientMapAggregateValueComparison.polynomialCoordinates), (`ZetaNine.CoefficientMapAggregate.aggregateLinearMap, `ZetaNine.CoefficientMapAggregateValueComparison.aggregateLinearMap), (`ZetaNine.CoefficientMapAggregate.coordinateLinearMap, `ZetaNine.CoefficientMapAggregateValueComparison.coordinateLinearMap), (`ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap, `ZetaNine.CoefficientMapAggregateValueComparison.quarticAggregateLinearMap)] do
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
      ("original_raw_value", Json.str nv.pretty), ("comparison_raw_value", Json.str av.pretty),
      ("axioms", toJson (axs.toList.map Name.toString))]).compress
  for name in [`native_value_aggregate_eq, `native_value_coordinatePolynomial_eq, `native_value_polynomialCoordinates_eq, `native_value_aggregateLinearMap_eq, `native_value_coordinateLinearMap_eq, `native_value_quarticAggregateLinearMap_eq, `native_data_aggregateLinearMap, `native_data_coordinateLinearMap, `native_data_quarticAggregateLinearMap] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("kind", Json.str "rfl_or_data_equality"),
      ("declaration", Json.str name.toString), ("type", Json.str typ.pretty),
      ("axioms", toJson (axs.toList.map Name.toString))]).compress
