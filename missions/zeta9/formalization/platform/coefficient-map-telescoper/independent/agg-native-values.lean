import NativeValueComparisonDefinition
import Lean
open Lean Meta
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true

theorem agg_review_native_value_aggregate_eq : ZetaNine.CoefficientMapAggregateValueComparison.aggregate = ZetaNine.CoefficientMapAggregate.aggregate := rfl

theorem agg_review_native_value_coordinatePolynomial_eq : ZetaNine.CoefficientMapAggregateValueComparison.coordinatePolynomial = ZetaNine.CoefficientMapAggregate.coordinatePolynomial := rfl

theorem agg_review_native_value_polynomialCoordinates_eq : ZetaNine.CoefficientMapAggregateValueComparison.polynomialCoordinates = ZetaNine.CoefficientMapAggregate.polynomialCoordinates := rfl

theorem agg_review_native_value_aggregateLinearMap_eq : ZetaNine.CoefficientMapAggregateValueComparison.aggregateLinearMap = ZetaNine.CoefficientMapAggregate.aggregateLinearMap := rfl

theorem agg_review_native_value_coordinateLinearMap_eq : ZetaNine.CoefficientMapAggregateValueComparison.coordinateLinearMap = ZetaNine.CoefficientMapAggregate.coordinateLinearMap := rfl

theorem agg_review_native_value_quarticAggregateLinearMap_eq : ZetaNine.CoefficientMapAggregateValueComparison.quarticAggregateLinearMap = ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap := rfl

theorem agg_review_native_data_aggregate (n : Nat) (W : Polynomial Rat) :
  ZetaNine.CoefficientMapAggregateValueComparison.aggregateLinearMap n W = ZetaNine.CoefficientMapAggregate.aggregate n W := rfl

theorem agg_review_native_data_coordinate (a : Fin 5 → Rat) :
  ZetaNine.CoefficientMapAggregateValueComparison.coordinateLinearMap a = ZetaNine.CoefficientMapAggregate.coordinatePolynomial a := rfl

theorem agg_review_native_data_quartic (n : Nat) (a : Fin 5 → Rat) :
  ZetaNine.CoefficientMapAggregateValueComparison.quarticAggregateLinearMap n a = ZetaNine.CoefficientMapAggregate.aggregate n (ZetaNine.CoefficientMapAggregate.coordinatePolynomial a) := rfl

private def remapActualDataName (n : Name) : Name :=
  if n == `ZetaNine.CoefficientMapAggregate.aggregate then `ZetaNine.CoefficientMapAggregateValueComparison.aggregate
  else if n == `ZetaNine.CoefficientMapAggregate.coordinatePolynomial then `ZetaNine.CoefficientMapAggregateValueComparison.coordinatePolynomial
  else if n == `ZetaNine.CoefficientMapAggregate.polynomialCoordinates then `ZetaNine.CoefficientMapAggregateValueComparison.polynomialCoordinates
  else if n == `ZetaNine.CoefficientMapAggregate.aggregateLinearMap then `ZetaNine.CoefficientMapAggregateValueComparison.aggregateLinearMap
  else if n == `ZetaNine.CoefficientMapAggregate.coordinateLinearMap then `ZetaNine.CoefficientMapAggregateValueComparison.coordinateLinearMap
  else if n == `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap then `ZetaNine.CoefficientMapAggregateValueComparison.quarticAggregateLinearMap
  else n

run_meta do
  for (name,aliasName) in [(`ZetaNine.CoefficientMapAggregate.aggregate, `ZetaNine.CoefficientMapAggregateValueComparison.aggregate), (`ZetaNine.CoefficientMapAggregate.coordinatePolynomial, `ZetaNine.CoefficientMapAggregateValueComparison.coordinatePolynomial), (`ZetaNine.CoefficientMapAggregate.polynomialCoordinates, `ZetaNine.CoefficientMapAggregateValueComparison.polynomialCoordinates), (`ZetaNine.CoefficientMapAggregate.aggregateLinearMap, `ZetaNine.CoefficientMapAggregateValueComparison.aggregateLinearMap), (`ZetaNine.CoefficientMapAggregate.coordinateLinearMap, `ZetaNine.CoefficientMapAggregateValueComparison.coordinateLinearMap), (`ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap, `ZetaNine.CoefficientMapAggregateValueComparison.quarticAggregateLinearMap)] do
    let ci ← getConstInfo name
    let ai ← getConstInfo aliasName
    let .defnInfo d := ci | throwError "Native is not a definition"
    let .defnInfo a := ai | throwError "Alias is not a definition"
    let typeEq ← isDefEq d.type a.type
    let valueEq ← isDefEq d.value a.value
    unless typeEq && valueEq do throwError "Actual whole definition mismatch: {name}"
    let remapped := d.value.replace fun e => match e with
      | .const n ls =>
          let m := remapActualDataName n
          if m == n then none else some (.const m ls)
      | _ => none
    let typ ← ppExpr d.type
    let orig ← ppExpr d.value
    let alt ← ppExpr a.value
    let axs ← Lean.collectAxioms aliasName
    IO.println (Json.mkObj [("kind", Json.str "actual_native_whole_kernel_value"),
      ("declaration", Json.str name.toString), ("alias_declaration", Json.str aliasName.toString),
      ("type", Json.str typ.pretty), ("type_kernel_equal", toJson typeEq),
      ("full_value_kernel_equal", toJson valueEq), ("pp_proofs", toJson true),
      ("original_raw_value", Json.str orig.pretty), ("alias_raw_value", Json.str alt.pretty),
      ("original_full_expr_repr", Json.str (reprStr d.value)),
      ("alias_full_expr_repr", Json.str (reprStr a.value)),
      ("raw_expression_equal_after_data_name_remap", toJson (remapped == a.value)),
      ("axioms", toJson (axs.toList.map Name.toString))]).compress
  for name in [`agg_review_native_value_aggregate_eq, `agg_review_native_value_coordinatePolynomial_eq, `agg_review_native_value_polynomialCoordinates_eq, `agg_review_native_value_aggregateLinearMap_eq, `agg_review_native_value_coordinateLinearMap_eq, `agg_review_native_value_quarticAggregateLinearMap_eq, `agg_review_native_data_aggregate, `agg_review_native_data_coordinate, `agg_review_native_data_quartic] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("kind", Json.str "rfl_whole_or_data_equality"),
      ("declaration", Json.str name.toString), ("type", Json.str typ.pretty),
      ("axioms", toJson (axs.toList.map Name.toString))]).compress
