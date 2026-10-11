import Theorems.RefConstantV2
import Theorems.RefFiveV2
import Theorems.RefMatrixV2
import OutputsPlatformExprDagV1
import Lean
open Lean Meta IndependentLosslessExprDagV1
open scoped BigOperators Matrix
open Finset Polynomial
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapFormalTransportData
set_option maxRecDepth 20000
set_option maxHeartbeats 0
noncomputable def originalProp0 : Prop := ∀ (n : ℕ) (hn : 1 ≤ n) (r : Fin 5),
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r)
noncomputable def originalProp1 : Prop := ∀ (n : ℕ) (hn : 1 ≤ n) (r : Fin 5),
    aggregate (n + 2) (X ^ r.val) = aggregate n (connectionP n r)
noncomputable def originalProp2 : Prop := ∀ (n : ℕ) (hn : 1 ≤ n),
    actualFMatrix (n + 2) = connectionGamma n * actualFMatrix n
private def catalogType (actual expected : Name) : MetaM Unit := do
  let a ← getConstInfo actual
  let .defnInfo e ← getConstInfo expected | throwError "Expected original complete Prop definition"
  unless !(a.type.hasMVar || a.type.hasFVar || e.value.hasMVar || e.value.hasFVar) do
    throwError "Catalog type or expected full Prop not closed"
  let same ← isDefEq a.type e.value
  unless same do throwError "Catalog whole type differs from original header: {actual}"
  let axioms ← collectAxioms expected
  unless axioms.toList.all (fun n => ([`propext, `Classical.choice, `Quot.sound] : List Name).contains n) do
    throwError "Original expected Prop introduced an axiom"
  let payload ← ofExcept (persistedRoundTrip a.type e.value)
  let (rt, rv) ← ofExcept (decode payload)
  unless Expr.equal a.type rt && Expr.equal e.value rv do throwError "Catalog type DAG loss"
  IO.println (Json.mkObj [
    ("kind", Json.str "platform_author_complete_catalog_type_only"),
    ("declaration", Json.str actual.toString), ("expected_original_full_Prop", Json.str expected.toString),
    ("whole_type_kernel_equal", toJson same), ("closed_complete_types", toJson true),
    ("all_fields_roundtrip", toJson true), ("type_Expr_equal_diagnostic", toJson (Expr.equal a.type e.value)),
    ("actual_catalog_full_type_raw_Expr", Json.str (reprStr a.type)),
    ("expected_original_full_type_raw_Expr", Json.str (reprStr e.value)),
    ("complete_catalog_type_and_expected_Prop_dag", payload),
    ("catalog_proof_value_read_or_used", toJson false),
    ("catalog_proof_or_Std3_PASS_claimed", toJson false)]).compress
run_meta do
  catalogType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_constantTerm_transport `originalProp0
  catalogType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_chosen_five_output_transport `originalProp1
  catalogType `ZetaNine.CoefficientMapFormalTransportOutputs.actual_five_output_matrix_transport `originalProp2
