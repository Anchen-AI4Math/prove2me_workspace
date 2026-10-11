"""Prepare complete catalog types against the three original native headers."""
import initialize_author as p

RECORDER = r'''
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
{expected}
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
{calls}
'''


def main():
    ctx = p.PROJECT / "r"
    target = ctx / "OutputsPlatformExprDagV1.lean"
    p.write(target, (p.PROJECT / "d/OutputsPlatformExprDagV1.lean").read_bytes())
    expected, calls = [], []
    for index, target_plan in enumerate(p.load(p.OUT / "target-plan.json")["targets"]):
        head = target_plan["exact_original_header"]
        binder_part, body = head.split(" :\n", 1)
        binders = binder_part.split(" ", 2)[2]
        expected.append("noncomputable def originalProp" + str(index) + " : Prop := ∀ " + binders + ",\n" + body)
        calls.append("  catalogType `" + target_plan["theorem_name"] + " `originalProp" + str(index))
    source = RECORDER.replace("{expected}", "\n".join(expected)).replace("{calls}", "\n".join(calls)).lstrip("\n")
    destination = ctx / "OutputsPlatformReferenceTypesV1.lean"
    p.write(destination, source)
    p.dump(p.OUT / "author-reference-type-control-preparation-v1.json", {
        "rows": [{"module": "OutputsPlatformExprDagV1", "path": target.name, "binding": p.bind(target)},
                 {"module": "OutputsPlatformReferenceTypesV1", "path": destination.name, "binding": p.bind(destination)}],
        "all_three_complete_catalog_types_vs_original_full_headers": True,
        "catalog_proof_values_never_read_or_used": True, "Lean_calls_in_preparation": 0,
        "API_calls": 0, "foreign_proof_objects_reused": False})
    print("Prepared two own SOURCE controls; catalogs remain type-only")


if __name__ == "__main__":
    main()
