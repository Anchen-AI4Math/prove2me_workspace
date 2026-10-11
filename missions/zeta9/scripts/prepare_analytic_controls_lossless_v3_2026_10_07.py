"""Append SOURCE-only lossless DAG audit controls; no Lean calls or object imports."""
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
OUT = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"
PROJECT = OUT / ".rt/afb1"
DEST = PROJECT / "private-controls/v3/src"


def binding(p):
    data = p.read_bytes()
    return {"task_relative": p.relative_to(TASK).as_posix(), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def write_new(p, text):
    assert not p.exists(), p
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")


RECORD = '''private def afRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let some value := ci.value? true | throwError "Missing complete proof/definition value: {n}"
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type value)
  let (rt,rv) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  let exactType := Expr.equal ci.type rt
  let exactValue := Expr.equal value rv
  unless exactType && exactValue do throwError "Full-field Expr DAG changed an expression: {n}"
  let typeKernel ← isDefEq ci.type rt
  let valueKernel ← isDefEq value rv
  let typed ← isDefEq (← inferType rv) ci.type
  unless typeKernel && valueKernel && typed do
    throwError "Complete reconstructed proof/value does not have its exact complete type: {n}"
  afEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",toJson payload.compress),
    ("value_raw_format",toJson "lossless lean-expr-dag-v1; full type_root and value_root"),
    ("all_fields_type_Expr_equal",toJson exactType),("all_fields_value_Expr_equal",toJson exactValue),
    ("full_type_kernel_equal",toJson typeKernel),("full_value_kernel_equal",toJson valueKernel),
    ("value_type_isDefEq",toJson typed),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← afAxioms n)]
'''


def main():
    core_source = TASK / ".rt/api1/APIPhaseExprDagV1.lean"
    fixture_source = TASK / ".rt/api1/APIPhaseExprDagValidationV1.lean"
    core_target = DEST / "AFExprDag.lean"
    fixture_target = DEST / "AFExprDagValidation.lean"
    write_new(core_target, core_source.read_text(encoding="utf-8"))
    fixtures = fixture_source.read_text(encoding="utf-8")
    fixtures = fixtures.replace("import APIPhaseExprDagV1", "import AFExprDag")
    fixtures = fixtures.replace("import missions.zeta9.formalization.AnalyticPhaseUpperBound", "import AnalyticPhaseUpperBound")
    write_new(fixture_target, fixtures)
    copied = [{"module": "AFExprDag", "source": binding(core_source), "own_source_copy": binding(core_target)},
              {"module": "AFExprDagValidation", "source": binding(fixture_source), "own_source_copy": binding(fixture_target)}]
    controls = []
    for module in ("AFTypes", "AFKernel", "AFBoundary", "AFResolver"):
        source = PROJECT / "private-controls/v2/src" / (module + ".lean")
        text = source.read_text(encoding="utf-8")
        if module != "AFResolver":
            assert text.count('  liftM <| IO.println ("AF_RECORD|" ++ j.compress)') == 1
            text = text.replace('  liftM <| IO.println ("AF_RECORD|" ++ j.compress)',
                                '  liftM <| do\n    let stdout ← IO.getStdout\n    stdout.putStrLn ("AF_RECORD|" ++ j.compress)\n    stdout.flush')
            start = text.index("private def afRecord ")
            end = text.index("\n\n", text.index('("isProp",', start))
            text = text[:start] + RECORD.rstrip() + text[end:]
            text = "import AFExprDag\n" + text
        if module == "AFKernel":
            # Whole definition bodies are small. Compiler proof-helper bodies use the same
            # complete round-trip lossless serializer to avoid shared-tree expansion.
            text = text.replace('(\"value_actual_raw\",toJson (reprStr va)),(\"value_expected_raw\",toJson (reprStr vb)),',
                                '(\"value_actual_raw\",← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type va)),(\"value_expected_raw\",← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type vb)),')
        target = DEST / (module + ".lean")
        write_new(target, text)
        controls.append({"module": module, "original_control_v2": binding(source), "private_control_v3": binding(target)})
    report = {"status": "PURE_SOURCE_LOSSLESS_DAG_CONTROLS_PREPARATION",
              "reason": "Actual AFTypes call22 tree repr exhausted memory; retain all constructor fields through lossless DAG and strict reconstruction",
              "actual_lean_calls": 0, "foreign_objects_copied": 0,
              "source_only_serializer_copies": copied, "controls": controls,
              "complete_70_types_29_definitions_15_boundaries_11_inventories_preserved": True,
              "all_Expr_constructor_Name_Level_BinderInfo_Literal_MData_Syntax_fields_retained": True,
              "actual_lossless_fixture_and_kernel_checks_pending": True,
              "failure_calls_21_and_22_retained": True}
    path = OUT / "private-controls-lossless-v3-preparation.json"
    write_new(path, json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "report": binding(path)}))


if __name__ == "__main__":
    main()
