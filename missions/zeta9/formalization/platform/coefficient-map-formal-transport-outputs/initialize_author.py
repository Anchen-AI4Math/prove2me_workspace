"""Initialize fresh isolated author SOURCE contexts after the explicit lane grant."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
PROJECT = TASK / ".rt/opfa1"


def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def sha(path):
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def bind(path):
    path = path.resolve()
    row = {"bytes": path.stat().st_size, "sha256": sha(path)}
    if path.is_relative_to(TASK.resolve()):
        row["task_relative"] = path.relative_to(TASK.resolve()).as_posix()
    elif path.is_relative_to(ROOT.resolve()):
        row["root_relative"] = path.relative_to(ROOT.resolve()).as_posix()
    else:
        row["absolute_path"] = str(path)
    return row


def resolve(row):
    if row.get("task_relative"):
        return TASK / row["task_relative"]
    if row.get("root_relative"):
        return ROOT / row["root_relative"]
    return Path(row["absolute_path"])


def check(rows):
    for row in rows:
        path = resolve(row)
        assert path.stat().st_size == row["bytes"] and sha(path) == row["sha256"], str(path)


def write(path, data):
    assert not path.exists(), "Preserve existing context/source: " + str(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data if isinstance(data, bytes) else data.encode("utf-8"))


def dump(path, value):
    write(path, json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    grant_path = OUT / "Root-platform-author-lane2-grant.json"
    grant = load(grant_path)
    assert grant["Root_explicit_grant"] is True and grant["lane"] == 2 and grant["serial_lean_j1_only"] is True
    handoff = OUT / "pure-source-handoff.json"
    assert sha(handoff) == grant["frozen_SOURCE_handoff_sha256"] == "54def136ec9b9025097dc6e43a1ac9047d06f86df1a600dcca579d48b5380728"
    check(load(handoff)["stable_files"])
    assert not PROJECT.exists()
    prep, plan = load(OUT / "source-preparation.json"), load(OUT / "target-plan.json")
    assert len(prep["native_SOURCE_closure"]) == 21
    template = TASK / ".rt/apfa1/native/lean_call.py"
    wrapper = template.read_bytes().replace(b"PHASE_PLATFORM_PATH_RECEIPT", b"OUTPUTS_PLATFORM_PATH_RECEIPT")
    dag = TASK / ".rt/apfa1/right/PhasePlatformExprDagV1.lean"
    dag_validation = TASK / ".rt/apfa1/right/PhasePlatformExprDagValidationV1.lean"
    dag_source = dag.read_bytes()
    assert dag_source.decode("utf-8").replace("\r\n", "\n").startswith("import Lean\n") and b"CoefficientMap" not in dag_source
    fixture = dag_validation.read_text(encoding="utf-8")
    fixture = fixture.replace("import PhasePlatformExprDagV1", "import OutputsPlatformExprDagV1")
    fixture = fixture.replace("import Definitions.Def_ZetaNine_AnalyticPhase", "import Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs")
    fixture = fixture.replace('"ZetaNine.AnalyticPhase.phaseRatio"', '"ZetaNine.CoefficientMapParameterShift.parameterScale"')
    fixture = fixture.replace('"ZetaNine.AnalyticPhase.phaseSlope"', '"ZetaNine.CoefficientMapFormalTransportData.remainderNumerator"')
    fixture = fixture.replace('"ZetaNine.AnalyticPhase.smoothPhaseRatio"', '"ZetaNine.CoefficientMapFormalTransportData.connectionGamma"')
    fixture = fixture.replace("PHASE DAG", "OUTPUTS PLATFORM DAG")
    contexts = []
    renames = {row["module"]: "Oracle." + ("HarmonicStability" if row["module"].startswith("Definitions.") else row["module"].rsplit(".", 1)[-1]) for row in prep["native_SOURCE_closure"]}
    PROJECT.mkdir()
    for tag in ["n", "d", "r", "c", "f", "m"]:
        ctx = PROJECT / tag
        ctx.mkdir()
        root_module = "missions.zeta9.formalization.CoefficientMapFormalTransportOutputs" if tag == "n" else "Definitions.Def_ZetaNine_CoefficientMapFormalTransportOutputs"
        write(ctx / "lakefile.toml", 'name = "outputsPlatformAuthor_' + tag + '"\nbuildDir = "b"\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "' + plan["Mathlib_ENV"] + '"\n[[lean_lib]]\nname = "Outputs"\nroots = ["' + root_module + '"]\n')
        for name in ["lean-toolchain", "lake-manifest.json"]:
            write(ctx / name, (ROOT / name).read_bytes())
        assert (ctx / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.1"
        assert next(p for p in load(ctx / "lake-manifest.json")["packages"] if p["name"] == "mathlib")["rev"] == plan["Mathlib_ENV"]
        write(ctx / "lean_call.py", wrapper)
        rows = []
        if tag == "n":
            for item in prep["native_SOURCE_closure"]:
                source = resolve(item["own_snapshot"])
                check([item["own_snapshot"]])
                rel = item["future_native_project_path"]
                write(ctx / rel, source.read_bytes())
                rows.append({"kind": "complete_native_SOURCE", "module": item["module"], "path": rel, "binding": bind(ctx / rel)})
        else:
            for item in plan["existing_definitions"]:
                source = resolve(item)
                check([item])
                rel = item["module"].replace(".", "/") + ".lean"
                write(ctx / rel, source.read_bytes())
                rows.append({"kind": "canonical_definition_SOURCE_only", "module": item["module"], "path": rel, "binding": bind(ctx / rel)})
            rel = plan["local_definition"]
            write(ctx / rel, (OUT / "staged" / rel).read_bytes())
            rows.append({"kind": "actual_new_definition_candidate", "module": rel[:-5].replace("/", "."), "path": rel, "binding": bind(ctx / rel)})
            if tag == "r":
                for target in plan["targets"]:
                    rel = target["local_reference"]
                    write(ctx / rel, (OUT / "staged" / rel).read_bytes())
                    rows.append({"kind": "catalog_type_only_never_proof", "module": rel[:-5].replace("/", "."), "path": rel, "binding": bind(ctx / rel)})
            else:
                for item in prep["native_SOURCE_closure"]:
                    source = resolve(item["own_snapshot"]).read_text(encoding="utf-8-sig")
                    for old, new in renames.items():
                        source = source.replace("import " + old + "\n", "import " + new + "\n")
                    source = source.replace("ZetaNine", "OutputsPlatformOracle")
                    module = renames[item["module"]]
                    rel = module.replace(".", "/") + ".lean"
                    write(ctx / rel, source)
                    rows.append({"kind": "own_full_SOURCE_oracle_namespace_only", "module": module, "path": rel, "binding": bind(ctx / rel)})
                if tag in ["c", "f", "m"]:
                    index = ["c", "f", "m"].index(tag)
                    rel = plan["targets"][index]["local_solution"]
                    write(ctx / rel, (OUT / "staged" / rel).read_bytes())
                    rows.append({"kind": "complete_solution_all380_proof_SOURCE_candidate", "module": rel[:-5].replace("/", "."), "path": rel, "binding": bind(ctx / rel)})
                for module, source in [("OutputsPlatformExprDagV1", dag_source), ("OutputsPlatformExprDagValidationV1", fixture)]:
                    rel = module + ".lean"
                    write(ctx / rel, source)
                    rows.append({"kind": "generic_lossless_recorder_SOURCE_no_math_object_reuse", "module": module, "path": rel, "binding": bind(ctx / rel)})
        contexts.append({"tag": tag, "task_relative": ctx.relative_to(TASK).as_posix(), "initially_absent": True, "math_sources": rows})
    stable = [bind(p) for p in sorted(PROJECT.rglob("*")) if p.is_file()]
    dump(OUT / "author-context-preparation.json", {"prepared_at": datetime.now(timezone.utc).isoformat(), "Root_lane2_grant": bind(grant_path),
         "frozen_SOURCE_handoff": bind(handoff), "fresh_project_initially_absent": True, "contexts": contexts, "stable_files": stable,
         "own_oracle_21_source_namespace_import_rename_only": True, "raw_Expr_namespace_differences_must_be_retained": True,
         "dag_generic_SOURCE_reuse": {"core": bind(dag), "fixtures": bind(dag_validation), "wrapper": bind(template)},
         "foreign_math_proof_objects_copied": False, "Lean_calls_in_initialization": 0, "API_calls": 0, "credentials_reads": 0})
    print(json.dumps({"fresh_project": str(PROJECT), "contexts": len(contexts), "SOURCE_inputs": len(stable), "Lean_calls": 0,
                      "preparation_sha256": sha(OUT / "author-context-preparation.json")}, indent=2))


if __name__ == "__main__":
    main()
