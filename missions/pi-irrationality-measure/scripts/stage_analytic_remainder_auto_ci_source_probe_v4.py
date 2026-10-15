"""Pure additional source-only AP19 metadata probe for two observed auto CIs.

The original three four-Def preflights are immutable and reused. This script
only stages one bounded source Meta snapshot; Root alone may compile it.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import stage_analytic_remainder_data_provider as base


TASK, ROOT, V = base.TASK, base.ROOT, base.V
SELF = Path(__file__).resolve()
STAGE = V / "ap19/analytic-remainder-auto-ci-source-v4"
OUTPUT = "SourceAutomaticSnapshot.lean"
SOURCE_JSON = "source-automatic-ci.json"
MANIFEST = "c4.json"
CERTIFICATE = "actual-provider-validation-auto-ci-v5.json"
CONSUMER = TASK / "scripts/certify_analytic_remainder_data_auto_ci_v5.py"
TYPE_CORE = V / "TypeOnlyTheoremSnapshotCore.inc"
RUNTIME = V / "lean-runtime.json"
RUNNER = TASK / "scripts/preflight_staged_module_windows_bounded.py"
SOURCE_MODULE = "OAI.NumberTheory.PiExponent.Analysis.CollisionExponential"
SOURCE_FILE = TASK / ("port/lean/" + SOURCE_MODULE.replace(".", "/") + ".lean")
EXPECTED_AUTO_NAMES = [
    "OAI.PiExponent.Collision.collisionRatio._proof_1",
    "OAI.PiExponent.Collision.collisionRemainder._proof_1",
]
PYTHON = "C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe"
need, read, sha, digest, encode, rel, workspace_rel = (
    base.need, base.read, base.sha, base.sha_bytes, base.encode, base.rel, base.workspace_rel)


def actual_auto_names():
    inventory_path = base.STAGE / base.INVENTORY_JSON
    inventory = read(inventory_path)
    rows = inventory["rawOwnedCIs"]
    names = sorted(r["name"] for r in rows if r["kind"] == "theorem")
    need(names == sorted(EXPECTED_AUTO_NAMES)
         and len(rows) == 6
         and sorted(r["name"] for r in rows if r["kind"] == "def") == sorted(base.NAMES),
         "Actual generated full owned-CI inventory does not show exactly four original Defs and two observed auto CIs")
    for r in rows:
        if r["name"] in names:
            need(r["isProp"] is True and r["closedType"] is True
                 and r["closedValue"] is True and r["axioms"] == ["propext"]
                 and r["owner"] == base.PLATFORM_MODULE and r["privateUserName"] is None,
                 "Observed generated automatic CI is not a closed public Prop theorem")
    return names


PROBE = r'''
namespace AnalyticRemainderSourceAutomaticProbe
open Lean Meta
def exportAutomaticCIs (names : Array Name) (owner output : String) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for name in names do
    let some ci := env.find? name | throwError "Missing genuine source automatic CI: {name}"
    let .thmInfo thm := ci | throwError "Expected original source theorem CI: {name}"
    let actualOwner ← match env.getModuleIdxFor? name with
      | none => pure env.mainModule.toString
      | some idx => do
        let some m := env.header.moduleNames[idx.toNat]? | throwError "Invalid source auto-CI owner"
        pure m.toString
    unless actualOwner == owner do throwError "Original automatic CI owner differs: {name}"
    unless ← isProp ci.type do throwError "Source automatic CI is not Prop: {name}"
    if ci.type.hasMVar || ci.type.hasFVar || thm.value.hasMVar || thm.value.hasFVar then
      throwError "Unclosed original automatic CI: {name}"
    let ax := ((← Lean.collectAxioms name).map Name.toString).qsort (· < ·)
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("actualOwner", toJson actualOwner),
      ("privateUserName", toJson ((Lean.privateToUserName? name).map Name.toString)),
      ("kind", toJson "theorem"), ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", PiExponentInterfaceSnapshot.exprJson ci.type), ("value", Json.null),
      ("closedType", toJson true), ("closedValue", toJson true), ("isProp", toJson true),
      ("typeRefs", toJson ((ci.type.getUsedConstants.map Name.toString).qsort (· < ·))),
      ("valueRefs", toJson ((thm.value.getUsedConstants.map Name.toString).qsort (· < ·))),
      ("axioms", toJson ax)]
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("probeMainModule", toJson env.mainModule.toString),
    ("sourceModule", toJson owner), ("rawSourceAutomaticCIs", Json.arr rows)]).compress
end AnalyticRemainderSourceAutomaticProbe
'''


def files():
    names = actual_auto_names()
    need(sha(SOURCE_FILE) == "218d50c9a1c34eb9990f64049c4b7806da0d2575df60fc0729478c1faeb514b8",
         "Original CollisionExponential source changed")
    need((base.STAGE / "GeneratedSnapshot.lean.preflight.json").is_file(),
         "Actual generated compiler context is missing")
    source = ("import Lean\nimport " + SOURCE_MODULE + "\n\n" +
              TYPE_CORE.read_text(encoding="utf-8").rstrip() + "\n" + PROBE +
              "\nrun_meta do\n  AnalyticRemainderSourceAutomaticProbe.exportAutomaticCIs #[" +
              ", ".join("`" + name for name in names) + "] " + json.dumps(SOURCE_MODULE) +
              " " + json.dumps(workspace_rel(STAGE / SOURCE_JSON)) + "\n" +
              "".join("#print axioms " + name + "\n" for name in names)).encode("utf-8")
    inputs = [SELF, CONSUMER, Path(base.__file__), TYPE_CORE, RUNTIME, RUNNER, SOURCE_FILE,
              base.STAGE / "preparation.json", base.STAGE / base.INVENTORY_JSON,
              base.STAGE / base.SOURCE_JSON, base.STAGE / base.GENERATED_JSON]
    inputs += [base.STAGE / f"c{i}.json" for i in range(1, 4)]
    inputs += [base.STAGE / f for f in [base.PROVIDER_FILE, base.SOURCE_SNAPSHOT, base.GENERATED_SNAPSHOT]]
    pins = {rel(path): sha(path) for path in inputs}
    for f in [base.PROVIDER_FILE, base.SOURCE_SNAPSHOT, base.GENERATED_SNAPSHOT]:
        sidecar = (base.STAGE / f).with_suffix(".lean.preflight.json")
        need(sidecar.is_file(), "Original bounded compiler sidecar missing: " + f)
        pins[rel(sidecar)] = sha(sidecar)
        side = read(sidecar)
        for key in ["source", "manifest", "log"]:
            actual = Path(side[key])
            if not actual.is_absolute():
                actual = TASK / actual
            pins[rel(actual)] = sha(actual)
        for dep in side["dependency_oleans"]:
            need(dep["stable_during_compile"] and dep["sha256_before"] == dep["sha256_after"],
                 "Original three-context dependency OLean was unstable")
            dep_path = Path(dep["path"]).resolve()
            pins[str(dep_path) if not dep_path.is_relative_to(TASK.resolve()) else rel(dep_path)] = dep["sha256_before"]
    # The bounded runner accepts only mission-local input_hashes. Historical
    # external OLeans remain exact provenance pins in preparation, and the
    # actual source import is independently bound by its compiler sidecar.
    manifest_pins = {key: value for key, value in pins.items()
                     if not Path(key).is_absolute()}
    external_olean_pins = {key: value for key, value in pins.items()
                           if Path(key).is_absolute()}
    need(len(manifest_pins) + len(external_olean_pins) == len(pins)
         and len(external_olean_pins) == 6,
         "The finite historical OLean provenance domain changed")
    manifest = {"schema_version": 1,
                "artifact_kind": "ap19-analytic-remainder-two-autoCI-source-bounded-manifest",
                "output": workspace_rel(STAGE / OUTPUT), "output_sha256": digest(source),
                "imports": ["Lean", SOURCE_MODULE], "input_hashes": manifest_pins,
                "runtime_sha256": sha(RUNTIME), "mode": "modecheck", "emit_olean": False,
                "timeout_seconds": 300, "bounded_runner": rel(RUNNER),
                "bounded_runner_sha256": sha(RUNNER),
                "validated": False, "submission_ready": False}
    command = ("& '" + PYTHON + "' scripts/preflight_staged_module_windows_bounded.py " +
               "ap19/analytic-remainder-auto-ci-source-v4/" + OUTPUT +
               " --root ap19/analytic-remainder-auto-ci-source-v4" +
               " --imports-manifest ap19/analytic-remainder-auto-ci-source-v4/" + MANIFEST +
               " --timeout-seconds 300")
    preparation = {"schema_version": 1,
                   "artifact_kind": "ap19-analytic-remainder-two-observed-autoCI-source-probe-preparation",
                   "observed_generated_automatic_names": names,
                   "observed_generated_inventory": rel(base.STAGE / base.INVENTORY_JSON),
                   "observed_generated_inventory_sha256": sha(base.STAGE / base.INVENTORY_JSON),
                   "source_module": SOURCE_MODULE, "source_sha256": sha(SOURCE_FILE),
                   "source_output": OUTPUT, "source_output_sha256": digest(source),
                   "source_json": SOURCE_JSON, "manifest": MANIFEST,
                   "original_three_contexts_reused_unmodified": True,
                   "input_hashes": pins,
                   "manifest_input_hashes": manifest_pins,
                   "historical_external_olean_provenance_sha256": external_olean_pins,
                   "compile_command": command,
                   "expected_source_automatic_CI_kind": "closed Prop theorem",
                   "validated": False, "submission_ready": False,
                   "Lean_started": False, "API_used": False}
    return {OUTPUT: source, MANIFEST: encode(manifest),
            "preparation.json": encode(preparation),
            "compile-command.txt": (command + "\n").encode("utf-8")}


def check_only():
    expected = files()
    for path, raw in expected.items():
        need((STAGE / path).read_bytes() == raw, "AutoCI source probe input changed: " + path)
    return {"checked_files": len(expected), "observed_names": actual_auto_names(),
            "one_source_modecheck_pending": True, "validated": False,
            "Lean_started": False, "API_used": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if args.prepare:
        for name, raw in files().items():
            path = STAGE / name
            if path.exists():
                need(path.read_bytes() == raw, "Refusing overwrite of autoCI probe: " + name)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps(check_only(), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
