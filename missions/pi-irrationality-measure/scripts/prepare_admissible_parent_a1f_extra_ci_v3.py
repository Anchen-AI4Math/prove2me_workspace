"""Purely stage source/generated probes for four missing auto-generated CI references.

This producer never invokes Lean or an API. It copies the already-frozen f
solution byte-for-byte into the generated probe and builds a separate source
probe over the original AdmissibleParameters and Dimension modules. The
dimension_volume_lt_one private helper name is discovered from the actual
source parent's immediate value references; it is not guessed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import preflight_staged_module as runner

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
BASE = V / "ap6/a1/source017f"
STAGE = V / "ap6/a1/source017f-extra-ci-v3"
SELF = Path(__file__).resolve()
SOLUTION = BASE / "Solutions/Sol_OAI_PiExponent_exists_admissible_parameters_source017.lean"
SOURCE_MODULES = [
    "OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
    "OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension",
]
PARENTS = [
    "OAI.PiExponent.interpolationSeparationConstant",
    "OAI.PiExponent.weightErrorCoefficient",
    "OAI.PiExponent.dimension_volume_lt_one",
]
EXPECTED_PARENT_HELPERS = {
    PARENTS[0]: ["OAI.PiExponent.interpolationSeparationConstant._proof_1"],
    PARENTS[1]: ["OAI.PiExponent.weightErrorCoefficient._proof_1",
                 "OAI.PiExponent.weightErrorCoefficient._proof_2"],
}
PRIOR_DM_CI = V / "dm-extra-ci/extra-ci-validation.json"
PRIOR_DM_SHA256 = "b647079f89109d6b653867a39352a7626854ad6e281de052358d4290e731d6cc"
CORE = V / "TypedSnapshotCore.inc"
V2_STAGE = V / "ap6/a1/source017f-extra-ci-v2"
V2_FAILED_SOURCE = V2_STAGE / "SourceExtraCI.lean"
V2_FAILED_RECORD = V2_FAILED_SOURCE.with_suffix(".lean.preflight.json")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def rel(path: Path) -> str:
    return path.relative_to(TASK).as_posix()


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def write_exact(path: Path, raw: bytes) -> None:
    if path.exists():
        need(path.read_bytes() == raw, "Refusing to replace different staged evidence: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


PROBE = r'''
open Lean Meta

namespace A1FExtraCI

def refs (value : Expr) : Array Name :=
  (value.getUsedConstants).qsort (fun a b => a.toString < b.toString)

def declarationValue (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo d => some d.value
  | .thmInfo t => some t.value
  | _ => none

def actualOwner (env : Environment) (name : Name) : MetaM Json := do
  match env.getModuleIdxFor? name with
  | none =>
    unless env.mainModule != Name.anonymous do
      throwError "Own-module declaration has anonymous probe module: {name}"
    pure <| Json.mkObj [
      ("kind", toJson "OwnModule"),
      ("moduleIndex", Json.null),
      ("module", toJson env.mainModule.toString)]
  | some index =>
    let some owner := env.header.moduleNames[index.toNat]?
      | throwError "Invalid actual owner module index for {name}"
    pure <| Json.mkObj [
      ("kind", toJson "ImportedModule"),
      ("moduleIndex", toJson index.toNat),
      ("module", toJson owner.toString)]

def fullCI (name : Name) : MetaM Json := do
  let env ← getEnv
  let some ci := env.find? name | throwError "Missing actual CI: {name}"
  let some value := declarationValue ci | throwError "CI has no actual value: {name}"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
    throwError "CI type is not closed: {name}"
  if value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "CI value is not closed: {name}"
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "CI uses axioms outside Std3: {name}"
  let owner ← actualOwner env name
  let typeText ← ppExpr ci.type
  pure <| Json.mkObj [
    ("name", toJson name.toString),
    ("kind", toJson (match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | _ => "other")),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("closedType", toJson true),
    ("closedValue", toJson true),
    ("type", PiExponentInterfaceSnapshot.exprJson ci.type),
    ("value", PiExponentInterfaceSnapshot.exprJson value),
    ("prettyType", toJson typeText.pretty),
    ("typeRefs", toJson ((refs ci.type).map Name.toString)),
    ("valueRefs", toJson ((refs value).map Name.toString)),
    ("axioms", toJson ((axioms.map Name.toString).qsort (fun a b => a < b))),
    ("owner", owner)]

def exportActual (side output : String) : MetaM Unit := do
  let env ← getEnv
  let mut parentRows : Array Json := #[]
  let mut allHelpers : Array Name := #[]
  for parentName in #[
      `OAI.PiExponent.interpolationSeparationConstant,
      `OAI.PiExponent.weightErrorCoefficient,
      `OAI.PiExponent.dimension_volume_lt_one] do
    let some ci := env.find? parentName | throwError "Missing source parent: {parentName}"
    let some value := declarationValue ci | throwError "Parent lacks value: {parentName}"
    let helperPrefix := parentName.toString ++ "._proof_"
    let immediate := (refs value).filter (fun n => n.toString.startsWith helperPrefix)
    if parentName != `OAI.PiExponent.dimension_volume_lt_one then
      let expected := if parentName == `OAI.PiExponent.interpolationSeparationConstant then
        #[`OAI.PiExponent.interpolationSeparationConstant._proof_1]
        else #[`OAI.PiExponent.weightErrorCoefficient._proof_1,
               `OAI.PiExponent.weightErrorCoefficient._proof_2]
      unless immediate == expected do
        throwError "Exact immediate helper names differ for parent {parentName}: {immediate}"
    else
      unless !immediate.isEmpty do
        throwError "Source parent has no immediate auto-proof CI: {parentName}"
    let parentCI ← fullCI parentName
    let mut helperRows : Array Json := #[]
    for helperName in immediate do
      allHelpers := allHelpers.push helperName
      helperRows := helperRows.push (← fullCI helperName)
    parentRows := parentRows.push <| Json.mkObj [
      ("parent", parentCI),
      ("immediateAutoProofRefs", toJson (immediate.map Name.toString)),
      ("helpers", Json.arr helperRows)]
  let result := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)),
    ("artifactKind", toJson "admissible-parent-auto-ci-paired-probe"),
    ("side", toJson side),
    ("probeMainModule", toJson env.mainModule.toString),
    ("sourceParents", Json.arr parentRows),
    ("dynamicallyDiscoveredHelperNames", toJson ((allHelpers.map Name.toString).qsort (fun a b => a < b))),
    ("std3AllowedAxioms", toJson (["propext", "Classical.choice", "Quot.sound"] : List String))]
  IO.FS.writeFile output result.compress

end A1FExtraCI

run_meta do
  A1FExtraCI.exportActual "SIDE" "OUTPUT"
'''


def source_raw() -> bytes:
    imports = ["import " + name for name in ["Lean", *SOURCE_MODULES]]
    output = (TASK.relative_to(ROOT) / rel(STAGE) / "source-extra.json").as_posix()
    exporter = PROBE.replace('"SIDE"', '"source"').replace(
        '"OUTPUT"', json.dumps(output))
    return ("\n".join(imports) + "\n\n" + CORE.read_text(encoding="utf-8") + "\n" + exporter + "\n").encode("utf-8")


def generated_raw() -> bytes:
    # The frozen f solution bytes remain an exact contiguous substring.
    prefix = b"import Lean\n"
    frozen_solution = SOLUTION.read_bytes()
    output = (TASK.relative_to(ROOT) / rel(STAGE) / "generated-extra.json").as_posix()
    exporter = PROBE.replace('"SIDE"', '"generated"').replace(
        '"OUTPUT"', json.dumps(output))
    return prefix + frozen_solution + b"\n" + CORE.read_bytes() + b"\n" + exporter.encode("utf-8") + b"\n"


def authorities():
    prep = read(BASE / "preparation.json")
    need(prep["validated"] is False and prep["submission_ready"] is False,
         "The frozen f preparation state changed unexpectedly")
    need("sorry" not in SOLUTION.read_text(encoding="utf-8"),
         "The frozen solution unexpectedly contains a sorry")
    proof_refs = read(BASE / "proof-references.json")
    rows = {r["name"]: r for r in proof_refs["rows"]}
    expected = {
        "OAI.PiExponent.interpolationSeparationConstant._proof_1",
        "OAI.PiExponent.weightErrorCoefficient._proof_1",
        "OAI.PiExponent.weightErrorCoefficient._proof_2",
        "OAI.PiExponent.dimension_volume_lt_one._proof_1_1",
    }
    actual = set().union(*(set(r.get("valueRefs", [])) for r in rows.values()))
    need(expected <= actual, "The four requested generated-side refs are not in the frozen f proof-reference export")
    need(sha(PRIOR_DM_CI) == PRIOR_DM_SHA256, "Prior dimensionV._proof_1 paired certificate changed")
    prior = read(PRIOR_DM_CI)
    need(prior.get("validated") is True, "The existing dimensionV auto-CI paired certificate is not validated")
    v2 = read(V2_FAILED_RECORD)
    need(v2.get("exit_code") == 1 and v2.get("timed_out") is False
         and v2.get("source_sha256_before") == sha(V2_FAILED_SOURCE)
         and v2.get("source_sha256_after") == sha(V2_FAILED_SOURCE),
         "Retained v2 failure provenance differs")
    v2_log = TASK / v2["log"]
    need(sha(v2_log) == v2["log_sha256"] and b"unexpected token 'prefix'" in v2_log.read_bytes(),
         "Retained v2 log is not the exact reserved-word failure")
    return prep, proof_refs, prior, v2, v2_log


def plan():
    prep, proof_refs, prior, v2, v2_log = authorities()
    base_manifest = read(BASE / "manifest.json")
    solution_manifest = read(BASE / "c2.json")
    input_hashes = dict(prep["input_hashes"])
    for path in [SELF, SOLUTION, BASE / "preparation.json", BASE / "proof-references.json",
                 BASE / "source-type.json", BASE / "generated-type.json", BASE / "manifest.json",
                 BASE / "SourceSnapshot.lean", BASE / "SnapshotGeneratedWithRefs.lean",
                 BASE / "c1.json", BASE / "c2.json", BASE / "c3.json", BASE / "c4.json",
                 BASE / "Solutions/Sol_OAI_PiExponent_exists_admissible_parameters_source017.lean.preflight.json",
                 BASE / "SnapshotGeneratedWithRefs.lean.preflight.json", CORE,
                 PRIOR_DM_CI, V / "dm-extra-ci/original-extra.json", V / "dm-extra-ci/generated-extra.json",
                 V2_FAILED_SOURCE, V2_FAILED_RECORD, v2_log, V2_STAGE / "source.json"]:
        input_hashes[rel(path)] = sha(path)
    runtime_sha = solution_manifest["runtime_sha256"]
    files = {}
    for side, name in (("source", "SourceExtraCI.lean"), ("generated", "GeneratedExtraCI.lean")):
        raw = source_raw() if side == "source" else generated_raw()
        imports = ["Lean", *SOURCE_MODULES] if side == "source" else ["Lean", *solution_manifest["imports"]]
        files[name] = {"side": side, "source": rel(STAGE / name), "source_sha256": hashlib.sha256(raw).hexdigest(),
                       "manifest": rel(STAGE / (side + ".json")), "imports": imports}
    return {
        "schema_version": 1,
        "artifact_kind": "admissible-parent-auto-ci-paired-preparation",
        "status": "prepared-uncompiled",
        "node": "OAI.PiExponent.exists_admissible_parameters_source017",
        "source_stage": rel(BASE),
        "source_commit": base_manifest["source_commit"],
        "source_solution": rel(SOLUTION),
        "source_solution_sha256": sha(SOLUTION),
        "source_parents": PARENTS,
        "exact_generated_helper_refs": [
            "OAI.PiExponent.interpolationSeparationConstant._proof_1",
            "OAI.PiExponent.weightErrorCoefficient._proof_1",
            "OAI.PiExponent.weightErrorCoefficient._proof_2"],
        "dynamic_source_parent": "OAI.PiExponent.dimension_volume_lt_one",
        "dynamic_source_rule": "Collect only immediate full-CI value references whose exact name starts with OAI.PiExponent.dimension_volume_lt_one._proof_; export the parent actual type/value and every matching helper actual CI. Do not assume the source suffix matches the generated-side proof-reference suffix.",
        "existing_dimensionV_helper_certificate": {
            "name": "OAI.PiExponent.dimensionV._proof_1",
            "certificate": rel(PRIOR_DM_CI),
            "certificate_sha256": sha(PRIOR_DM_CI),
            "source_extra_sha256": sha(V / "dm-extra-ci/original-extra.json"),
            "generated_extra_sha256": sha(V / "dm-extra-ci/generated-extra.json"),
            "reused_without_recompilation": True},
        "retained_v2_failure": {
            "source": rel(V2_FAILED_SOURCE),
            "source_sha256": sha(V2_FAILED_SOURCE),
            "preflight_record": rel(V2_FAILED_RECORD),
            "preflight_record_sha256": sha(V2_FAILED_RECORD),
            "log": rel(v2_log),
            "log_sha256": sha(v2_log),
            "failure": "Lean reserved keyword prefix used as a local identifier; v3 changes only that identifier and corrects actual OwnModule owner serialization."},
        "runtime_sha256": runtime_sha,
        "input_hashes": input_hashes,
        "files": files,
        "compile_commands": {name: f"python scripts/preflight_staged_module.py {STAGE.name}/{name} --root {STAGE.name} --imports-manifest {STAGE.name}/{row['side']}.json --timeout-seconds 300" for name, row in files.items()},
        "Lean_started": False,
        "API_used": False,
        "validated": False,
        "submission_ready": False}


def manifests(p):
    return {name: {
        "schema_version": 1,
        "artifact_kind": "admissible-parent-auto-ci-probe-import-certificate",
        "output": (TASK / row["source"]).relative_to(ROOT).as_posix(),
        "output_sha256": row["source_sha256"],
        "imports": row["imports"],
        "input_hashes": p["input_hashes"],
        "runtime_sha256": p["runtime_sha256"],
        "timeout_seconds": 300,
        "node_validated": False,
        "Lean_started": False,
        "submission_ready": False} for name, row in p["files"].items()}


def check():
    p = plan()
    need(read(STAGE / "preparation.json") == p, "Preparation record differs from deterministic plan")
    docs = manifests(p)
    for name, row in p["files"].items():
        source, manifest = TASK / row["source"], TASK / row["manifest"]
        expected_raw = source_raw() if row["side"] == "source" else generated_raw()
        need(source.read_bytes() == expected_raw, "Staged source differs: " + name)
        need(read(manifest) == docs[name], "Staged compiler manifest differs: " + name)
        runner.verify_manifest_inputs(docs[name])
        runner.verify_source_certificate(source, docs[name])
        need(runner.certified_imports(source, docs[name]) == row["imports"], "Certified imports differ: " + name)
    return {"prepared": True, "stage": rel(STAGE), "files": p["files"],
            "Lean_started": False, "API_used": False, "validated": False, "submission_ready": False}


def prepare():
    p = plan()
    docs = manifests(p)
    for name, row in p["files"].items():
        path = TASK / row["source"]
        write_exact(path, source_raw() if row["side"] == "source" else generated_raw())
        write_exact(TASK / row["manifest"], (json.dumps(docs[name], indent=2, ensure_ascii=False) + "\n").encode())
    write_exact(STAGE / "preparation.json", (json.dumps(p, indent=2, ensure_ascii=False) + "\n").encode())
    return check()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare else check(), indent=2))
