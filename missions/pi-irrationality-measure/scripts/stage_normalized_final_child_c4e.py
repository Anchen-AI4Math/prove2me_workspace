"""Pure staging for the proved normalized-successive-approximations child.

This script never starts Lean and never calls the Prove2Me API.  It derives the
child source from the exact accepted ap5/n3 solution by changing only the top
level theorem binding and its final ``#print axioms`` request.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import preflight_staged_module as runner

ROOT = Path(__file__).resolve().parents[1]
STAGE = ROOT / "verification/ap6/c4e"
THEOREM = "OAI.PiExponent.exists_normalized_successive_approximations"
MODULE = "Theorems.Thm_OAI_PiExponent_exists_normalized_successive_approximations"
N3 = ROOT / "verification/ap5/n3"
ACCEPTED = N3 / "Solutions/Sol_OAI_PiExponent_exists_normalized_successive_approximations.lean"
N3_CERT = N3 / "n3-validation.json"
PUBLICATION = N3 / "publication-draft/publication.json"
EXPECTED_N3_CERT_SHA = "8af423f4a67eb56ef2d3cac0754d3b465de385c38c6acf0a0c467811b4d5843e"
EXPECTED_ACCEPTED_SHA = "4a934c65e4ca027498c6596bb63e84e0eaea61a397525d9bed4dd01914c8ffc3"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def task_rel(path: Path) -> str:
    return "missions/pi-irrationality-measure/" + path.resolve().relative_to(ROOT).as_posix()


def input_rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


TYPE_CORE = r'''
open Lean Meta
namespace C4Snapshot
partial def levelJson : Level -> Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ u => Json.arr #[toJson "succ", levelJson u]
  | .max u v => Json.arr #[toJson "max", levelJson u, levelJson v]
  | .imax u v => Json.arr #[toJson "imax", levelJson u, levelJson v]
  | .param n => Json.arr #[toJson "param", toJson n.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]
def binderTag : BinderInfo -> String
  | .default => "explicit" | .implicit => "implicit"
  | .strictImplicit => "strictImplicit" | .instImplicit => "instance"
partial def exprJson : Expr -> Json
  | .bvar i => Json.arr #[toJson "bvar", toJson i]
  | .fvar n => Json.arr #[toJson "fvar", toJson n.name.toString]
  | .mvar n => Json.arr #[toJson "mvar", toJson n.name.toString]
  | .sort u => Json.arr #[toJson "sort", levelJson u]
  | .const n us => Json.arr #[toJson "const", toJson n.toString, Json.arr (us.map levelJson).toArray]
  | .app f a => Json.arr #[toJson "app", exprJson f, exprJson a]
  | .lam _ t b bi => Json.arr #[toJson "lambda", toJson (binderTag bi), exprJson t, exprJson b]
  | .forallE _ t b bi => Json.arr #[toJson "forall", toJson (binderTag bi), exprJson t, exprJson b]
  | .letE _ t v b nondep => Json.arr #[toJson "let", exprJson t, exprJson v, exprJson b, toJson nondep]
  | .lit (.natVal n) => Json.arr #[toJson "natLiteral", toJson n]
  | .lit (.strVal s) => Json.arr #[toJson "stringLiteral", toJson s]
  | .mdata _ e => exprJson e
  | .proj n i e => Json.arr #[toJson "projection", toJson n.toString, toJson i, exprJson e]
def refs (e : Expr) : Array String := (e.getUsedConstants.map Name.toString).qsort (fun a b => a < b)
def exportSnapshot (name : Name) (expectedOwner outputType outputRefs : String) (imported : Bool) : MetaM Unit := do
  let env <- getEnv
  let some ci := env.find? name | throwError "missing declaration"
  let value <- match ci with | .thmInfo t => pure t.value | _ => throwError "not theorem"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "open theorem CI"
  let owner <- if imported then do
    let some idx := env.getModuleIdxFor? name | throwError "theorem is not imported"
    let some actual := env.header.moduleNames[idx.toNat]? | throwError "bad module index"
    unless actual.toString == expectedOwner do throwError "wrong actual owner"
    pure (Json.mkObj [("kind", toJson "ImportedModule"), ("module", toJson actual.toString), ("index", toJson idx.toNat)])
  else do
    unless (env.getModuleIdxFor? name).isNone do throwError "source theorem was inherited"
    pure (Json.mkObj [("kind", toJson "OwnModule"), ("module", toJson env.mainModule.toString)])
  let axioms <- collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "non-Std3 axiom"
  let typeText <- ppExpr ci.type
  IO.FS.writeFile outputType (Json.arr #[Json.mkObj [("name", toJson name.toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)), ("type", exprJson ci.type),
    ("value", Json.null), ("prettyType", toJson typeText.pretty)]] |>.compress)
  IO.FS.writeFile outputRefs ((Json.mkObj [("schemaVersion", toJson 1),
    ("probeMainModule", toJson env.mainModule.toString), ("rows", Json.arr #[Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson "theorem"), ("closedType", toJson true),
      ("closedValue", toJson true), ("typeRefs", toJson (refs ci.type)), ("valueRefs", toJson (refs value)),
      ("axioms", toJson (axioms.map Name.toString)), ("owner", owner)]])]).pretty)
end C4Snapshot
'''


def stage() -> dict:
    if sha(N3_CERT) != EXPECTED_N3_CERT_SHA or sha(ACCEPTED) != EXPECTED_ACCEPTED_SHA:
        raise ValueError("frozen ap5/n3 certificate or accepted solution changed")
    publication = json.loads(PUBLICATION.read_text(encoding="utf-8"))
    parent_certificate = json.loads(N3_CERT.read_text(encoding="utf-8"))
    verdict = publication["last_verify_verdict"]["body"]
    readback = publication["target_readback"]["body"]
    if verdict["status"] != "ACCEPTED" or readback["status"] != "Proved":
        raise ValueError("ap5/n3 is not Accepted/Proved")
    accepted_bytes = ACCEPTED.read_bytes()
    old_binding = b"theorem solution"
    old_print = b"#print axioms solution"
    if accepted_bytes.count(old_binding) != 1 or accepted_bytes.count(old_print) != 1:
        raise ValueError("accepted solution top binding shape changed")
    child_bytes = accepted_bytes.replace(old_binding, f"theorem {THEOREM}".encode(), 1)
    child_bytes = child_bytes.replace(old_print, f"#print axioms {THEOREM}".encode(), 1)
    child = child_bytes.decode("utf-8")
    target = STAGE / "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(child_bytes)

    source_probe = child + "\n" + TYPE_CORE + f'''\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\nrun_meta do\n  C4Snapshot.exportSnapshot `{THEOREM} "SourceSnapshot" "{task_rel(STAGE / 'source-type.json')}" "{task_rel(STAGE / 'source-proof-references.json')}" false\n'''
    (STAGE / "SourceSnapshot.lean").write_text(source_probe, encoding="utf-8")
    child_probe = f'''import Lean\nimport {MODULE}\n\n{TYPE_CORE}\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\nrun_meta do\n  C4Snapshot.exportSnapshot `{THEOREM} "{MODULE}" "{task_rel(STAGE / 'child-type.json')}" "{task_rel(STAGE / 'child-proof-references.json')}" true\n#print axioms {THEOREM}\n'''
    (STAGE / "ChildSnapshot.lean").write_text(child_probe, encoding="utf-8")

    common_inputs = {
        input_rel(Path(__file__)): sha(Path(__file__)),
        input_rel(ACCEPTED): sha(ACCEPTED), input_rel(N3_CERT): sha(N3_CERT),
        input_rel(PUBLICATION): sha(PUBLICATION)
    }
    runtime_sha = sha(ROOT / "verification/lean-runtime.json")
    dump(STAGE / "child-module.json", {"schema_version": 1,
        "artifact_kind": "ap6-c4e-proved-child-source-certificate", "output": task_rel(target),
        "output_sha256": sha(target), "imports": ["Lean",
          "Theorems.Thm_OAI_PiExponent_exists_successive_approximations",
          "Theorems.Thm_OAI_PiExponent_exists_normalized_selection_of_selector"],
        "input_hashes": common_inputs, "runtime_sha256": runtime_sha, "theorem_name": THEOREM,
        "module": MODULE, "emit_olean_required": True, "timeout_seconds": 300, "validated": False})
    dump(STAGE / "source-snapshot.json", {"schema_version": 1,
        "artifact_kind": "ap6-c4e-source-own-snapshot-certificate", "output": task_rel(STAGE / "SourceSnapshot.lean"),
        "output_sha256": sha(STAGE / "SourceSnapshot.lean"), "imports": ["Lean",
          "Theorems.Thm_OAI_PiExponent_exists_successive_approximations",
          "Theorems.Thm_OAI_PiExponent_exists_normalized_selection_of_selector"],
        "input_hashes": common_inputs, "runtime_sha256": runtime_sha, "theorem_name": THEOREM,
        "module": "SourceSnapshot", "timeout_seconds": 300, "validated": False})

    pins = {
        "schema_version": 1,
        "artifact_kind": "ap6-c4e-proved-normalized-final-child-preparation",
        "validated": False,
        "actual_child_certificate": "verification/ap6/c4e/actual-child-validation.json",
        "actual_child_certificate_status": "pending_root_compile",
        "theorem_name": THEOREM,
        "module": MODULE,
        "source": "verification/ap6/c4e/Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean",
        "source_sha256": sha(target),
        "derivation": "exact accepted solution with only top-level binding and #print target renamed",
        "accepted_solution": "verification/ap5/n3/Solutions/Sol_OAI_PiExponent_exists_normalized_successive_approximations.lean",
        "accepted_solution_sha256": EXPECTED_ACCEPTED_SHA,
        "parent_validation": "verification/ap5/n3/n3-validation.json",
        "parent_validation_sha256": EXPECTED_N3_CERT_SHA,
        "own_accepted_record": "verification/ap5/n3/publication-draft/publication.json",
        "own_accepted_record_sha256": sha(PUBLICATION),
        "theorem_id": readback["theorem_id"],
        "submission_id": verdict["id"],
        "publication_status": readback["status"],
        "verification_status": verdict["status"],
        "parent_outputs": {
            "ORIGINAL1": {"path": "verification/ap5/n3/original-type.json", "sha256": sha(N3 / "original-type.json"), "name": THEOREM},
            "GENERATED1solution": {"path": "verification/ap5/n3/generated-type.json", "sha256": sha(N3 / "generated-type.json"), "name": "solution"},
            "proof_references": {"path": "verification/ap5/n3/proof-references.json", "sha256": sha(N3 / "proof-references.json"),
                "actual_proved_children": ["OAI.PiExponent.exists_successive_approximations", "OAI.PiExponent.exists_normalized_selection_of_selector"]}
        },
        "parent_implementation_hashes": parent_certificate["implementation_hashes"],
        "parent_output_json_sha256": parent_certificate["output_json_sha256"],
        "parent_preflights": {
            name: {
                "record": row["record"],
                "record_sha256": row["record_sha256"],
                "seconds": row.get("seconds", row["data"]["seconds"]),
                "dependency_oleans": row["data"]["dependency_oleans"]
            }
            for name, row in parent_certificate["preflights"].items()
        },
        "source_probe": "verification/ap6/c4e/SourceSnapshot.lean",
        "child_probe": "verification/ap6/c4e/ChildSnapshot.lean",
        "output_olean": "verification/staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.olean",
        "constraints": {"Lean_started": False, "API_used": False, "target_sorry_emitted": False, "target_sorry_imported": False, "root_sole_compiler": True}
    }
    dump(STAGE / "preparation.json", pins)
    return pins


def bind() -> dict:
    check()
    source = STAGE / "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean"
    olean = ROOT / "verification/staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.olean"
    theorem_pf = source.with_suffix(source.suffix + ".preflight.json")
    source_pf = STAGE / "SourceSnapshot.lean.preflight.json"
    for path in (olean, theorem_pf, source_pf):
        if not path.is_file():
            raise ValueError("root compile output missing: " + task_rel(path))
    script = Path(__file__)
    inputs = {input_rel(script): sha(script), input_rel(source): sha(source),
        input_rel(STAGE / "child-module.json"): sha(STAGE / "child-module.json"),
        input_rel(theorem_pf): sha(theorem_pf), input_rel(source_pf): sha(source_pf), input_rel(olean): sha(olean),
        input_rel(N3_CERT): sha(N3_CERT), input_rel(PUBLICATION): sha(PUBLICATION)}
    manifest = {"schema_version": 1, "artifact_kind": "ap6-c4e-proved-child-import-snapshot-certificate",
        "output": task_rel(STAGE / "ChildSnapshot.lean"), "output_sha256": sha(STAGE / "ChildSnapshot.lean"),
        "imports": ["Lean", MODULE], "input_hashes": inputs,
        "runtime_sha256": sha(ROOT / "verification/lean-runtime.json"), "theorem_name": THEOREM,
        "module": MODULE, "child_olean": task_rel(olean), "child_olean_sha256": sha(olean),
        "timeout_seconds": 300, "validated": False}
    dump(STAGE / "child-snapshot.json", manifest)
    binding = {"schema_version": 1, "artifact_kind": "ap6-c4e-postcompile-binding", "validated": False,
        "child_olean": task_rel(olean), "child_olean_sha256": sha(olean),
        "theorem_preflight": task_rel(theorem_pf), "theorem_preflight_sha256": sha(theorem_pf),
        "source_preflight": task_rel(source_pf), "source_preflight_sha256": sha(source_pf),
        "child_snapshot_manifest": task_rel(STAGE / "child-snapshot.json"),
        "child_snapshot_manifest_sha256": sha(STAGE / "child-snapshot.json"),
        "actual_child_certificate": task_rel(STAGE / "actual-child-validation.json"),
        "actual_child_certificate_status": "pending_child_probe_and_certify_existing", "Lean_started": False, "API_used": False}
    dump(STAGE / "postcompile-bindings.json", binding)
    return binding


def check() -> dict:
    pins = json.loads((STAGE / "preparation.json").read_text(encoding="utf-8"))
    source = STAGE / pins["source"].split("verification/ap6/c4e/", 1)[-1]
    if sha(source) != pins["source_sha256"]:
        raise ValueError("staged child source drift")
    text = source.read_text(encoding="utf-8")
    if "sorry" in text or "theorem solution" in text or f"theorem {THEOREM}" not in text:
        raise ValueError("staged child source is not the exact proved rename")
    if pins["parent_validation_sha256"] != sha(N3_CERT) or pins["own_accepted_record_sha256"] != sha(PUBLICATION):
        raise ValueError("parent evidence drift")
    for staged_source, manifest_path in (
        (source, STAGE / "child-module.json"),
        (STAGE / "SourceSnapshot.lean", STAGE / "source-snapshot.json")):
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        runner.verify_manifest_inputs(manifest)
        runner.verify_source_certificate(staged_source, manifest)
        if runner.certified_imports(staged_source, manifest) != manifest["imports"]:
            raise ValueError("certified import list differs: " + input_rel(staged_source))
    for probe in (STAGE / "SourceSnapshot.lean", STAGE / "ChildSnapshot.lean"):
        probe_text = probe.read_text(encoding="utf-8")
        if "def export (" in probe_text or "C4Snapshot.export `" in probe_text:
            raise ValueError("reserved export identifier remains: " + input_rel(probe))
        if "def exportSnapshot (" not in probe_text or "C4Snapshot.exportSnapshot `" not in probe_text:
            raise ValueError("bounded exportSnapshot repair missing: " + input_rel(probe))
        for output_name in ("type.json", "proof-references.json"):
            if output_name in probe_text and str(ROOT).replace("\\", "/") in probe_text:
                raise ValueError("probe output JSON path is not workspace-relative: " + input_rel(probe))
    return {"pure_check": True, "source_sha256": sha(source), "Lean_started": False, "API_used": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--check", action="store_true")
    group.add_argument("--bind", action="store_true")
    args = parser.parse_args()
    result = bind() if args.bind else check() if args.check else stage()
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
