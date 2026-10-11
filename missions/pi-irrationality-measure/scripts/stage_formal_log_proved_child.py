"""Stage a proved Theorems child module and its imported-kernel snapshot.

This producer consumes only an actual f1 kernel certificate.  It never imports
the f1 statement stub: the exact certified Sol bytes are rebound from the
literal `solution` name to the public source theorem name.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import generate_formal_log_truncation_provider as formal
import stage_formal_log_base_node as exact_io
import validate_formal_log_node as node_certificate

TASK, ROOT, V = formal.TASK, formal.ROOT, formal.V
F1 = V / "flp3/f1"
DEST = V / "flp3/c1"
THEOREM = "OAI.PiExponent.FormalLogTruncation.liftSeries_eq_toMvPowerSeries"
NODE = "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:356"
MODULE = "Theorems.Thm_" + THEOREM.replace(".", "_")
SOURCE = DEST / Path(*MODULE.split(".")).with_suffix(".lean")
SOURCE_MANIFEST = DEST / "child-module.json"
SOURCE_PREPARATION = DEST / "child-source-preparation.json"
SNAPSHOT = DEST / "ChildSnapshot.lean"
SNAPSHOT_MANIFEST = DEST / "child-snapshot.json"
SNAPSHOT_PREPARATION = DEST / "child-snapshot-preparation.json"
CHILD_TYPE = DEST / "child-type.json"
CHILD_REFS = DEST / "child-proof-references.json"
SELF = Path(__file__).resolve()


def certificate():
    result = node_certificate.validate_formal_node(F1)
    data = result["certificate"]["data"]
    if (data.get("validated") is not True or data.get("node") != NODE
            or data.get("theorem_name") != THEOREM or data.get("Std3_only") is not True
            or data.get("target_stub_unused") is not True
            or data.get("actual_project_reference_coverage_complete") is not True):
        raise ValueError("f1 is not the exact validated proved parent node")
    return result


def prepare_source():
    cert = certificate()
    source = cert["solution_bytes"]
    if b"sorry" in source:
        raise ValueError("Certified solution source unexpectedly contains sorry")
    edits = [(b"theorem solution (", ("theorem " + THEOREM + " (").encode()),
             (b"#print axioms solution", ("#print axioms " + THEOREM).encode())]
    output, ledger = source, []
    for old, new in edits:
        if output.count(old) != 1 or output.count(new) != 0:
            raise ValueError("Proved-child binding edit is not unique and fresh")
        offset = output.index(old)
        output = output.replace(old, new, 1)
        ledger.append({"start": offset, "end": offset + len(old),
                       "source": old.decode(), "replacement": new.decode()})
    exact_io.write_exact(SOURCE, output)
    manifest = cert["manifest_data"]
    cert_path = TASK / cert["certificate"]["path"]
    pins = {formal.rel(SELF): formal.sha(SELF),
            formal.rel(Path(node_certificate.__file__)): formal.sha(Path(node_certificate.__file__)),
            formal.rel(cert_path): formal.sha(cert_path), formal.rel(cert["manifest"]): formal.sha(cert["manifest"]),
            formal.rel(ROOT / manifest["solution"]): formal.sha(ROOT / manifest["solution"])}
    document = {"schema_version": 1, "artifact_kind": "proved-formal-log-child-module-import-certificate",
        "output": SOURCE.relative_to(ROOT).as_posix(), "output_sha256": formal.sha(SOURCE),
        "imports": manifest["imports"], "input_hashes": pins,
        "runtime_sha256": manifest["runtime_sha256"], "parent_node_certificate": formal.rel(cert_path),
        "parent_node_certificate_sha256": formal.sha(cert_path), "theorem_name": THEOREM,
        "module": MODULE, "emit_olean_required": True, "timeout_seconds": 300,
        "validated": False, "submission_ready": False}
    exact_io.write_exact(SOURCE_MANIFEST, document)
    preparation = {"schema_version": 1, "artifact_kind": "proved-formal-log-child-source-preparation",
        "parent_node": NODE, "parent_node_certificate": formal.rel(cert_path),
        "parent_node_certificate_sha256": formal.sha(cert_path),
        "certified_solution": formal.rel(ROOT / manifest["solution"]),
        "certified_solution_sha256": formal.sha(ROOT / manifest["solution"]),
        "output": formal.rel(SOURCE), "output_sha256": formal.sha(SOURCE),
        "module": MODULE, "theorem_name": THEOREM, "edit_ledger": ledger,
        "only_literal_binding_and_axiom_marker_renamed": True,
        "statement_stub_imported": False, "Lean_started": False,
        "validated": False, "submission_ready": False}
    exact_io.write_exact(SOURCE_PREPARATION, preparation)
    return preparation


def check_source():
    cert = certificate()
    preparation = formal.read(SOURCE_PREPARATION)
    reconstructed = cert["solution_bytes"]
    for row in preparation["edit_ledger"]:
        old, new = row["source"].encode(), row["replacement"].encode()
        if reconstructed.count(old) != 1:
            raise ValueError("Child source edit ledger no longer applies uniquely")
        reconstructed = reconstructed.replace(old, new, 1)
    if reconstructed != SOURCE.read_bytes() or b"theorem solution (" in reconstructed or b"sorry" in reconstructed:
        raise ValueError("Proved child source is not the exact certified solution rebinding")
    manifest = formal.read(SOURCE_MANIFEST)
    formal.runner.verify_manifest_inputs(manifest)
    formal.runner.verify_source_certificate(SOURCE, manifest)
    imports = formal.runner.certified_imports(SOURCE, manifest)
    paths = [SOURCE.resolve(), Path(str(SOURCE.resolve()) + ".preflight.json"), SOURCE_MANIFEST.resolve()]
    if max(map(lambda p: len(str(p)), paths)) >= 240:
        raise ValueError("Proved child compiler path exceeds Windows budget")
    return {"exact_certified_solution_rebinding": True, "imports": len(imports),
            "maximum_absolute_path_length": max(len(str(p)) for p in paths),
            "Lean_started": False, "validated": False, "submission_ready": False}


IMPORTED_REFS = r'''
namespace FormalLogImportedChildSnapshot
open Lean Meta
def refs (value : Expr) : Array String :=
  (value.getUsedConstants.map Name.toString).qsort (fun a b => a < b)
def exportChild (name : Name) (expectedModule output : String) : MetaM Unit := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? name | throwError "Proved child theorem is not imported"
  let some owner := env.header.moduleNames[idx.toNat]? | throwError "Invalid proved child module index"
  unless owner.toString == expectedModule do throwError "Proved child theorem has the wrong owner"
  let some ci := env.find? name | throwError "Missing proved child theorem"
  let value ← match ci with | .thmInfo t => pure t.value | _ => throwError "Proved child CI is not a theorem"
  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars ||
      value.hasMVar || value.hasFVar || value.hasLooseBVars then
    throwError "Proved child theorem type/value is not closed"
  let axioms ← collectAxioms name
  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
    throwError "Proved child theorem has nonstandard axioms"
  let row := Json.mkObj [("name", toJson name.toString), ("kind", toJson "theorem"),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("closedType", toJson true), ("closedValue", toJson true),
    ("typeRefs", toJson (refs ci.type)), ("valueRefs", toJson (refs value)),
    ("axioms", toJson (axioms.map Name.toString)),
    ("owner", Json.mkObj [("kind", toJson "ImportedModule"),
      ("module", toJson owner.toString), ("index", toJson idx.toNat)])]
  IO.FS.writeFile output <| (Json.mkObj [("schemaVersion", toJson 1),
    ("probeMainModule", toJson env.mainModule.toString), ("rows", Json.arr #[row])]).pretty
end FormalLogImportedChildSnapshot
'''


def prepare_snapshot():
    cert = certificate()
    record_path = Path(str(SOURCE) + ".preflight.json")
    if not record_path.is_file():
        raise ValueError("Proved child module has no actual emitted-OLean preflight")
    record = formal.read(record_path)
    olean = V / "staged-build/lib/lean" / Path(*MODULE.split(".")).with_suffix(".olean")
    if (record.get("success") is not True or record.get("mode") != "emit-olean"
            or record.get("actual_module_identity") != MODULE
            or record.get("output_olean_sha256") != formal.sha(olean)
            or record.get("source_sha256_before") != formal.sha(SOURCE)):
        raise ValueError("Proved child emitted OLean evidence is stale or failed")
    core = (V / "TypeOnlyTheoremSnapshotCore.inc").read_text(encoding="utf-8")
    source = ("import Lean\nimport " + MODULE + "\n\n" + core + IMPORTED_REFS +
        "\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\n" +
        "run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`" + THEOREM + "] " +
        json.dumps(formal.provider.workspace_relative(CHILD_TYPE)) + "\n" +
        "run_meta do\n  FormalLogImportedChildSnapshot.exportChild `" + THEOREM + " " +
        json.dumps(MODULE) + " " + json.dumps(formal.provider.workspace_relative(CHILD_REFS)) + "\n" +
        "#print axioms " + THEOREM + "\n")
    exact_io.write_exact(SNAPSHOT, source.encode())
    cert_path = TASK / cert["certificate"]["path"]
    pins = {formal.rel(SELF): formal.sha(SELF), formal.rel(cert_path): formal.sha(cert_path),
            formal.rel(SOURCE): formal.sha(SOURCE), formal.rel(SOURCE_MANIFEST): formal.sha(SOURCE_MANIFEST),
            formal.rel(record_path): formal.sha(record_path), formal.rel(olean): formal.sha(olean),
            "verification/TypeOnlyTheoremSnapshotCore.inc": formal.sha(V / "TypeOnlyTheoremSnapshotCore.inc")}
    document = {"schema_version": 1, "artifact_kind": "proved-formal-log-child-snapshot-import-certificate",
        "output": SNAPSHOT.relative_to(ROOT).as_posix(), "output_sha256": formal.sha(SNAPSHOT),
        "imports": ["Lean", MODULE], "input_hashes": pins,
        "runtime_sha256": cert["manifest_data"]["runtime_sha256"], "theorem_name": THEOREM,
        "child_module": MODULE, "child_olean": formal.rel(olean), "child_olean_sha256": formal.sha(olean),
        "timeout_seconds": 300, "validated": False, "submission_ready": False}
    exact_io.write_exact(SNAPSHOT_MANIFEST, document)
    preparation = {"schema_version": 1, "artifact_kind": "proved-formal-log-child-snapshot-preparation",
        "source": formal.rel(SNAPSHOT), "source_sha256": formal.sha(SNAPSHOT),
        "manifest": formal.rel(SNAPSHOT_MANIFEST), "manifest_sha256": formal.sha(SNAPSHOT_MANIFEST),
        "child_module": MODULE, "child_olean": formal.rel(olean), "child_olean_sha256": formal.sha(olean),
        "type_output": formal.rel(CHILD_TYPE), "proof_reference_output": formal.rel(CHILD_REFS),
        "actual_imported_owner_required": True, "Std3_required": True,
        "Lean_started": False, "validated": False, "submission_ready": False}
    exact_io.write_exact(SNAPSHOT_PREPARATION, preparation)
    return preparation


def check_snapshot():
    preparation = formal.read(SNAPSHOT_PREPARATION)
    manifest = formal.read(SNAPSHOT_MANIFEST)
    formal.runner.verify_manifest_inputs(manifest)
    formal.runner.verify_source_certificate(SNAPSHOT, manifest)
    imports = formal.runner.certified_imports(SNAPSHOT, manifest)
    paths = [SNAPSHOT.resolve(), Path(str(SNAPSHOT.resolve()) + ".preflight.json"),
             CHILD_TYPE.resolve(), CHILD_REFS.resolve()]
    if max(len(str(p)) for p in paths) >= 240:
        raise ValueError("Child snapshot compiler/output path exceeds Windows budget")
    return {"child_module": MODULE, "imports": imports, "actual_imported_owner_required": True,
            "maximum_absolute_path_length": max(len(str(p)) for p in paths),
            "Lean_started": False, "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare-source", action="store_true")
    group.add_argument("--check-source", action="store_true")
    group.add_argument("--prepare-snapshot", action="store_true")
    group.add_argument("--check-snapshot", action="store_true")
    args = parser.parse_args()
    if args.prepare_source: result = prepare_source()
    elif args.check_source: result = check_source()
    elif args.prepare_snapshot: result = prepare_snapshot()
    else: result = check_snapshot()
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
