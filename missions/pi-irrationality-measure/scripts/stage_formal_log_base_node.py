"""Stage the first FormalLog proof node under a fresh immutable attempt root.

Pure Python only.  The fourth compiler input is an exact byte-prefix extension
of SnapshotGenerated.lean which also exports closed proof reference sets.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import generate_formal_log_truncation_provider as formal
import generate_platform_provider_nodes as node_impl
import plan_formal_log_proof_nodes as plan

TASK, ROOT, V = formal.TASK, formal.ROOT, formal.V
DEST = V / "formal-log-proof-nodes-v2"
KEY = plan.NODE_KEYS["liftSeries_eq_toMvPowerSeries"]
SELF = Path(__file__).resolve()


def sha_bytes(value):
    return hashlib.sha256(value).hexdigest()


def write_exact(path, data):
    raw = data if isinstance(data, bytes) else (json.dumps(data, indent=2, ensure_ascii=False) + "\n").encode()
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Existing v2 artifact differs; preserve the attempt before regenerating: " + str(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)


def proof_reference_addon(requests, output):
    names = ["solution", *[row["generated_name"] for row in requests]]
    if len(names) != len(set(names)):
        raise ValueError("Proof-reference request names are not unique")
    lean_names = ", ".join("`" + name for name in names)
    return r'''

namespace FormalLogProofReferenceSnapshot

open Lean Meta

def refs (value : Expr) : Array String :=
  (value.getUsedConstants.map Name.toString).qsort (fun a b => a < b)

def export (requests : Array Name) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut seen : Array Name := #[]
  let mut rows : Array Json := #[]
  for name in requests do
    if seen.contains name then
      throwError "Duplicate proof-reference request: {name}"
    seen := seen.push name
    unless (env.getModuleIdxFor? name).isNone do
      throwError "Proof-reference request was inherited instead of declared here: {name}"
    let some ci := env.find? name | throwError "Missing proof-reference request: {name}"
    let value ← match ci with
      | .thmInfo theoremInfo => pure theoremInfo.value
      | _ => throwError "Proof-reference request is not a theorem: {name}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
      throwError "Proof-reference theorem type is not closed: {name}"
    if value.hasMVar || value.hasFVar || value.hasLooseBVars then
      throwError "Proof-reference theorem value is not closed: {name}"
    let axioms ← collectAxioms name
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Proof-reference theorem has nonstandard axioms: {name}"
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("userName", toJson name.toString),
      ("kind", toJson "theorem"),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("closedType", toJson true), ("closedValue", toJson true),
      ("typeRefs", toJson (refs ci.type)), ("valueRefs", toJson (refs value)),
      ("axioms", toJson (axioms.map Name.toString)),
      ("owner", Json.mkObj [("kind", toJson "OwnModule"),
        ("module", toJson env.mainModule.toString)])]
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion", toJson 1), ("probeMainModule", toJson env.mainModule.toString),
    ("rows", Json.arr rows)]).pretty

end FormalLogProofReferenceSnapshot

open Lean Meta in
run_meta do
  FormalLogProofReferenceSnapshot.export #[REQUESTS] OUTPUT
'''.replace("REQUESTS", lean_names).replace("OUTPUT", json.dumps(formal.provider.workspace_relative(output)))


def prepare():
    if sha_bytes(SELF.read_bytes()) != sha_bytes(Path(__file__).read_bytes()):
        raise ValueError("Staging implementation changed during startup")
    old_dest = node_impl.DEST
    try:
        node_impl.DEST = DEST
        generator = node_impl.ProviderNodeGenerator()
        generated = generator.generate(KEY)
    finally:
        node_impl.DEST = old_dest
    stage = TASK / generated["stage"]
    manifest_path = stage / "manifest.json"
    manifest = formal.read(manifest_path)
    if manifest["child_nodes"]:
        raise ValueError("The base node must have no child dependency")
    certificates = [plan.certified_definition(row["source_module"], row["platform_module"])
                    for row in manifest["definition_dependency_witnesses"]]
    base_snapshot = stage / "SnapshotGenerated.lean"
    refs_output = stage / "proof-references.json"
    addon = proof_reference_addon(manifest["public_inline_ci_requests"], refs_output).encode()
    with_refs = stage / "SnapshotGeneratedWithRefs.lean"
    write_exact(with_refs, base_snapshot.read_bytes() + addon)
    certified_inputs_path = stage / "certified-inputs.json"
    write_exact(certified_inputs_path, {
        "schema_version": 1, "artifact_kind": "formal-log-base-node-certified-inputs",
        "node": KEY, "definition_certificates": certificates, "child_certificates": [],
        "validated_node": False, "Lean_started": False, "submission_ready": False})
    pins = {formal.rel(SELF): formal.sha(SELF), formal.rel(Path(plan.__file__)): formal.sha(Path(plan.__file__)),
            formal.rel(manifest_path): formal.sha(manifest_path),
            formal.rel(certified_inputs_path): formal.sha(certified_inputs_path)}
    for row in certificates:
        pins[row["certificate"]] = row["certificate_sha256"]
        pins[row["output_olean"]] = row["output_lean_sha256"]
    files = [next(stage.glob("Thm_*.lean")), next(stage.glob("Sol_*.lean")),
             stage / "SnapshotOriginal.lean", with_refs]
    compile_manifests = {}
    for index, source in enumerate(files, 1):
        imports = (["Lean", manifest["source_components"][0]["source_module"]]
                   if source.name == "SnapshotOriginal.lean" else manifest["imports"])
        path = stage / f"compile-{index}.json"
        write_exact(path, {"schema_version": 1,
            "artifact_kind": "formal-log-proof-node-file-import-certificate",
            "output": source.relative_to(ROOT).as_posix(), "output_sha256": formal.sha(source),
            "imports": imports, "input_hashes": pins, "runtime_sha256": manifest["runtime_sha256"],
            "node": KEY, "node_validated": False, "timeout_seconds": 300,
            "Lean_started": False, "submission_ready": False})
        compile_manifests[source.name] = {"manifest": formal.rel(path), "manifest_sha256": formal.sha(path)}
    preparation = {**generated, "attempt_root": formal.rel(DEST),
        "base_snapshot": formal.rel(base_snapshot), "base_snapshot_sha256": formal.sha(base_snapshot),
        "generated_with_refs": formal.rel(with_refs), "generated_with_refs_sha256": formal.sha(with_refs),
        "generated_with_refs_prefix_bytes": base_snapshot.stat().st_size,
        "proof_reference_addon_sha256": sha_bytes(addon), "proof_reference_output": formal.rel(refs_output),
        "proof_reference_requests": ["solution", *[x["generated_name"] for x in manifest["public_inline_ci_requests"]]],
        "certified_definition_dependencies": len(certificates), "compile_manifests": compile_manifests,
        "exact_old_snapshot_prefix": True, "pure_python_prepared": True,
        "Lean_started": False, "validated": False, "submission_ready": False}
    write_exact(stage / "preparation.json", preparation)
    return preparation


def check():
    name = node_impl.ProviderNodeGenerator().node_name(KEY)
    stage = DEST / name.replace(".", "_")
    preparation = formal.read(stage / "preparation.json")
    base = TASK / preparation["base_snapshot"]
    extended = TASK / preparation["generated_with_refs"]
    if not extended.read_bytes().startswith(base.read_bytes()):
        raise ValueError("Generated-with-refs lost the exact frozen snapshot prefix")
    checked = {}
    for filename, row in preparation["compile_manifests"].items():
        source = stage / filename
        mp = TASK / row["manifest"]
        if formal.sha(mp) != row["manifest_sha256"]:
            raise ValueError("Compilation manifest changed: " + filename)
        document = formal.read(mp)
        formal.runner.verify_manifest_inputs(document)
        formal.runner.verify_source_certificate(source, document)
        imports = formal.runner.certified_imports(source, document)
        checked[filename] = {"source_sha256": formal.sha(source), "imports": len(imports)}
    return {"node": KEY, "fresh_attempt_root": formal.rel(DEST),
            "exact_old_snapshot_prefix": True, "file_and_import_pins_checked": True,
            "files": checked, "Lean_started": False, "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare else check(), indent=2))


if __name__ == "__main__":
    main()
