"""Stage the actual Accepted exists_parameters proof as ap6/c5, without Lean/API."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil

import preflight_staged_module as runner

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
STAGE = V / "ap6/c5"
PARENT = V / "ap5/p1j"
PARENT_MANIFEST = PARENT / "manifest.json"
PARENT_VALIDATION = PARENT / "p1-validation.json"
PUBLICATION = PARENT / "publication-draft/publication.json"
CORE = V / "TypeOnlyTheoremSnapshotCore.inc"
THEOREM = "OAI.PiExponent.exists_parameters"
HELPER = "OAI.PiExponent.exists_eta_preserving_exponent_gap"
MODULE = "Theorems.Thm_OAI_PiExponent_exists_parameters"
SOURCE = STAGE / "Theorems/Thm_OAI_PiExponent_exists_parameters.lean"
SOURCE_MANIFEST = STAGE / "child-module.json"
SOURCE_SNAPSHOT = STAGE / "SourceSnapshot.lean"
SOURCE_SNAPSHOT_MANIFEST = STAGE / "source-snapshot.json"
CHILD_SNAPSHOT = STAGE / "ChildSnapshot.lean"
CHILD_SNAPSHOT_MANIFEST = STAGE / "child-snapshot.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def dump(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")


def task_rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def workspace_rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def impl():
    paths = (Path(__file__), TASK / "scripts/validate_ap6_c5_parameters_child.py",
             TASK / "scripts/preflight_staged_module.py")
    return {task_rel(p): sha(p) for p in paths}


def archive_once(path: Path):
    old = path.with_name(path.name + ".before-c5-regeneration")
    if path.is_file() and not old.exists():
        shutil.copyfile(path, old)


def certified_parent():
    m, v, p = read(PARENT_MANIFEST), read(PARENT_VALIDATION), read(PUBLICATION)
    if (m.get("theorem_name") != THEOREM or m.get("inline_helper") != HELPER
            or v.get("theorem_name") != THEOREM or v.get("validated") is not True
            or v.get("stage_manifest_sha256") != sha(PARENT_MANIFEST)
            or m.get("source_commit") != "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
            or p.get("theorem_name") != THEOREM or p.get("confirmed_proved") is not True
            or p.get("theorem_id") != "ee7f5876-ef98-4f15-ba69-401d7b11dc72"
            or p.get("submission_id") != "370aa267-cd8c-4179-ae54-18f84961a1d3"
            or p.get("last_verify_verdict", {}).get("body", {}).get("status") != "ACCEPTED"
            or p.get("target_readback", {}).get("body", {}).get("status") != "Proved"
            or p.get("target_readback", {}).get("body", {}).get("theorem_id") != p["theorem_id"]):
        raise ValueError("p1j kernel/own Accepted and public Proved gate incomplete")
    for relative, digest in v["implementation_hashes"].items():
        if sha(TASK / relative) != digest:
            raise ValueError("p1j certified implementation changed: " + relative)
    for relative, digest in v["output_json_sha256"].items():
        if sha(TASK / relative) != digest:
            raise ValueError("p1j certified JSON output changed: " + relative)
    for relative, digest in m["input_hashes"].items():
        if sha(TASK / relative) != digest:
            raise ValueError("p1j certified input changed: " + relative)
    for key, hashkey in (("source_path", "source_sha256"), ("port_path", "port_sha256"),
                         ("solution", "solution_sha256")):
        if sha(ROOT / m[key]) != m[hashkey]:
            raise ValueError("p1j original/port/solution bytes changed: " + key)
    for dependency in (m["definition_dependency"], m["proved_child_dependency"]):
        for pathkey, hashkey in (("first_search_olean", "first_search_olean_sha256"),
                                 ("actual_child_certificate", "actual_child_certificate_sha256"),
                                 ("olean", "olean_sha256"), ("child_type", "child_type_sha256"),
                                 ("child_proof_references", "child_proof_references_sha256"),
                                 ("structural_certificate", "structural_certificate_sha256")):
            if pathkey in dependency and sha(TASK / dependency[pathkey]) != dependency[hashkey]:
                raise ValueError("Actual published definition/child dependency changed: " + pathkey)
    original, generated = read(PARENT / "original-type.json"), read(PARENT / "generated-type.json")
    if ([x["name"] for x in original] != [HELPER, THEOREM]
            or [x["name"] for x in generated] != [HELPER, THEOREM, "solution"]
            or any(x["value"] is not None for x in original + generated)):
        raise ValueError("p1j parent is not the exact modern null-only helper/target/Sol schema")
    proofrefs = read(PARENT / "proof-references.json")
    if (set(proofrefs) != {"schemaVersion", "probeMainModule", "rows"}
            or {x["name"] for x in proofrefs["rows"]} != {HELPER, "solution"}
            or any(x.get("kind") != "theorem" or x.get("closedType") is not True
                   or x.get("closedValue") is not True for x in proofrefs["rows"])):
        raise ValueError("p1j actual helper/solution proof reference certificate differs")
    pubdir = PUBLICATION.parent
    prep = p.get("preparation", {})
    publish_payload = pubdir / "publish-payload.json"
    verify_payload = pubdir / "verification-payload.json"
    multipart = pubdir / "verification-request.multipart"
    if (sha(publish_payload) != p.get("publish_intent", {}).get("payload_sha256")
            or sha(verify_payload) != p.get("verify_intent", {}).get("descriptor_sha256")
            or sha(multipart) != p.get("verify_intent", {}).get("multipart_sha256")
            or p.get("verify_intent", {}).get("solution_sha256") != m["solution_sha256"]
            or prep.get("validation_sha256") != sha(PARENT_VALIDATION)):
        raise ValueError("p1j published target/solution payload bytes changed")
    payload_problem = read(publish_payload)["problems"][0]
    public_target = p["target_readback"]["body"]
    if any(payload_problem.get(k) != public_target.get(k)
           for k in ("theorem_name", "formal_statement", "preamble", "source")):
        raise ValueError("p1j public target differs from exact published payload")
    return m, v, p


def snapshot_text(import_module: str, artifact: str) -> str:
    names = (HELPER, THEOREM)
    type_output = STAGE / ("source-type.json" if artifact == "source" else "child-type.json")
    refs_output = STAGE / ("source-proof-references.json" if artifact == "source" else "child-proof-references.json")
    names_lean = ", ".join("`" + n for n in names)
    lean = "import Lean\nimport " + import_module + "\n\n" + CORE.read_text(encoding="utf-8")
    lean += "\nrun_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[" + names_lean + "] " + json.dumps(str(type_output.resolve()).replace("\\", "/")) + "\n"
    lean += "\nopen Lean Meta in\nrun_meta do\n"
    lean += "  let env ← Lean.getEnv\n  let mut rows : Array Lean.Json := #[]\n"
    for name in names:
        lean += "  let name : Lean.Name := `" + name + "\n"
        lean += "  let some idx := env.getModuleIdxFor? name | throwError \"expected imported theorem\"\n"
        lean += "  let some owner := env.header.moduleNames[idx.toNat]? | throwError \"bad imported owner index\"\n"
        lean += "  unless owner.toString == " + json.dumps(import_module) + " do throwError \"wrong actual imported theorem owner\"\n"
        lean += "  let some ci := env.find? name | throwError \"missing imported theorem\"\n"
        lean += "  let value ← match ci with | .thmInfo t => pure t.value | _ => throwError \"expected theorem CI\"\n"
        lean += "  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError \"open theorem CI\"\n"
        lean += "  let axioms ← collectAxioms name\n"
        lean += "  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do throwError \"nonstandard axiom\"\n"
        lean += "  rows := rows.push <| Lean.Json.mkObj [(\"name\", toJson name.toString), (\"kind\", toJson \"theorem\"),\n"
        lean += "    (\"levelParams\", toJson (ci.levelParams.map Lean.Name.toString)),\n"
        lean += "    (\"closedType\", toJson true), (\"closedValue\", toJson true),\n"
        lean += "    (\"typeRefs\", toJson ((ci.type.getUsedConstants.map Lean.Name.toString).qsort (fun a b => a < b))),\n"
        lean += "    (\"valueRefs\", toJson ((value.getUsedConstants.map Lean.Name.toString).qsort (fun a b => a < b))),\n"
        lean += "    (\"axioms\", toJson (axioms.map Lean.Name.toString)),\n"
        lean += "    (\"owner\", Lean.Json.mkObj [(\"kind\", toJson \"ImportedModule\"), (\"module\", toJson owner.toString), (\"index\", toJson idx.toNat)])]\n"
    lean += "  IO.FS.writeFile " + json.dumps(str(refs_output.resolve()).replace("\\", "/")) + " ((Lean.Json.mkObj [(\"schemaVersion\", toJson 1), (\"probeMainModule\", toJson env.mainModule.toString), (\"rows\", Lean.Json.arr rows)]).pretty)\n"
    for name in names:
        lean += "#print axioms " + name + "\n"
    return lean


def manifest_for(path: Path, imports: list[str], pins: dict[str, str], artifact: str):
    return {"schema_version": 1, "artifact_kind": "ap6-c5-" + artifact,
        "output": workspace_rel(path), "output_sha256": sha(path), "imports": imports,
        "input_hashes": pins, "runtime_sha256": read(PARENT_MANIFEST)["runtime_sha256"],
        "theorem_name": THEOREM, "helper_name": HELPER, "module": MODULE,
        "parent_validation_sha256": sha(PARENT_VALIDATION),
        "parent_output_json_sha256": read(PARENT_VALIDATION)["output_json_sha256"],
        "implementation_hashes": impl(), "timeout_seconds": 300,
        "validated": False, "submission_ready": False}


def checked_manifest(path: Path, manifest_path: Path):
    manifest = read(manifest_path)
    if manifest.get("output") != workspace_rel(path) or manifest.get("output_sha256") != sha(path):
        raise ValueError("ap6/c5 output/source workspace-relative manifest changed")
    checked = runner.verify_manifest_inputs(manifest)
    source = runner.verify_source_certificate(path, manifest)
    imports = runner.certified_imports(path, manifest)
    if (not all(x["matches"] for x in checked.values())
            or source["source"]["matches"] is not True or imports != manifest["imports"]):
        raise ValueError("Frozen runner source/import/manifest verification failed")
    return {"manifest_sha256": sha(manifest_path), "runner_input_count": len(checked),
            "imports": imports, "source_sha256": sha(path)}


def prepare():
    m, v, p = certified_parent()
    for path in (SOURCE, SOURCE_MANIFEST, SOURCE_SNAPSHOT, SOURCE_SNAPSHOT_MANIFEST,
                 STAGE / "source-preparation.json"):
        archive_once(path)
    original = (ROOT / m["solution"]).read_bytes()
    old1, new1 = b"theorem solution", ("theorem " + THEOREM).encode()
    old2, new2 = b"#print axioms solution", ("#print axioms " + THEOREM).encode()
    if original.count(old1) != 1 or original.count(old2) != 1 or b"sorry" in original:
        raise ValueError("Certified solution is not the expected single sorry-free theorem")
    child = original.replace(old1, new1, 1).replace(old2, new2, 1)
    SOURCE.parent.mkdir(parents=True, exist_ok=True)
    SOURCE.write_bytes(child)
    imports = [line.decode("utf-8").strip()[7:] for line in child.splitlines() if line.startswith(b"import ")]
    if not imports or len(imports) != len(set(imports)):
        raise ValueError("Certified solution import header is empty or duplicated")
    pins = {task_rel(Path(__file__)): sha(Path(__file__)),
            task_rel(TASK / "scripts/validate_ap6_c5_parameters_child.py"): sha(TASK / "scripts/validate_ap6_c5_parameters_child.py"),
            task_rel(TASK / "scripts/preflight_staged_module.py"): sha(TASK / "scripts/preflight_staged_module.py"),
            task_rel(PARENT_MANIFEST): sha(PARENT_MANIFEST), task_rel(PARENT_VALIDATION): sha(PARENT_VALIDATION),
            task_rel(PUBLICATION): sha(PUBLICATION), task_rel(ROOT / m["solution"]): sha(ROOT / m["solution"]),
            task_rel(TASK / m["proved_child_dependency"]["actual_child_certificate"]): m["proved_child_dependency"]["actual_child_certificate_sha256"],
            task_rel(TASK / m["definition_dependency"]["structural_certificate"]): m["definition_dependency"]["structural_certificate_sha256"]}
    dump(SOURCE_MANIFEST, manifest_for(SOURCE, imports, pins, "proved-child-source"))
    SOURCE_SNAPSHOT.write_text(snapshot_text(m["source_module"], "source"), encoding="utf-8", newline="\n")
    source_pins = dict(pins)
    source_pins[task_rel(CORE)] = sha(CORE)
    source_pins[task_rel(ROOT / m["port_path"])] = m["port_sha256"]
    source_pins[task_rel(ROOT / m["source_path"])] = m["source_sha256"]
    dump(SOURCE_SNAPSHOT_MANIFEST, manifest_for(SOURCE_SNAPSHOT,
        ["Lean", m["source_module"]], source_pins, "source-import-snapshot"))
    prep = {"schema_version": 1, "artifact_kind": "ap6-c5-source-preparation",
        "theorem_name": THEOREM, "provided_names": [HELPER],
        "source": workspace_rel(SOURCE), "source_sha256": sha(SOURCE),
        "parent_solution": m["solution"], "parent_solution_sha256": m["solution_sha256"],
        "literal_edits": [{"old": old1.decode(), "new": new1.decode(), "count": 1},
                          {"old": old2.decode(), "new": new2.decode(), "count": 1}],
        "only_top_level_binding_and_axiom_marker_renamed": True,
        "parent_validation_sha256": sha(PARENT_VALIDATION),
        "publication_sha256": sha(PUBLICATION), "implementation_hashes": impl(),
        "source_manifest_sha256": sha(SOURCE_MANIFEST),
        "source_snapshot_manifest_sha256": sha(SOURCE_SNAPSHOT_MANIFEST),
        "Lean_started": False, "API_used": False, "validated": False}
    dump(STAGE / "source-preparation.json", prep)
    return {"prepared": True, "source_sha256": sha(SOURCE), "source_manifest": task_rel(SOURCE_MANIFEST),
        "source_snapshot_manifest": task_rel(SOURCE_SNAPSHOT_MANIFEST),
        "source_preflight": "py -3 scripts/preflight_staged_module.py ap6/c5/Theorems/Thm_OAI_PiExponent_exists_parameters.lean --root ap6/c5 --imports-manifest ap6/c5/child-module.json --emit-olean",
        "source_snapshot_preflight": "py -3 scripts/preflight_staged_module.py ap6/c5/SourceSnapshot.lean --root ap6/c5 --imports-manifest ap6/c5/source-snapshot.json",
        "Lean_started": False, "API_used": False}


def check_only():
    m, _, _ = certified_parent()
    solution = (ROOT / m["solution"]).read_bytes()
    expected = solution.replace(b"theorem solution", ("theorem " + THEOREM).encode(), 1).replace(
        b"#print axioms solution", ("#print axioms " + THEOREM).encode(), 1)
    if SOURCE.read_bytes() != expected:
        raise ValueError("ap6/c5 child proof differs from certified Sol beyond two literal edits")
    source = checked_manifest(SOURCE, SOURCE_MANIFEST)
    snapshot = checked_manifest(SOURCE_SNAPSHOT, SOURCE_SNAPSHOT_MANIFEST)
    prep = read(STAGE / "source-preparation.json")
    if (prep["source_sha256"] != sha(SOURCE) or prep["source_manifest_sha256"] != sha(SOURCE_MANIFEST)
            or prep["source_snapshot_manifest_sha256"] != sha(SOURCE_SNAPSHOT_MANIFEST)
            or prep["implementation_hashes"] != impl()):
        raise ValueError("ap6/c5 preparation pin changed")
    return {"check_only": True, "source": source, "source_snapshot": snapshot,
            "module": MODULE, "theorem_name": THEOREM, "helper": HELPER,
            "Lean_started": False, "API_used": False}


def bind():
    check_only()
    pf = Path(str(SOURCE) + ".preflight.json")
    olean = V / "staged-build/lib/lean/Theorems/Thm_OAI_PiExponent_exists_parameters.olean"
    record = read(pf)
    if (record.get("success") is not True or record.get("mode") != "emit-olean"
            or record.get("actual_module_identity") != MODULE or record.get("output_olean_sha256") != sha(olean)
            or record.get("source_sha256_before") != sha(SOURCE) or record.get("timeout_seconds") != 300):
        raise ValueError("Actual emitted ap6/c5 child OLean record differs")
    for path in (CHILD_SNAPSHOT, CHILD_SNAPSHOT_MANIFEST, STAGE / "child-snapshot-preparation.json"):
        archive_once(path)
    CHILD_SNAPSHOT.write_text(snapshot_text(MODULE, "child"), encoding="utf-8", newline="\n")
    pins = {task_rel(Path(__file__)): sha(Path(__file__)),
            task_rel(TASK / "scripts/validate_ap6_c5_parameters_child.py"): sha(TASK / "scripts/validate_ap6_c5_parameters_child.py"),
            task_rel(TASK / "scripts/preflight_staged_module.py"): sha(TASK / "scripts/preflight_staged_module.py"),
            task_rel(SOURCE): sha(SOURCE), task_rel(SOURCE_MANIFEST): sha(SOURCE_MANIFEST),
            task_rel(pf): sha(pf), task_rel(olean): sha(olean), task_rel(CORE): sha(CORE),
            task_rel(PARENT_VALIDATION): sha(PARENT_VALIDATION)}
    manifest = manifest_for(CHILD_SNAPSHOT, ["Lean", MODULE], pins, "child-import-snapshot")
    manifest["child_olean"] = task_rel(olean)
    manifest["child_olean_sha256"] = sha(olean)
    dump(CHILD_SNAPSHOT_MANIFEST, manifest)
    dump(STAGE / "child-snapshot-preparation.json", {
        "schema_version": 1, "child_snapshot": workspace_rel(CHILD_SNAPSHOT),
        "child_snapshot_sha256": sha(CHILD_SNAPSHOT), "manifest_sha256": sha(CHILD_SNAPSHOT_MANIFEST),
        "child_olean": task_rel(olean), "child_olean_sha256": sha(olean),
        "provided_names": [HELPER], "implementation_hashes": impl(),
        "Lean_started": False, "API_used": False, "validated": False})
    checked_manifest(CHILD_SNAPSHOT, CHILD_SNAPSHOT_MANIFEST)
    return {"bound": True, "child_olean_sha256": sha(olean),
        "snapshot_preflight": "py -3 scripts/preflight_staged_module.py ap6/c5/ChildSnapshot.lean --root ap6/c5 --imports-manifest ap6/c5/child-snapshot.json",
        "Lean_started": False, "API_used": False}


def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--prepare", action="store_true")
    g.add_argument("--check-only", action="store_true")
    g.add_argument("--bind", action="store_true")
    args = ap.parse_args()
    result = prepare() if args.prepare else check_only() if args.check_only else bind()
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
