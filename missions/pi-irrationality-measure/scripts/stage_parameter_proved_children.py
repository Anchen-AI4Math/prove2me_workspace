"""Pure-Python staging for already accepted, independently proved leaves.

The generated theorem source is the exact certified solution with only its
top-level `solution` binding and axiom marker renamed.  This script never runs
Lean or contacts the platform.  Use --check-only before compilation, --bind
after the root agent emits the child OLean, and --validate-existing after the
source and imported-child snapshots have been compiled.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path
import sys

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
SPECS = [
    ("c1", "exists_large_log_approximation", "independent"),
    ("c2", "exists_rational_parameters", "independent"),
    ("c3", "exists_small_rational_sigma", "independent"),
    ("c4", "exists_uniform_weight_error_margin", "nodes-preview"),
]
STD3 = {"propext", "Classical.choice", "Quot.sound"}
sys.path.insert(0, str(TASK / "scripts"))
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone
import generate_independent_node as independent


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def task_rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def written_during(path: Path, preflight: dict):
    finished = datetime.fromisoformat(preflight["at_utc"]).timestamp()
    if not finished - preflight["seconds"] - 2 <= path.stat().st_mtime <= finished + 2:
        raise ValueError(f"Snapshot output was not written during its exact Lean run: {path}")


def dump(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")


def source_stage(slug: str, kind: str) -> Path:
    if kind == "independent":
        return V / "independent" / ("OAI_PiExponent_" + slug)
    return V / "nodes-preview" / ("OAI_PiExponent_" + slug)


def configure(row):
    stage, slug, kind = row
    parent = source_stage(slug, kind)
    manifest = read(parent / "manifest.json")
    theorem = manifest["theorem_name"]
    module = "Theorems.Thm_" + theorem.replace(".", "_")
    child_stage = V / "ap4" / stage
    source = child_stage / Path(*module.split(".")).with_suffix(".lean")
    snapshot = child_stage / "ChildSnapshot.lean"
    return {"stage": stage, "slug": slug, "kind": kind, "parent": parent,
            "parent_manifest": parent / "manifest.json", "parent_validation": parent / "validation.json",
            "publication": parent / "publication.json", "source": source,
            "source_manifest": child_stage / "child-module.json",
            "preparation": child_stage / "child-source-preparation.json",
            "accepted_capture": child_stage / "own-accepted-capture.json",
            "snapshot": snapshot, "snapshot_manifest": child_stage / "child-snapshot.json",
            "snapshot_preparation": child_stage / "child-snapshot-preparation.json",
            "child_type": child_stage / "child-type.json", "child_refs": child_stage / "child-proof-references.json",
            "source_snapshot": child_stage / "SourceSnapshot.lean",
            "source_snapshot_manifest": child_stage / "source-snapshot.json",
            "source_type": child_stage / "source-type.json", "source_refs": child_stage / "source-proof-references.json",
            "theorem": theorem, "module": module, "runtime_sha256": manifest["runtime_sha256"]}


def accepted_pins(c):
    manifest, validation, publication = read(c["parent_manifest"]), read(c["parent_validation"]), read(c["publication"])
    if c["accepted_capture"].is_file():
        capture = read(c["accepted_capture"])
        progress_row = capture.get("captured_own_accepted_row", {})
    else:
        progress = read(V / "verified-stage-progress.json")
        proofs = [x for x in progress["proofs"] if x.get("theorem_name") == c["theorem"]]
        if len(proofs) != 1:
            raise ValueError(f"Expected one ownAccepted progress row for {c['theorem']}")
        progress_row = proofs[0]
        capture = None
    if progress_row.get("status") != "ACCEPTED_AND_PROVED" or progress_row.get("verification_record") != task_rel(c["publication"]):
        raise ValueError(f"Current progress does not pin ownAccepted+exactProved for {c['theorem']}")
    if sha(c["publication"]) != progress_row.get("verification_record_sha256"):
        raise ValueError(f"Own publication pin is stale for {c['theorem']}")
    if publication.get("theorem_name") != c["theorem"] or publication.get("theorem_id") != progress_row.get("theorem_id") or publication.get("submission_id") != progress_row.get("submission_id"):
        raise ValueError(f"Own publication identities differ for {c['theorem']}")
    if capture is not None and (capture.get("publication_sha256") != sha(c["publication"])
            or capture.get("captured_own_accepted_row") != progress_row
            or capture.get("theorem_name") != c["theorem"]):
        raise ValueError(f"Captured Accepted row differs from its pinned own publication: {c['theorem']}")
    if validation.get("validated") is not True or validation.get("standard_axioms_only") is not True or validation.get("kernel_types_equal") is not True:
        raise ValueError(f"Accepted source validation is incomplete for {c['theorem']}")
    for key in ("statement_sha256", "solution_sha256", "runtime_sha256"):
        expected = manifest.get(key)
        if expected is not None and validation.get(key) != expected:
            raise ValueError(f"Source proof validation no longer matches its frozen manifest ({key}): {c['theorem']}")
    if manifest.get("theorem_name") != c["theorem"] or manifest.get("source_commit") != "adc7f1241b42e322a6451854ab7e4b4c146bf78a":
        raise ValueError(f"Frozen source identity/commit differs for {c['theorem']}")
    return manifest, validation, publication, progress_row


def prepare(c):
    manifest, validation, publication, progress_row = accepted_pins(c)
    if not c["accepted_capture"].exists():
        dump(c["accepted_capture"], {"schema_version": 1, "artifact_kind": "own-accepted-proved-row-capture",
             "theorem_name": c["theorem"], "captured_own_accepted_row": progress_row,
             "publication": task_rel(c["publication"]), "publication_sha256": sha(c["publication"]),
             "status": "ACCEPTED_AND_PROVED", "target_status": "Proved"})
    source_component = manifest.get("source_components", [{}])[0] if manifest.get("source_components") else {}
    solution = ROOT / manifest["solution"]
    sol = solution.read_bytes()
    imports = [line.decode("utf-8").strip()[7:] for line in sol.splitlines()
               if line.lstrip().startswith(b"import ")]
    if not imports or len(imports) != len(set(imports)):
        raise ValueError(f"Certified solution import preamble is empty or duplicated: {solution}")
    old1, new1 = b"theorem solution", ("theorem " + c["theorem"]).encode("utf-8")
    old2, new2 = b"#print axioms solution", ("#print axioms " + c["theorem"]).encode("utf-8")
    if sol.count(old1) != 1 or sol.count(old2) != 1 or b"sorry" in sol:
        raise ValueError(f"Certified solution is not a single sorry-free theorem: {solution}")
    child = sol.replace(old1, new1, 1).replace(old2, new2, 1)
    c["source"].parent.mkdir(parents=True, exist_ok=True)
    c["source"].write_bytes(child)
    pins = {
        task_rel(Path(__file__)): sha(Path(__file__)),
        task_rel(c["parent_manifest"]): sha(c["parent_manifest"]),
        task_rel(c["parent_validation"]): sha(c["parent_validation"]),
        task_rel(c["publication"]): sha(c["publication"]),
        task_rel(c["accepted_capture"]): sha(c["accepted_capture"]),
        task_rel(solution): sha(solution),
    }
    source_manifest = {
        "schema_version": 1, "artifact_kind": "accepted-parameter-proved-child-source-certificate",
        "output": rel(c["source"]), "output_sha256": sha(c["source"]),
        "imports": imports, "input_hashes": pins, "runtime_sha256": c["runtime_sha256"],
        "source_commit": manifest["source_commit"], "source_module": manifest.get("source_module", source_component.get("source_module")),
        "source_sha256": manifest.get("source_sha256", source_component.get("source_sha256")),
        "theorem_name": c["theorem"], "module": c["module"],
        "parent_validation_sha256": sha(c["parent_validation"]),
        "own_accepted_theorem_id": progress_row["theorem_id"], "own_accepted_submission_id": progress_row["submission_id"],
        "emit_olean_required": True, "timeout_seconds": 300, "validated": False, "submission_ready": False,
    }
    dump(c["source_manifest"], source_manifest)
    edits = [
        {"old": old1.decode(), "new": new1.decode(), "count": 1},
        {"old": old2.decode(), "new": new2.decode(), "count": 1},
    ]
    prep = {
        "schema_version": 1, "artifact_kind": "accepted-parameter-proved-child-source-preparation",
        "parent_validation": rel(c["parent_validation"]), "parent_validation_sha256": sha(c["parent_validation"]),
        "parent_solution": rel(solution), "parent_solution_sha256": sha(solution),
        "publication": rel(c["publication"]), "publication_sha256": sha(c["publication"]),
        "source": rel(c["source"]), "source_sha256": sha(c["source"]), "module": c["module"],
        "theorem_name": c["theorem"], "literal_edits": edits, "only_top_level_binding_and_axiom_marker_renamed": True,
        "sorry_free_actual_proof_body": True, "Lean_started": False, "validated": False,
    }
    dump(c["preparation"], prep)
    source_component = manifest.get("source_components", [{}])[0] if manifest.get("source_components") else {}
    source_module = manifest.get("source_module", source_component.get("source_module"))
    source_path = ROOT / manifest.get("source", source_component.get("source"))
    original_path = ROOT / manifest.get("original_source", source_component.get("original_source"))
    core_path = V / "TypeOnlyTheoremSnapshotCore.inc"
    source_snapshot = ("import Lean\nimport " + source_module + "\n\n" + core_path.read_text(encoding="utf-8") +
        "\nnamespace ParameterSourceSnapshot\nopen Lean Meta\n"+
        "def refs (value : Expr) : Array String :=\n  (value.getUsedConstants.map Name.toString).qsort (fun a b => a < b)\n"+
        "def exportSource (name : Name) (expectedModule output : String) : MetaM Unit := do\n"+
        "  let env ← getEnv\n  let some idx := env.getModuleIdxFor? name | throwError \"source theorem is not imported\"\n"+
        "  let some owner := env.header.moduleNames[idx.toNat]? | throwError \"invalid module index\"\n"+
        "  unless owner.toString == expectedModule do throwError \"source theorem has wrong actual owner\"\n"+
        "  let some ci := env.find? name | throwError \"missing source theorem\"\n"+
        "  let value ← match ci with | .thmInfo t => pure t.value | _ => throwError \"source is not theorem CI\"\n"+
        "  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError \"source theorem CI is not closed\"\n"+
        "  let axioms ← collectAxioms name\n"+
        "  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do throwError \"source theorem uses non-Std3 axiom\"\n"+
        "  let row := Json.mkObj [(\"name\", toJson name.toString), (\"kind\", toJson \"theorem\"), (\"levelParams\", toJson (ci.levelParams.map Name.toString)),\n"+
        "    (\"closedType\", toJson true), (\"closedValue\", toJson true), (\"typeRefs\", toJson (refs ci.type)),\n"+
        "    (\"valueRefs\", toJson (refs value)), (\"axioms\", toJson (axioms.map Name.toString)),\n"+
        "    (\"owner\", Json.mkObj [(\"kind\", toJson \"ImportedModule\"), (\"module\", toJson owner.toString), (\"index\", toJson idx.toNat)])]\n"+
        "  IO.FS.writeFile output ((Json.mkObj [(\"schemaVersion\", toJson 1), (\"probeMainModule\", toJson env.mainModule.toString), (\"rows\", Json.arr #[row])]).pretty)\nend ParameterSourceSnapshot\n"+
        "\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\n"+
        "run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`" + c["theorem"] + "] " +
        json.dumps(str(c["source_type"].resolve()).replace("\\", "/")) + "\n"+
        "run_meta do\n  ParameterSourceSnapshot.exportSource `" + c["theorem"] + " " + json.dumps(source_module) + " " +
        json.dumps(str(c["source_refs"].resolve()).replace("\\", "/")) + "\n"+
        "#print axioms " + c["theorem"] + "\n")
    c["source_snapshot"].write_text(source_snapshot, encoding="utf-8", newline="\n")
    source_pins = {task_rel(Path(__file__)): sha(Path(__file__)), task_rel(c["parent_manifest"]): sha(c["parent_manifest"]),
        task_rel(c["parent_validation"]): sha(c["parent_validation"]), task_rel(source_path): sha(source_path),
        task_rel(original_path): sha(original_path), task_rel(core_path): sha(core_path)}
    dump(c["source_snapshot_manifest"], {"schema_version": 1, "artifact_kind": "parameter-source-import-snapshot-certificate",
        "output": rel(c["source_snapshot"]), "output_sha256": sha(c["source_snapshot"]),
        "imports": ["Lean", source_module], "input_hashes": source_pins, "runtime_sha256": c["runtime_sha256"],
        "theorem_name": c["theorem"], "module": source_module, "source_snapshot_module": "SourceSnapshot",
        "timeout_seconds": 300, "validated": False})
    return {"stage": c["stage"], "module": c["module"], "theorem": c["theorem"],
            "source": rel(c["source"]), "source_sha256": sha(c["source"]),
            "imports": imports, "compile_command":
            "python scripts/preflight_staged_module.py " + c["source"].relative_to(V).as_posix()
            + " --root ap4/" + c["stage"] + " --imports-manifest "
            + c["source_manifest"].relative_to(V).as_posix() + " --emit-olean",
            "source_snapshot_compile_command": "python scripts/preflight_staged_module.py "
            + c["source_snapshot"].relative_to(V).as_posix() + " --root ap4/" + c["stage"]
            + " --imports-manifest " + c["source_snapshot_manifest"].relative_to(V).as_posix(),
            "Lean_started": False, "validated": False}


def check_only(c):
    accepted_pins(c)
    if c["kind"] == "independent":
        independent.check_stage_inputs(c["parent"], read(c["parent_manifest"]))
    m, p = read(c["source_manifest"]), read(c["preparation"])
    solution = ROOT / read(c["parent_manifest"])["solution"]
    expected = solution.read_bytes().replace(b"theorem solution", ("theorem " + c["theorem"]).encode(), 1).replace(
        b"#print axioms solution", ("#print axioms " + c["theorem"]).encode(), 1)
    if c["source"].read_bytes() != expected or m["output_sha256"] != sha(c["source"]):
        raise ValueError(f"Staged child is no longer the exact certified proof for {c['theorem']}")
    for path, digest in m["input_hashes"].items():
        if sha(TASK / path) != digest:
            raise ValueError(f"Staged input pin changed: {path}")
    sm = read(c["source_snapshot_manifest"])
    if sm.get("output") != rel(c["source_snapshot"]) or sm.get("output_sha256") != sha(c["source_snapshot"]):
        raise ValueError(f"Fresh source snapshot manifest differs: {c['theorem']}")
    for path, digest in sm["input_hashes"].items():
        if sha(TASK / path) != digest:
            raise ValueError(f"Fresh source snapshot pin changed: {path}")
    if p["sorry_free_actual_proof_body"] is not True or p["only_top_level_binding_and_axiom_marker_renamed"] is not True:
        raise ValueError("Child preparation evidence is not exact")
    return {"stage": c["stage"], "check_only": True, "source_sha256": sha(c["source"]),
            "imports": m["imports"], "module": c["module"], "theorem": c["theorem"], "Lean_started": False}


def bind(c):
    check_only(c)
    pf = Path(str(c["source"]) + ".preflight.json")
    if not pf.is_file():
        raise ValueError(f"Missing emitted-OLean preflight from root agent: {pf}")
    record = read(pf)
    olean = V / "staged-build/lib/lean" / Path(*c["module"].split(".")).with_suffix(".olean")
    if (record.get("success") is not True or record.get("mode") != "emit-olean"
            or record.get("actual_module_identity") != c["module"]
            or record.get("output_olean_sha256") != sha(olean)
            or record.get("source_sha256_before") != sha(c["source"])
            or record.get("timeout_seconds") != 300):
        raise ValueError(f"Emitted child OLean record is stale or mismatched: {c['theorem']}")
    core_path = V / "TypeOnlyTheoremSnapshotCore.inc"
    core = core_path.read_text(encoding="utf-8")
    snapshot = ("import Lean\nimport " + c["module"] + "\n\n" + core +
        "\nnamespace ParameterChildSnapshot\nopen Lean Meta\n" +
        "def refs (value : Expr) : Array String :=\n  (value.getUsedConstants.map Name.toString).qsort (fun a b => a < b)\n"+
        "def exportChild (name : Name) (expectedModule output : String) : MetaM Unit := do\n"+
        "  let env ← getEnv\n  let some idx := env.getModuleIdxFor? name | throwError \"child theorem is not imported\"\n"+
        "  let some owner := env.header.moduleNames[idx.toNat]? | throwError \"invalid module index\"\n"+
        "  unless owner.toString == expectedModule do throwError \"child theorem has wrong actual owner\"\n"+
        "  let some ci := env.find? name | throwError \"missing child theorem\"\n"+
        "  let value ← match ci with | .thmInfo t => pure t.value | _ => throwError \"child is not theorem CI\"\n"+
        "  if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars || value.hasMVar || value.hasFVar || value.hasLooseBVars then throwError \"child CI is not closed\"\n"+
        "  let axioms ← collectAxioms name\n"+
        "  unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do throwError \"child uses non-Std3 axiom\"\n"+
        "  let row := Json.mkObj [(\"name\", toJson name.toString), (\"kind\", toJson \"theorem\"),\n"+
        "    (\"levelParams\", toJson (ci.levelParams.map Name.toString)),\n"+
        "    (\"closedType\", toJson true), (\"closedValue\", toJson true),\n"+
        "    (\"typeRefs\", toJson (refs ci.type)), (\"valueRefs\", toJson (refs value)),\n"+
        "    (\"axioms\", toJson (axioms.map Name.toString)), (\"owner\", Json.mkObj [(\"kind\", toJson \"ImportedModule\"), (\"module\", toJson owner.toString), (\"index\", toJson idx.toNat)])]\n"+
        "  IO.FS.writeFile output ((Json.mkObj [(\"schemaVersion\", toJson 1), (\"probeMainModule\", toJson env.mainModule.toString), (\"rows\", Json.arr #[row])]).pretty)\nend ParameterChildSnapshot\n"+
        "\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\n"+
        "run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`" + c["theorem"] + "] " +
        json.dumps(str(c["child_type"].resolve()).replace("\\", "/")) + "\n"+
        "run_meta do\n  ParameterChildSnapshot.exportChild `" + c["theorem"] + " " + json.dumps(c["module"]) + " " +
        json.dumps(str(c["child_refs"].resolve()).replace("\\", "/")) + "\n"+
        "#print axioms " + c["theorem"] + "\n")
    c["snapshot"].write_text(snapshot, encoding="utf-8", newline="\n")
    pins = {task_rel(Path(__file__)): sha(Path(__file__)), task_rel(c["source"]): sha(c["source"]),
            task_rel(c["source_manifest"]): sha(c["source_manifest"]), task_rel(pf): sha(pf), task_rel(olean): sha(olean),
            task_rel(core_path): sha(core_path)}
    sm = {"schema_version": 1, "artifact_kind": "parameter-proved-child-import-snapshot-certificate",
          "output": rel(c["snapshot"]), "output_sha256": sha(c["snapshot"]),
          "imports": ["Lean", c["module"]], "input_hashes": pins, "runtime_sha256": c["runtime_sha256"],
          "theorem_name": c["theorem"], "module": c["module"], "child_olean": rel(olean),
          "child_olean_sha256": sha(olean), "timeout_seconds": 300, "validated": False}
    dump(c["snapshot_manifest"], sm)
    dump(c["snapshot_preparation"], {"schema_version": 1, "artifact_kind": "parameter-proved-child-import-snapshot-preparation",
         "source": rel(c["snapshot"]), "source_sha256": sha(c["snapshot"]), "manifest": rel(c["snapshot_manifest"]),
         "manifest_sha256": sha(c["snapshot_manifest"]), "module": c["module"], "child_olean": rel(olean),
         "actual_imported_owner_required": True, "type_and_proof_refs_required": True, "Std3_required": True,
         "Lean_started": False, "validated": False})
    return {"stage": c["stage"], "bound_child_olean": rel(olean), "child_olean_sha256": sha(olean),
            "snapshot": rel(c["snapshot"]), "snapshot_sha256": sha(c["snapshot"]),
            "snapshot_compile_command": "python scripts/preflight_staged_module.py " + c["snapshot"].relative_to(V).as_posix()
            + " --root ap4/" + c["stage"] + " --imports-manifest "
            + c["snapshot_manifest"].relative_to(V).as_posix(), "Lean_started": False}


def validate_existing(c):
    check_only(c)
    data = read(c["child_refs"])
    rows = data.get("rows", [])
    if len(rows) != 1:
        raise ValueError(f"Expected one imported child CI row for {c['theorem']}")
    row = rows[0]
    if (set(row) != {"name", "kind", "levelParams", "closedType", "closedValue", "typeRefs", "valueRefs", "axioms", "owner"}
            or row.get("name") != c["theorem"] or row.get("kind") != "theorem"
            or row.get("closedType") is not True or row.get("closedValue") is not True
            or row.get("owner", {}).get("kind") != "ImportedModule"
            or row.get("owner", {}).get("module") != c["module"]
            or set(row.get("axioms", [])) != STD3):
        raise ValueError(f"Actual imported theorem CI/owner/Std3 evidence mismatches for {c['theorem']}")
    for key in ("levelParams", "typeRefs", "valueRefs", "axioms"):
        values = row[key]
        if not isinstance(values, list) or any(not isinstance(x, str) for x in values) or len(values) != len(set(values)):
            raise ValueError(f"Imported child {key} list is malformed: {c['theorem']}")
    if row["typeRefs"] != sorted(row["typeRefs"]) or row["valueRefs"] != sorted(row["valueRefs"]):
        raise ValueError(f"Imported child reference lists are not canonical: {c['theorem']}")
    if c["theorem"] in set(row["typeRefs"]) | set(row["valueRefs"]) or "solution" in set(row["typeRefs"]) | set(row["valueRefs"]):
        raise ValueError(f"Imported proof has a self/solution reference: {c['theorem']}")
    owner = row["owner"]
    if set(owner) != {"kind", "module", "index"} or type(owner["index"]) is not int or owner["index"] < 0:
        raise ValueError(f"Imported owner evidence has unexpected shape: {c['theorem']}")
    child_types = read(c["child_type"])
    source_types = read(c["source_type"])
    source_manifest = read(c["parent_manifest"])
    source_component = source_manifest.get("source_components", [{}])[0] if source_manifest.get("source_components") else {}
    source_module = source_manifest.get("source_module", source_component.get("source_module"))
    original_types = read(c["parent"] / "original-type.json")
    generated_types = read(c["parent"] / "generated-type.json")
    if not (isinstance(child_types, list) and len(child_types) == 1
            and isinstance(source_types, list) and len(source_types) == 1
            and isinstance(original_types, list) and len(original_types) == 1
            and isinstance(generated_types, list) and len(generated_types) == 2):
        raise ValueError(f"Source/child type snapshots have an unexpected domain: {c['theorem']}")
    child_t, fresh_source_t, original_t = child_types[0], source_types[0], original_types[0]
    generated_by_name = {x.get("name"): x for x in generated_types}
    source_row = next((x for x in original_types if x.get("name") == c["theorem"]), None)
    target_row, solution_row = generated_by_name.get(c["theorem"]), generated_by_name.get("solution")
    if any(not isinstance(x, dict) or set(x) != {"levelParams", "name", "prettyType", "type", "value"}
           for x in (child_t, fresh_source_t, original_t, target_row, solution_row)):
        raise ValueError(f"Source/child type snapshot row schema differs: {c['theorem']}")
    if any(x["name"] != c["theorem"] for x in (child_t, fresh_source_t, original_t, target_row)) or solution_row["name"] != "solution":
        raise ValueError(f"Source/child type snapshot identity differs: {c['theorem']}")
    def normalized_type(item, levels):
        mapping = {name: f"u{i}" for i, name in enumerate(levels)}
        def walk(x):
            if isinstance(x, list):
                if len(x) == 2 and x[0] == "param" and x[1] in mapping:
                    return ["param", mapping[x[1]]]
                return [walk(y) for y in x]
            if isinstance(x, dict): return {k: walk(v) for k, v in x.items()}
            return x
        return walk(item)
    type_rows = (child_t, fresh_source_t, original_t, target_row, solution_row)
    for other in type_rows[1:]:
        if (len(child_t["levelParams"]) != len(other["levelParams"])
                or normalized_type(child_t["type"], child_t["levelParams"]) != normalized_type(other["type"], other["levelParams"])):
            raise ValueError(f"Imported child kernel type differs from source/solution: {c['theorem']}")
    if child_t["value"] is not None or fresh_source_t["value"] is not None or original_t["value"] is not None:
        raise ValueError(f"Type-only source/child snapshots unexpectedly export theorem values: {c['theorem']}")
    source_refs_doc = read(c["source_refs"])
    source_rows = source_refs_doc.get("rows", [])
    if len(source_rows) != 1:
        raise ValueError(f"Expected one freshly imported source CI row: {c['theorem']}")
    source_row = source_rows[0]
    if (set(source_row) != {"name", "kind", "levelParams", "closedType", "closedValue", "typeRefs", "valueRefs", "axioms", "owner"}
            or source_row.get("name") != c["theorem"] or source_row.get("kind") != "theorem"
            or source_row.get("closedType") is not True or source_row.get("closedValue") is not True
            or set(source_row.get("axioms", [])) != STD3
            or source_row.get("owner", {}).get("kind") != "ImportedModule"
            or source_row.get("owner", {}).get("module") != source_module):
        raise ValueError(f"Fresh source theorem CI/owner/Std3 evidence mismatches: {c['theorem']}")
    source_owner = source_row["owner"]
    if set(source_owner) != {"kind", "module", "index"} or type(source_owner["index"]) is not int or source_owner["index"] < 0:
        raise ValueError(f"Fresh source owner evidence has unexpected shape: {c['theorem']}")
    for refrow in (source_row, row):
        for key in ("levelParams", "typeRefs", "valueRefs", "axioms"):
            values = refrow[key]
            if not isinstance(values, list) or any(not isinstance(x, str) for x in values) or len(values) != len(set(values)):
                raise ValueError(f"Malformed actual CI references/universes: {c['theorem']}")
        if refrow["typeRefs"] != sorted(refrow["typeRefs"]) or refrow["valueRefs"] != sorted(refrow["valueRefs"]):
            raise ValueError(f"Actual CI references are not canonically sorted: {c['theorem']}")
    parent_validation = read(c["parent_validation"])
    if not parent_validation.get("kernel_types_equal") or not parent_validation.get("standard_axioms_only"):
        raise ValueError("Source-side type/Std3 certificate is not current")
    # Fresh direct imports prove the source and child owner identities and replay
    # every ordered import OLean lookup. Existing parent proof bytes/logs remain
    # pinned by their immutable validation certificate.
    source_pf = context.record(c["source_snapshot"], c["source_snapshot_manifest"],
                               "modecheck", "SourceSnapshot", V/"ap4"/c["stage"])
    child_source_pf = context.record(c["source"], c["source_manifest"], "emit-olean", c["module"], V/"ap4"/c["stage"])
    child_snapshot_pf = context.record(c["snapshot"], c["snapshot_manifest"], "modecheck", "ChildSnapshot", V/"ap4"/c["stage"])
    for output in (c["source_type"], c["source_refs"]):
        written_during(output, source_pf["data"])
    for output in (c["child_type"], c["child_refs"]):
        written_during(output, child_snapshot_pf["data"])
    for refs_path in (c["source_refs"], c["child_refs"]):
        refs_doc = read(refs_path)
        if set(refs_doc) != {"schemaVersion", "probeMainModule", "rows"} or refs_doc["schemaVersion"] != 1:
            raise ValueError(f"Proof-reference snapshot schema differs: {refs_path}")
        expected_main = "SourceSnapshot" if refs_path == c["source_refs"] else "ChildSnapshot"
        if refs_doc["probeMainModule"] != expected_main:
            raise ValueError(f"Proof-reference snapshot module differs: {refs_path}")
    source_axioms = standalone.audit_axioms(context.file(source_pf["data"]["log"]), c["theorem"])
    parent_validation_doc = read(c["parent_validation"])
    generated_record = parent_validation_doc["preflights"]["SnapshotGenerated.lean"]
    generated_log = ROOT / generated_record["log"]
    generated_snapshot = c["parent"] / "SnapshotGenerated.lean"
    generated_sidecar = read(Path(str(generated_snapshot) + ".preflight.json"))
    if (generated_record["exit_code"] != 0 or generated_record["original_exit_code"] != 0
            or generated_record["timed_out"] or generated_record["timeout_seconds"] != 300
            or generated_record["runtime_sha256"] != parent_validation_doc["runtime_sha256"]
            or generated_record["source"] != rel(generated_snapshot)
            or generated_record["source_sha256"] != sha(generated_snapshot)
            or not generated_record["source_unchanged"] or sha(generated_log) != generated_record["log_sha256"]
            or generated_sidecar.get("exit_code") != generated_record["exit_code"]
            or generated_sidecar.get("original_exit_code") != generated_record["original_exit_code"]
            or generated_sidecar.get("timed_out") != generated_record["timed_out"]
            or generated_sidecar.get("timeout_seconds") != generated_record["timeout_seconds"]
            or generated_sidecar.get("runtime_sha256") != generated_record["runtime_sha256"]
            or generated_sidecar.get("source_sha256") != generated_record["source_sha256"]
            or generated_sidecar.get("source_unchanged") != generated_record["source_unchanged"]
            or generated_sidecar.get("log") != generated_record["log"]):
        raise ValueError(f"Parent generated proof preflight changed: {c['theorem']}")
    solution_axioms = standalone.audit_axioms(generated_log, "solution")
    emitted_axioms = standalone.audit_axioms(context.file(child_source_pf["data"]["log"]), c["theorem"])
    imported_axioms = standalone.audit_axioms(context.file(child_snapshot_pf["data"]["log"]), c["theorem"])
    if any(set(x) != STD3 for x in (source_axioms, solution_axioms, emitted_axioms, imported_axioms)):
        raise ValueError(f"Source/proof/child logs do not all report exactly Std3: {c['theorem']}")
    parent_validation = read(c["parent_validation"])
    if not parent_validation.get("kernel_types_equal") or not parent_validation.get("standard_axioms_only"):
        raise ValueError("Source-side type/Std3 certificate is not current")
    cert = {"schema_version": 1, "artifact_kind": "parameter-proved-child-actual-import-validation",
            "validated": True, "stage": "verification/ap4/" + c["stage"], "theorem_name": c["theorem"],
            "module": c["module"], "child_source": rel(c["source"]), "child_source_sha256": sha(c["source"]),
            "child_olean": read(c["snapshot_manifest"])["child_olean"],
            "child_olean_sha256": read(c["snapshot_manifest"])["child_olean_sha256"],
            "child_imported_type": rel(c["child_type"]), "child_imported_type_sha256": sha(c["child_type"]),
            "child_proof_references": rel(c["child_refs"]), "child_proof_references_sha256": sha(c["child_refs"]),
            "actual_module_owner": row["owner"], "Std3_only": True,
            "source_type_certificate": rel(c["source_type"]),
            "prior_source_type_certificate": rel(c["parent"]/"original-type.json"),
            "source_validation": rel(c["parent_validation"]), "source_validation_sha256": sha(c["parent_validation"]),
            "source_publication": rel(c["publication"]), "source_publication_sha256": sha(c["publication"]),
            "source_proof_bytes_pinned": read(c["source_manifest"])["input_hashes"][task_rel(ROOT/read(c["parent_manifest"])["solution"])],
            "source_proof_and_type_certificate_pins": True,
            "imported_child_snapshot_preflight_sha256": sha(Path(str(c["snapshot"])+".preflight.json")),
            "source_preflight_replay": source_pf,
            "source_actual_owner": source_row["owner"],
            "child_source_preflight_replay": child_source_pf, "child_snapshot_preflight_replay": child_snapshot_pf,
            "source_axioms": source_axioms, "solution_axioms": solution_axioms,
            "child_source_axioms": emitted_axioms, "child_imported_axioms": imported_axioms,
            "kernel_type_equal_to_source_and_proved_solution": True,
            "max_file_seconds": max(source_pf["data"]["seconds"], generated_pf["data"]["seconds"],
                                     child_source_pf["data"]["seconds"], child_snapshot_pf["data"]["seconds"]),
            "submission_ready": False}
    dump(c["stage"] and V/"ap4"/c["stage"] / "actual-child-validation.json", cert)
    return cert


def main():
    p = argparse.ArgumentParser()
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--prepare", action="store_true")
    g.add_argument("--check-only", action="store_true")
    g.add_argument("--bind", action="store_true")
    g.add_argument("--validate-existing", action="store_true")
    p.add_argument("--stage", choices=[x[0] for x in SPECS], required=True)
    args = p.parse_args()
    c = configure(next(x for x in SPECS if x[0] == args.stage))
    if args.prepare: result = prepare(c)
    elif args.check_only: result = check_only(c)
    elif args.bind: result = bind(c)
    else: result = validate_existing(c)
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
