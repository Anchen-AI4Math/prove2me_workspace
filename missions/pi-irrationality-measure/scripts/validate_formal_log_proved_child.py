"""Certify the actual imported theorem module produced from the f1 solution.

This checker is read-only except for ``--certify-existing``.  It never invokes
Lean or an API; it replays the frozen byte transformation and verifies the two
retained preflight records and their exported kernel evidence.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import generate_formal_log_truncation_provider as formal
import stage_formal_log_proved_child as emitter
import validate_formal_log_node as parent
import validate_formal_log_truncation_provider as formalcert
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

TASK, ROOT, V = formal.TASK, formal.ROOT, formal.V
STAGE = V / "flp3/c1"
F1 = V / "flp3/f1"
CERT_NAME = "proved-child-validation.json"
SELF = Path(__file__).resolve()
sha, read, rel, fail = context.sha, context.read, context.rel, context.fail


def stage_path(value=STAGE):
    path = Path(value)
    if not path.is_absolute():
        path = TASK / path if path.parts and path.parts[0] == "verification" else V / path
    path = path.resolve()
    fail(path != STAGE.resolve() or not path.is_dir(), "Only the actual FormalLog c1 stage is supported")
    return path


def reconstruct_source(parent_result):
    preparation = read(emitter.SOURCE_PREPARATION)
    expected_rows = [
        (b"theorem solution (",
         ("theorem " + emitter.THEOREM + " (").encode()),
        (b"#print axioms solution",
         ("#print axioms " + emitter.THEOREM).encode()),
    ]
    fail(preparation.get("parent_node") != emitter.NODE
         or preparation.get("parent_node_certificate") != parent_result["certificate"]["path"]
         or preparation.get("parent_node_certificate_sha256") != parent_result["certificate"]["sha256"]
         or preparation.get("certified_solution") != rel(ROOT / parent_result["manifest_data"]["solution"])
         or preparation.get("certified_solution_sha256") != sha(ROOT / parent_result["manifest_data"]["solution"])
         or preparation.get("module") != emitter.MODULE
         or preparation.get("theorem_name") != emitter.THEOREM
         or preparation.get("only_literal_binding_and_axiom_marker_renamed") is not True
         or preparation.get("statement_stub_imported") is not False,
         "Proved child source preparation is not bound to exact f1 evidence")
    source = parent_result["solution_bytes"]
    ledger = preparation.get("edit_ledger")
    fail(not isinstance(ledger, list) or len(ledger) != 2, "Expected exactly two proved-child edits")
    for actual, (old, new) in zip(ledger, expected_rows, strict=True):
        fail(source.count(old) != 1 or source.count(new) != 0, "Proved-child edit is not unique/fresh")
        start = source.index(old)
        expected = {"start": start, "end": start + len(old),
                    "source": old.decode(), "replacement": new.decode()}
        fail(actual != expected, "Proved-child edit ledger differs from the exact literal edit")
        source = source.replace(old, new, 1)
    fail(source != emitter.SOURCE.read_bytes() or b"sorry" in source
         or b"theorem solution (" in source or b"#print axioms solution" in source,
         "Proved child is not the exact sorry-free certified solution rebinding")
    fail(preparation.get("output") != rel(emitter.SOURCE)
         or preparation.get("output_sha256") != sha(emitter.SOURCE),
         "Proved child output binding differs")
    return preparation


def source_manifest(parent_result):
    manifest = read(emitter.SOURCE_MANIFEST)
    parent_manifest = parent_result["manifest_data"]
    parent_cert = TASK / parent_result["certificate"]["path"]
    expected_pins = {
        rel(Path(emitter.__file__)): sha(Path(emitter.__file__)),
        rel(Path(parent.__file__)): sha(Path(parent.__file__)),
        rel(parent_cert): sha(parent_cert),
        rel(parent_result["manifest"]): sha(parent_result["manifest"]),
        rel(ROOT / parent_manifest["solution"]): sha(ROOT / parent_manifest["solution"]),
    }
    expected = {
        "schema_version": 1,
        "artifact_kind": "proved-formal-log-child-module-import-certificate",
        "output": emitter.SOURCE.relative_to(ROOT).as_posix(),
        "output_sha256": sha(emitter.SOURCE),
        "imports": parent_manifest["imports"],
        "input_hashes": expected_pins,
        "runtime_sha256": parent_manifest["runtime_sha256"],
        "parent_node_certificate": rel(parent_cert),
        "parent_node_certificate_sha256": sha(parent_cert),
        "theorem_name": emitter.THEOREM,
        "module": emitter.MODULE,
        "emit_olean_required": True,
        "timeout_seconds": 300,
        "validated": False,
        "submission_ready": False,
    }
    fail(manifest != expected, "Proved child source manifest differs from exact reconstruction")
    return manifest


def reconstruct_snapshot(parent_result, child_olean):
    preparation, manifest = read(emitter.SNAPSHOT_PREPARATION), read(emitter.SNAPSHOT_MANIFEST)
    source_record = Path(str(emitter.SOURCE) + ".preflight.json")
    parent_cert = TASK / parent_result["certificate"]["path"]
    core_path = V / "TypeOnlyTheoremSnapshotCore.inc"
    core = core_path.read_text(encoding="utf-8")
    expected_source = ("import Lean\nimport " + emitter.MODULE + "\n\n" + core + emitter.IMPORTED_REFS
        + "\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\n"
        + "run_meta do\n  PiExponentInterfaceSnapshot.exportSnapshot #[`" + emitter.THEOREM + "] "
        + json.dumps(formal.provider.workspace_relative(emitter.CHILD_TYPE)) + "\n"
        + "run_meta do\n  FormalLogImportedChildSnapshot.exportChild `" + emitter.THEOREM + " "
        + json.dumps(emitter.MODULE) + " "
        + json.dumps(formal.provider.workspace_relative(emitter.CHILD_REFS)) + "\n"
        + "#print axioms " + emitter.THEOREM + "\n").encode()
    fail(emitter.SNAPSHOT.read_bytes() != expected_source, "Child snapshot source differs from exact frozen emitter")
    pins = {
        rel(Path(emitter.__file__)): sha(Path(emitter.__file__)),
        rel(parent_cert): sha(parent_cert),
        rel(emitter.SOURCE): sha(emitter.SOURCE),
        rel(emitter.SOURCE_MANIFEST): sha(emitter.SOURCE_MANIFEST),
        rel(source_record): sha(source_record),
        rel(child_olean): sha(child_olean),
        "verification/TypeOnlyTheoremSnapshotCore.inc": sha(core_path),
    }
    expected_manifest = {
        "schema_version": 1,
        "artifact_kind": "proved-formal-log-child-snapshot-import-certificate",
        "output": emitter.SNAPSHOT.relative_to(ROOT).as_posix(),
        "output_sha256": sha(emitter.SNAPSHOT),
        "imports": ["Lean", emitter.MODULE],
        "input_hashes": pins,
        "runtime_sha256": parent_result["manifest_data"]["runtime_sha256"],
        "theorem_name": emitter.THEOREM,
        "child_module": emitter.MODULE,
        "child_olean": rel(child_olean),
        "child_olean_sha256": sha(child_olean),
        "timeout_seconds": 300,
        "validated": False,
        "submission_ready": False,
    }
    fail(manifest != expected_manifest, "Child snapshot manifest differs from exact reconstruction")
    expected_preparation = {
        "schema_version": 1,
        "artifact_kind": "proved-formal-log-child-snapshot-preparation",
        "source": rel(emitter.SNAPSHOT),
        "source_sha256": sha(emitter.SNAPSHOT),
        "manifest": rel(emitter.SNAPSHOT_MANIFEST),
        "manifest_sha256": sha(emitter.SNAPSHOT_MANIFEST),
        "child_module": emitter.MODULE,
        "child_olean": rel(child_olean),
        "child_olean_sha256": sha(child_olean),
        "type_output": rel(emitter.CHILD_TYPE),
        "proof_reference_output": rel(emitter.CHILD_REFS),
        "actual_imported_owner_required": True,
        "Std3_required": True,
        "Lean_started": False,
        "validated": False,
        "submission_ready": False,
    }
    fail(preparation != expected_preparation, "Child snapshot preparation differs from exact reconstruction")
    return manifest


def proof_row(path, snapshot_pf):
    formalcert.written_during(path, snapshot_pf)
    document = read(path)
    fail(set(document) != {"schemaVersion", "probeMainModule", "rows"}
         or document["schemaVersion"] != 1
         or document["probeMainModule"] != "ChildSnapshot"
         or not isinstance(document["rows"], list) or len(document["rows"]) != 1,
         "Imported child proof-reference document schema differs")
    row = document["rows"][0]
    fail(set(row) != {"name", "kind", "levelParams", "closedType", "closedValue",
                     "typeRefs", "valueRefs", "axioms", "owner"}
         or row["name"] != emitter.THEOREM or row["kind"] != "theorem"
         or row["closedType"] is not True or row["closedValue"] is not True,
         "Imported child proof row identity/closure differs")
    fail(not isinstance(row["levelParams"], list)
         or any(not isinstance(x, str) for x in row["levelParams"])
         or len(set(row["levelParams"])) != len(row["levelParams"]),
         "Imported child universe binder list is invalid")
    for key in ("typeRefs", "valueRefs", "axioms"):
        values = row[key]
        fail(not isinstance(values, list) or any(not isinstance(x, str) for x in values)
             or len(values) != len(set(values)), "Imported child " + key + " has invalid/duplicate names")
        if key != "axioms":
            fail(values != sorted(values), "Imported child " + key + " is not sorted")
    fail(set(row["axioms"]) != context.STD3, "Imported child does not use exactly Std3")
    owner = row["owner"]
    fail(set(owner) != {"kind", "module", "index"} or owner["kind"] != "ImportedModule"
         or owner["module"] != emitter.MODULE or type(owner["index"]) is not int or owner["index"] < 0,
         "Imported child theorem owner differs from its actual theorem module")
    refs = set(row["typeRefs"]) | set(row["valueRefs"])
    fail(emitter.THEOREM in refs or "solution" in refs,
         "Imported child proof refers to itself or the generated solution binding")
    return row


def certify(stage=STAGE):
    stage = stage_path(stage)
    parent_result = parent.validate_formal_node(F1)
    parent_data = parent_result["certificate"]["data"]
    preparation = reconstruct_source(parent_result)
    source_manifest(parent_result)
    source_pf = context.record(emitter.SOURCE, emitter.SOURCE_MANIFEST, "emit-olean", emitter.MODULE, stage)
    child_olean = V / "staged-build/lib/lean" / Path(*emitter.MODULE.split(".")).with_suffix(".olean")
    fail(source_pf["data"]["output_olean_sha256"] != sha(child_olean), "Child OLean differs from actual source preflight")
    reconstruct_snapshot(parent_result, child_olean)
    snapshot_pf = context.record(emitter.SNAPSHOT, emitter.SNAPSHOT_MANIFEST, "modecheck", "ChildSnapshot", stage)
    child_dep = next((d for d in snapshot_pf["data"]["dependency_oleans"] if d["module"] == emitter.MODULE), None)
    fail(child_dep is None or child_dep["sha256_before"] != sha(child_olean),
         "Child snapshot did not import the exact emitted theorem OLean")

    parent_pf = parent_data["preflights"]["SnapshotGeneratedWithRefs2.lean"]
    parent_types = parent.kernel_rows(F1 / "generated-type.json", [emitter.THEOREM, "solution"], parent_pf)
    child_types = parent.kernel_rows(emitter.CHILD_TYPE, [emitter.THEOREM], snapshot_pf)
    parent.same_type(parent_types[0], parent_types[1])
    parent.same_type(parent_types[0], child_types[0])

    fail(parent_data["output_json_sha256"].get("proof-references.json") != sha(F1 / "proof-references.json"),
         "Parent proof-reference output differs from its certificate")
    parent_rows = read(F1 / "proof-references.json")["rows"]
    parent_solution = next((row for row in parent_rows if row.get("name") == "solution"), None)
    fail(parent_solution is None, "Parent certificate has no exact solution proof row")
    child_proof = proof_row(emitter.CHILD_REFS, snapshot_pf)
    for key in ("levelParams", "typeRefs", "valueRefs", "axioms"):
        fail(child_proof[key] != parent_solution[key], "Imported child proof differs from certified f1 solution: " + key)
    source_audit = standalone.audit_axioms(TASK / source_pf["data"]["log"], emitter.THEOREM)
    snapshot_audit = standalone.audit_axioms(TASK / snapshot_pf["data"]["log"], emitter.THEOREM)
    fail(set(source_audit) != context.STD3 or set(snapshot_audit) != set(child_proof["axioms"]),
         "Child source/imported #print axioms differs from exact Std3 proof exporter")
    graph_names = set(parent_data["actual_definition_provided_names"])
    project_refs = sorted(name for name in set(child_proof["typeRefs"] + child_proof["valueRefs"])
                          if name in graph_names or name.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions.", "_private.OAI.")))
    fail(not set(project_refs) <= set(parent_data["allowed_project_names"]),
         "Imported child proof uses project constants outside the f1 certified interface")
    implementation = {rel(path): sha(path) for path in
                      [SELF, Path(emitter.__file__), Path(parent.__file__), Path(formalcert.__file__),
                       Path(context.__file__), Path(standalone.__file__)]}
    return {
        "schema_version": 1,
        "artifact_kind": "formal-log-proved-child-kernel-certificate",
        "validated": True,
        "parent_node": emitter.NODE,
        "parent_node_certificate": parent_result["certificate"]["path"],
        "parent_node_certificate_sha256": parent_result["certificate"]["sha256"],
        "theorem_name": emitter.THEOREM,
        "module": emitter.MODULE,
        "source": rel(emitter.SOURCE),
        "source_sha256": sha(emitter.SOURCE),
        "source_preparation": rel(emitter.SOURCE_PREPARATION),
        "source_preparation_sha256": sha(emitter.SOURCE_PREPARATION),
        "source_manifest": rel(emitter.SOURCE_MANIFEST),
        "source_manifest_sha256": sha(emitter.SOURCE_MANIFEST),
        "output_olean": rel(child_olean),
        "output_olean_sha256": sha(child_olean),
        "snapshot": rel(emitter.SNAPSHOT),
        "snapshot_sha256": sha(emitter.SNAPSHOT),
        "snapshot_manifest": rel(emitter.SNAPSHOT_MANIFEST),
        "snapshot_manifest_sha256": sha(emitter.SNAPSHOT_MANIFEST),
        "child_type_output": rel(emitter.CHILD_TYPE),
        "child_type_output_sha256": sha(emitter.CHILD_TYPE),
        "child_proof_references": rel(emitter.CHILD_REFS),
        "child_proof_references_sha256": sha(emitter.CHILD_REFS),
        "exact_certified_solution_rebinding": True,
        "literal_edit_count": len(preparation["edit_ledger"]),
        "statement_stub_imported": False,
        "actual_imported_owner": True,
        "kernel_type_equal_to_parent_source_target_solution": True,
        "proof_type_refs_equal_to_f1_solution": True,
        "proof_value_refs_equal_to_f1_solution": True,
        "proof_self_reference_absent": True,
        "actual_project_reference_coverage_complete": True,
        "actual_project_refs": project_refs,
        "Std3_only": True,
        "proof_axioms": "Std3",
        "axioms": {"child_module": source_audit, "imported_snapshot": snapshot_audit},
        "preflights": {"child_module": source_pf, "imported_snapshot": snapshot_pf},
        "max_file_seconds": max(source_pf["data"]["seconds"], snapshot_pf["data"]["seconds"]),
        "implementation_hashes": implementation,
        "server_parent_pending": True,
        "submission_ready": False,
    }


def validate_proved_child(stage=STAGE):
    """Read-only successor interface for the exact local proved child."""
    stage = stage_path(stage)
    certificate = certify(stage)
    path = stage / CERT_NAME
    fail(not path.is_file() or read(path) != certificate,
         "Proved-child certificate is missing/stale after full readonly replay")
    return {"stage": stage,
            "certificate": {"path": rel(path), "sha256": sha(path), "data": certificate},
            "validated": True, "server_parent_pending": True, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", nargs="?", default="verification/flp3/c1")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-only", action="store_true")
    mode.add_argument("--certify-existing", action="store_true")
    mode.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    try:
        stage = stage_path(args.stage)
        if args.check_only:
            certificate = certify(stage)
            output = {"validated": False, "actual_evidence_checked": True,
                      "max_file_seconds": certificate["max_file_seconds"], "submission_ready": False}
        elif args.certify_existing:
            certificate = certify(stage)
            path = stage / CERT_NAME
            context.write_exact(path, certificate)
            output = {"validated": True, "certificate": rel(path), "sha256": sha(path),
                      "max_file_seconds": certificate["max_file_seconds"], "submission_ready": False}
        else:
            result = validate_proved_child(stage)
            output = {"validated": True, "certificate": result["certificate"]["path"],
                      "sha256": result["certificate"]["sha256"], "submission_ready": False}
        print(json.dumps(output, indent=2))
    except (ValueError, KeyError, FileNotFoundError, TypeError, StopIteration) as error:
        print(json.dumps({"validated": False, "status": "rejected", "error": str(error)}))
        raise SystemExit(2)


if __name__ == "__main__":
    main()
