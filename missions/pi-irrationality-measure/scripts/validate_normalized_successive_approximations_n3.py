"""Strictly certify existing ap5/n3 evidence; never starts Lean or uses the API."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from datetime import datetime
from pathlib import Path

import formal_log_node_refs as refs
import preflight_staged_module as runner
import stage_normalized_successive_approximations_n3 as prep
import validate_formal_log_node as kernel
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

TASK, ROOT, V, STAGE = prep.TASK, prep.ROOT, prep.V, prep.STAGE
SELF = Path(__file__).resolve()
CERT = STAGE / "n3-validation.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def fail(condition: bool, message: str) -> None:
    if condition:
        raise ValueError(message)


def reconstructed(manifest: dict) -> dict:
    unit, raw = prep.source_command()
    staged = read(STAGE / "source-command.json")
    fail(staged["source_unit"] != unit, "Source AST unit reconstruction differs")
    fail(staged["raw_command_utf8"].encode("utf-8") != raw,
         "Raw source command is not the exact authoritative byte slice")
    fail(staged["raw_command_sha256"] != hashlib.sha256(raw).hexdigest(),
         "Raw source command hash differs")
    bindings = [prep.child_binding(spec) for spec in prep.CHILDREN]
    fail(not all(row["ready"] for row in bindings), "Both actual proved-child certificates are required")
    artifacts = prep.make_artifacts(bindings)
    for name, expected in artifacts.items():
        if not name.startswith("_"):
            fail((STAGE / name).read_bytes() != expected,
                 "Exact staged source reconstruction differs: " + name)
    assembled = manifest["wire_preamble"].encode() + manifest["formal_statement"].encode()
    fail(hashlib.sha256(assembled).hexdigest() != manifest["assembled_wire_theorem_sha256"],
         "Future wire theorem assembly hash differs")
    fail(manifest["publication_assembly_guard"]["satisfied"] is not False,
         "Publication assembly guard was advanced without a compiled theorem")
    return {"source_unit": unit, "raw_command_sha256": hashlib.sha256(raw).hexdigest(),
            "child_bindings": bindings, "assembled_wire_theorem_sha256": hashlib.sha256(assembled).hexdigest()}


def strict_preflight(source: Path, manifest_path: Path, module: str, child_bindings: list[dict]) -> dict:
    runner_doc = read(manifest_path)
    runner.verify_manifest_inputs(runner_doc)
    runner.verify_source_certificate(source, runner_doc)
    runner.certified_imports(source, runner_doc)
    record_path = source.with_name(source.name + ".preflight.json")
    fail(not record_path.is_file(), "Missing actual preflight record: " + rel(source))
    data = read(record_path)
    fail(data.get("success") is not True or data.get("exit_code") != 0 or data.get("timed_out") is not False,
         "Preflight did not complete successfully: " + rel(source))
    fail(data.get("mode") != "modecheck" or data.get("timeout_seconds") != 300.0,
         "Preflight mode or timeout differs: " + rel(source))
    fail(data.get("seconds", 301) > 300, "Preflight exceeded the theorem budget: " + rel(source))
    fail(data.get("source_sha256_before") != sha(source)
         or data.get("source_sha256_after") != sha(source)
         or data.get("source_unchanged") is not True,
         "Preflight source bytes were not exact and stable: " + rel(source))
    fail(data.get("manifest_sha256_before") != sha(manifest_path)
         or data.get("manifest_sha256_after") != sha(manifest_path)
         or data.get("manifest_unchanged") is not True,
         "Preflight manifest bytes were not exact and stable: " + rel(source))
    fail(data.get("runtime_sha256") != prep.RUNTIME_SHA
         or data.get("runtime_sha256_after") != prep.RUNTIME_SHA
         or data.get("runtime_unchanged") is not True,
         "Preflight runtime differs or changed: " + rel(source))
    fail(data.get("actual_module_identity") != module,
         "Actual module identity differs: " + rel(source))
    log = TASK / data.get("log", "")
    fail(not log.is_file() or sha(log) != data.get("log_sha256")
         or data.get("stdout_and_stderr_sha256") != data.get("log_sha256"),
         "Preflight log pin differs: " + rel(source))
    fail(data.get("dependencies_stable_during_compile") is not True
         or data.get("input_certificates_stable") is not True,
         "Preflight dependency/input certificates were not stable: " + rel(source))
    source_side = source.name == "SourceSnapshot.lean"
    if source_side:
        dep = next((row for row in data["dependency_oleans"] if row["module"] == prep.SOURCE_MODULE), None)
        fail(dep is None or dep.get("stable_during_compile") is not True,
             "Source theorem module was not an exact stable imported dependency")
    else:
        first = Path(data["effective_lean_path"][0]).resolve()
        fail(first != prep.STAGED_LEAN.resolve(), "Staged OLean root was not first in LEAN_PATH")
        by_module = {row["module"]: row for row in data["dependency_oleans"]}
        for child in child_bindings:
            dep = by_module.get(child["module"])
            expected_olean = (TASK / child["output_olean"]).resolve()
            fail(dep is None, "Actual child dependency missing from preflight: " + child["module"])
            fail(Path(dep["path"]).resolve() != expected_olean
                 or Path(dep["resolved_search_root"]).resolve() != prep.STAGED_LEAN.resolve()
                 or dep["sha256_before"] != child["output_olean_sha256"]
                 or dep["sha256_after"] != child["output_olean_sha256"]
                 or dep["stable_during_compile"] is not True,
                 "Actual child was not resolved from the certified first-search OLean: " + child["module"])
    return {"record": rel(record_path), "record_sha256": sha(record_path), "data": data}


def proof_reference_rows(record: dict, generated_type: list[dict]) -> list[dict]:
    output = STAGE / "proof-references.json"
    data = record["data"]
    finished = datetime.fromisoformat(data["at_utc"]).timestamp()
    fail(not finished - data["seconds"] - 2 <= output.stat().st_mtime <= finished + 2,
         "Proof-reference JSON is outside the retained WithRefs preflight write window")
    doc = read(output)
    fail(set(doc) != {"schemaVersion", "probeMainModule", "rows"}
         or doc["schemaVersion"] != 1
         or doc["probeMainModule"] != data["actual_module_identity"],
         "Proof-reference JSON schema or actual module owner differs")
    rows = doc["rows"]
    fail(not isinstance(rows, list) or [row.get("name") for row in rows] != ["solution"],
         "Proof-reference JSON must contain exactly the local solution")
    by_name = {row["name"]: row for row in generated_type}
    for row in rows:
        fail(set(row) != {"name", "userName", "kind", "levelParams", "closedType", "closedValue",
                          "typeRefs", "valueRefs", "axioms", "owner"},
             "Proof-reference row schema differs")
        fail(row["name"] != row["userName"] or row["kind"] != "theorem"
             or row["closedType"] is not True or row["closedValue"] is not True
             or row["owner"] != {"kind": "OwnModule", "module": data["actual_module_identity"]},
             "Proof-reference identity, closedness, or owner differs")
        fail(row["levelParams"] != by_name[row["name"]]["levelParams"],
             "Proof-reference universes differ from the same-run type snapshot")
        for field in ("typeRefs", "valueRefs"):
            fail(not isinstance(row[field], list) or row[field] != sorted(set(row[field])),
                 "Proof-reference names must be sorted and unique")
        fail(set(row["typeRefs"]) != refs.kernel_refs(by_name[row["name"]]["type"]),
             "Proof-reference type constants differ from the structural type snapshot")
        fail(not set(row["axioms"]) <= STD3, "Proof-reference axioms exceed Std3")
    return rows


def statement_placeholder_audit(manifest: dict, record: dict) -> dict:
    source = ROOT / manifest["statement"]
    assembled = manifest["wire_preamble"].encode() + manifest["formal_statement"].encode()
    fail(source.read_bytes() != assembled, "Compiled statement bytes differ from wire preamble + formal statement")
    fail(hashlib.sha256(assembled).hexdigest() != manifest["assembled_wire_theorem_sha256"],
         "Compiled statement assembly SHA differs")
    fail(assembled.count(b":= by sorry") != 1 or assembled.count(b"sorry") != 1,
         "Statement placeholder must contain exactly one explicit sorry proof")
    fail(re.search(rb"(^|\n)\s*(axiom|opaque)\s+", assembled) is not None,
         "Statement placeholder contains an additional axiom/opaque declaration")
    log = (TASK / record["data"]["log"]).read_text(encoding="utf-8")
    warnings = re.findall(r"warning: declaration uses `sorry`", log)
    fail(len(warnings) != 1, "Statement modecheck must report exactly one sorry placeholder warning")
    fail("error:" in log.lower(), "Statement modecheck log contains an error")
    return {
        "source": rel(source),
        "source_sha256": sha(source),
        "assembled_wire_theorem_sha256": manifest["assembled_wire_theorem_sha256"],
        "exact_wire_bytes_equal": True,
        "successful_actual_modecheck": True,
        "placeholder_proof": "sorryAx",
        "explicit_sorry_count": 1,
        "sorry_warning_count": 1,
        "additional_axiom_or_opaque_declarations": 0,
        "olean_emitted": False,
        "imported_by_proof_artifact": False,
    }


def certify() -> dict:
    prep.check()
    manifest = read(STAGE / "manifest.json")
    preparation = read(STAGE / "preparation.json")
    fail(preparation["child_bindings_ready"] is not True,
         "Preparation still binds pending children; rerun stage --prepare after child certification")
    reconstruction = reconstructed(manifest)
    children = reconstruction["child_bindings"]
    files = list(preparation["compile_manifests"])
    records = {}
    for name in files:
        source = STAGE / name
        mp = TASK / preparation["compile_manifests"][name]["manifest"]
        module = ".".join(source.relative_to(STAGE).with_suffix("").parts)
        records[name] = strict_preflight(source, mp, module, children)
    source_record = records["SourceSnapshot.lean"]
    generated_record = records["SnapshotGenerated.lean"]
    refs_record = records["SnapshotGeneratedWithRefs.lean"]
    solution_name = "Solutions/Sol_OAI_PiExponent_exists_normalized_successive_approximations.lean"
    solution_record = records[solution_name]
    statement_name = "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean"
    statement_record = records[statement_name]
    statement_audit = statement_placeholder_audit(manifest, statement_record)
    original = kernel.kernel_rows(STAGE / "original-type.json", [prep.NAME], source_record)
    generated = kernel.kernel_rows(STAGE / "generated-type.json", ["solution"], refs_record)
    kernel.same_type(original[0], generated[0])
    audits = {
        "source": standalone.audit_axioms(TASK / source_record["data"]["log"], prep.NAME),
        "generated": standalone.audit_axioms(TASK / generated_record["data"]["log"], "solution"),
        "generated_with_refs": standalone.audit_axioms(TASK / refs_record["data"]["log"], "solution"),
        "literal_solution": standalone.audit_axioms(TASK / solution_record["data"]["log"], "solution"),
    }
    fail(any(not set(value) <= STD3 for value in audits.values()), "n3 proof axioms exceed Std3")
    actual_refs = proof_reference_rows(refs_record, generated)
    fail([row["name"] for row in actual_refs] != ["solution"],
         "Proof-reference collector domain differs")
    proof = actual_refs[0]
    fail(proof["owner"] != {"kind": "OwnModule", "module": "SnapshotGeneratedWithRefs"},
         "Generated solution is not owned by the exact WithRefs module")
    fail(prep.NAME in proof["valueRefs"] or "solution" in proof["valueRefs"],
         "Generated proof self-references the target or solution")
    allowed = {row["theorem_name"] for row in children}
    project = {name for name in proof["typeRefs"] + proof["valueRefs"]
               if name.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions.", "_private.OAI."))}
    fail(project != allowed, "Generated proof project references differ: " + repr(sorted(project)))
    output_paths = [STAGE / "original-type.json", STAGE / "generated-type.json",
                    STAGE / "proof-references.json"]
    implementations = [SELF, prep.SELF, Path(refs.__file__), Path(kernel.__file__),
                       Path(context.__file__), Path(standalone.__file__),
                       Path(runner.__file__), Path(prep.refs_producer.__file__)]
    report = {
        "schema_version": 1,
        "artifact_kind": "ap5-n3-strict-kernel-certificate",
        "node": prep.KEY,
        "theorem_name": prep.NAME,
        "source_commit": prep.SOURCE_COMMIT,
        "source_url": prep.SOURCE_URL,
        "source_ast_reconstruction": reconstruction,
        "manifest_sha256": sha(STAGE / "manifest.json"),
        "preparation_sha256": sha(STAGE / "preparation.json"),
        "academic_metadata_sha256": sha(STAGE / "academic-metadata.json"),
        "certified_inputs_sha256": sha(STAGE / "certified-inputs.json"),
        "child_certificates": children,
        "preflights": records,
        "formal_types_equal": True,
        "compiled_statement_type_matches_source_and_solution": True,
        "compiled_statement_type_basis": (
            "exact canonical source/statement/solution type text plus successful statement modecheck "
            "and source/solution structural kernel equality"),
        "source_type_name": prep.NAME,
        "generated_type_name": "solution",
        "proof_references": actual_refs,
        "project_proof_references": sorted(project),
        "axiom_audits": {key: sorted(value) for key, value in audits.items()},
        "proof_axioms": "Std3",
        "statement_placeholder_audit": statement_audit,
        "strict_actual_preflight_log_runtime_and_first_search_owner": True,
        "max_file_seconds": max(row["data"]["seconds"] for row in records.values()),
        "input_hashes": manifest["input_hashes"],
        "reconstruction_pins": {
            "source_command": manifest["source_command_sha256"],
            "assembled_wire_theorem": manifest["assembled_wire_theorem_sha256"],
            "snapshot_outputs": manifest["snapshot_outputs"],
        },
        "implementation_hashes": {rel(path): sha(path) for path in implementations},
        "output_json_sha256": {rel(path): sha(path) for path in output_paths},
        "publication_assembly_guard": {
            **manifest["publication_assembly_guard"],
            "actual_compiled_theorem_preflight": statement_record["record"],
            "actual_compiled_theorem_preflight_sha256": statement_record["record_sha256"],
            "satisfied": True,
        },
        "target_statement_stub_source_staged": True,
        "target_statement_stub_olean_emitted": False,
        "target_statement_stub_imported_by_proof_artifact": False,
        "validated": True,
        "Lean_started_by_validator": False,
        "API_used": False,
        "submission_ready": False,
    }
    raw = (json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8")
    if CERT.exists() and CERT.read_bytes() != raw:
        raise ValueError("Existing n3 certificate differs; preserve it before recertification")
    if not CERT.exists():
        CERT.write_bytes(raw)
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certify-existing", action="store_true", required=True)
    args = parser.parse_args()
    print(json.dumps(certify(), indent=2, ensure_ascii=False))
