"""Strict read-only consumer for already compiled ap6/a1 modecheck records."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from datetime import datetime

import stage_admissible_parent_a1f as prep
import validate_formal_log_node as kernel
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

TASK, ROOT, V, STAGE = prep.TASK, prep.ROOT, prep.V, prep.STAGE
CERT = STAGE / "a1-validation.json"
ORIGINAL_CONSUMER = TASK / "scripts/certify_admissible_parent_a1f_existing.py"
SELF = Path(__file__).resolve()
sha, read, rel, fail = context.sha, context.read, context.rel, context.fail


def refs(tree):
    out = set()
    def visit(node):
        if isinstance(node, list):
            if len(node) == 3 and node[0] == "const" and isinstance(node[1], str):
                out.add(node[1])
            for item in node:
                visit(item)
    visit(tree)
    return out


def imported(pf, dependency):
    rows = [x for x in pf["data"]["dependency_oleans"] if x.get("module") == dependency["module"]]
    fail(len(rows) != 1, "Expected one imported actual dependency: " + dependency["module"])
    row = rows[0]
    path = TASK / dependency["olean"]
    fail(Path(row["path"]).resolve() != path.resolve()
         or row.get("sha256_before") != dependency["olean_sha256"]
         or row.get("sha256_after") != dependency["olean_sha256"]
         or row.get("stable_during_compile") is not True,
         "First-search imported OLean changed or differs: " + dependency["module"])
    return row


def output_json(path, pf):
    data = read(path)
    finished = datetime.fromisoformat(pf["data"]["at_utc"]).timestamp()
    fail(not finished - pf["data"]["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "Exported JSON was not written during this exact compiler run: " + rel(path))
    return data


def compile_records(manifest, preparation):
    records = {}
    for index, filename in enumerate(preparation["order"], 1):
        source = STAGE / filename
        mp = STAGE / f"c{index}.json"
        doc = read(mp)
        fail(doc.get("mode") != "modecheck" or doc.get("emit_olean") is not False,
             "Comparator/preflight must be modecheck with no OLean emission: " + filename)
        module = ".".join(source.relative_to(STAGE).with_suffix("").parts)
        record = context.record(source, mp, "modecheck", module, STAGE)
        data = record["data"]
        fail(data.get("exit_code") != 0 or data.get("timed_out") is not False
             or data.get("seconds", 10**9) > 300,
             "Existing exact bounded modecheck did not pass: " + filename)
        records[filename] = record
    return records


def certify():
    prep.check_outputs(prep.stage_files())
    manifest, preparation = read(STAGE / "manifest.json"), read(STAGE / "preparation.json")
    fail(manifest.get("validated") is not False or manifest.get("submission_ready") is not False
         or manifest.get("proposal_status") != "Draft", "Stage must remain an unvalidated Draft")
    expected_source_owners = {name: prep.SOURCE_MODULE for name in prep.SOURCE_HELPERS[:3]}
    expected_source_owners.update({name: prep.DIM_SOURCE_MODULE for name in prep.SOURCE_HELPERS[3:]})
    expected_source_owners.update({name: prep.PARAM_SOURCE_MODULE for name in prep.PARAMETER_HELPERS})
    expected_source_owners[prep.SOURCE_NAME] = prep.SOURCE_MODULE
    fail(manifest.get("source_owner_by_name") != expected_source_owners,
         "Exact source AST module owners differ for theorem/helper names")
    fail(preparation.get("Lean_started") is not False or preparation.get("API_used") is not False
         or preparation.get("target_comparator_modecheck_only") is not True,
         "Preparation state must describe staging only and comparator modecheck")
    thm = STAGE / "Theorems/Thm_OAI_PiExponent_exists_admissible_parameters_source017.lean"
    solution = STAGE / "Solutions/Sol_OAI_PiExponent_exists_admissible_parameters_source017.lean"
    assembled = (manifest["preamble"] + manifest["formal_statement"]).encode("utf-8")
    fail(thm.read_bytes() != assembled, "Compiled Thm bytes differ from manifest preamble + formal statement")
    fail(hashlib.sha256(assembled).hexdigest() != preparation["compiled_statement_assembly_sha256"],
         "Frozen target assembly hash differs")
    fail(not manifest["formal_statement"].startswith("theorem " + prep.NAME),
         "Target comparator is not bound to the source017 fully qualified name")
    fail(b"sorry" in solution.read_bytes(), "Generated solution still contains sorry")

    records = compile_records(manifest, preparation)
    comparator_pf = records["Theorems/Thm_OAI_PiExponent_exists_admissible_parameters_source017.lean"]
    fail(comparator_pf["data"].get("output_olean") is not None
         or comparator_pf["data"].get("output_olean_sha256") is not None,
         "Sorry comparator unexpectedly emitted an OLean")
    source_pf, generated_pf = records["SourceSnapshot.lean"], records["SnapshotGeneratedWithRefs.lean"]
    original = kernel.kernel_rows(STAGE / "source-type.json", [*prep.ALL_HELPERS, prep.SOURCE_NAME], source_pf)
    generated = kernel.kernel_rows(STAGE / "generated-type.json", [*prep.ALL_HELPERS, prep.NAME, "solution"], generated_pf)
    for i, helper in enumerate(prep.ALL_HELPERS):
        kernel.same_type(original[i], generated[i])
    kernel.same_type(original[-1], generated[len(prep.ALL_HELPERS)])
    kernel.same_type(original[-1], generated[len(prep.ALL_HELPERS) + 1])
    source_imports = {row.get("module") for row in source_pf["data"]["dependency_oleans"]}
    fail(not {prep.SOURCE_MODULE, prep.PARAM_SOURCE_MODULE} <= source_imports,
         "Original source snapshot did not import both exact source declaration modules")

    solution_pf = records["Solutions/Sol_OAI_PiExponent_exists_admissible_parameters_source017.lean"]
    for pf in (solution_pf, generated_pf):
        for dep in manifest["definition_dependencies"]:
            imported(pf, dep)
        for dep in manifest["proved_child_dependencies"]:
            imported(pf, dep)

    refs_path = STAGE / "proof-references.json"
    refs_doc = output_json(refs_path, generated_pf)
    output_json(STAGE / "source-type.json", source_pf)
    output_json(STAGE / "generated-type.json", generated_pf)
    expected_names = [*prep.ALL_HELPERS, "solution"]
    fail(set(refs_doc) != {"schemaVersion", "probeMainModule", "rows"}
         or refs_doc["schemaVersion"] != 1
         or refs_doc["probeMainModule"] != generated_pf["data"]["actual_module_identity"],
         "Proof-reference export schema or owner module differs")
    rows = refs_doc["rows"]
    fail([row.get("name") for row in rows] != expected_names, "Proof-reference domain differs")
    generated_by_name = {row["name"]: row for row in generated}
    for row in rows:
        name = row["name"]
        expected_owner = ({"kind": "ImportedModule", "module": prep.DEF_PARAMS}
                          if name == "OAI.PiExponent.Parameters.A_pos"
                          else {"kind": "OwnModule", "module": generated_pf["data"]["actual_module_identity"]})
        fail(set(row) != {"name", "kind", "levelParams", "closedType", "closedValue", "typeRefs",
                          "valueRefs", "axioms", "owner"}
             or row["kind"] != "theorem" or row["closedType"] is not True or row["closedValue"] is not True
             or row["owner"] != expected_owner
             or row["levelParams"] != sorted(set(row["levelParams"]))
             or row["typeRefs"] != sorted(set(row["typeRefs"]))
             or row["valueRefs"] != sorted(set(row["valueRefs"]))
             or not isinstance(row["axioms"], list) or not set(row["axioms"]) <= context.STD3
             or name not in generated_by_name
             or set(row["typeRefs"]) != refs(generated_by_name[name]["type"]),
             "Proof-reference closure/owner/type mismatch: " + name)
    project_refs = {name for row in rows for field in ("typeRefs", "valueRefs") for name in row[field]
                    if name.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions."))}
    allowed = set(manifest["allowed_project_proof_references"])
    fail(not project_refs <= allowed, "Project proof references exceed exact dependency closure: "
         + str(sorted(project_refs - allowed)))

    source_log = context.file(source_pf["data"]["log"])
    generated_log = context.file(generated_pf["data"]["log"])
    source_axioms = {name: standalone.audit_axioms(source_log, name)
                     for name in [*prep.ALL_HELPERS, prep.SOURCE_NAME]}
    solution_axioms = standalone.audit_axioms(context.file(solution_pf["data"]["log"]), "solution")
    fail(any(not set(ax) <= context.STD3 for ax in source_axioms.values())
         or not set(solution_axioms) <= context.STD3, "Axiom audit exceeds Std3")

    output_json_paths = [STAGE / x for x in ("source-type.json", "generated-type.json", "proof-references.json")]
    report = {
        "schema_version": 1, "artifact_kind": "ap6-a1-admissible-parent-strict-existing-certificate",
        "stage": rel(STAGE), "source_name": prep.SOURCE_NAME, "theorem_name": prep.NAME,
        "source_commit": prep.COMMIT, "stage_manifest_sha256": sha(STAGE / "manifest.json"),
        "preparation_sha256": sha(STAGE / "preparation.json"),
        "consumer_provenance": {"active_consumer_path": rel(SELF), "active_consumer_sha256": sha(SELF),
            "original_staged_consumer_path": rel(ORIGINAL_CONSUMER),
            "original_staged_consumer_sha256": sha(ORIGINAL_CONSUMER),
            "change": "renamed output_json_paths local to preserve output_json() calls; all certificate gates copied"},
        "implementation_hashes": {rel(Path(prep.__file__)): sha(Path(prep.__file__)),
            rel(SELF): sha(SELF), rel(Path(context.__file__)): sha(Path(context.__file__)),
            rel(Path(kernel.__file__)): sha(Path(kernel.__file__)),
            rel(Path(standalone.__file__)): sha(Path(standalone.__file__))},
        "definition_dependencies": manifest["definition_dependencies"],
        "proved_child_dependencies": [{k: v for k, v in row.items() if k != "certificate"}
                                       for row in manifest["proved_child_dependencies"]],
        "preflights": records,
        "compiled_Thm_exact_assembly": {"preamble_sha256": hashlib.sha256(manifest["preamble"].encode()).hexdigest(),
            "formal_statement_sha256": hashlib.sha256(manifest["formal_statement"].encode()).hexdigest(),
            "compiled_file_sha256": sha(thm), "byte_equal": True},
        "type_equalities": [{"source": prep.SOURCE_NAME, "generated": prep.NAME, "equal": True},
                            {"source": prep.SOURCE_NAME, "generated": "solution", "equal": True},
                            *[{"source": name, "generated": name, "equal": True} for name in prep.ALL_HELPERS]],
        "source_axioms": {k: sorted(v) for k, v in source_axioms.items()},
        "solution_axioms": sorted(solution_axioms), "proof_references": rows,
        "project_proof_references": sorted(project_refs),
        "output_json_sha256": {rel(path): sha(path) for path in output_json_paths},
        "max_file_seconds": max(row["data"]["seconds"] for row in records.values()),
        "validated": True, "Lean_started_by_consumer": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft",
    }
    raw = (json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode()
    if CERT.exists() and CERT.read_bytes() != raw:
        raise ValueError("Existing a1 validation differs; refusing overwrite")
    if not CERT.exists():
        CERT.write_bytes(raw)
    return report


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certify-existing", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(certify(), ensure_ascii=False, indent=2))
