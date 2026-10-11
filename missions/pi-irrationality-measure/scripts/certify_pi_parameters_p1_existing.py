"""Strict, read-only consumer for already compiled Parameters p1 artifacts.

Only successful existing preflight sidecars are read.  This consumer never
starts Lean, never calls the platform, and refuses to rewrite a prior result.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from datetime import datetime

import prepare_pi_parameters_p1 as prep
import validate_formal_log_node as kernel
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

TASK, ROOT, V, STAGE = prep.TASK, prep.ROOT, prep.V, prep.STAGE
CERT = STAGE / "p1-validation.json"
SELF = Path(__file__).resolve()
sha, read, rel, fail = context.sha, context.read, context.rel, context.fail


def output_json(path: Path, pf: dict):
    data = read(path)
    finished = datetime.fromisoformat(pf["data"]["at_utc"]).timestamp()
    fail(not finished - pf["data"]["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "JSON output was not written during its exact compiler run: " + rel(path))
    return data


def dependency(pf: dict, module: str, path: Path, digest: str):
    rows = [x for x in pf["data"]["dependency_oleans"] if x.get("module") == module]
    fail(len(rows) != 1, "Expected one actual import dependency: " + module)
    row = rows[0]
    expected_path = path.resolve()
    fail(Path(row["path"]).resolve() != expected_path
         or row.get("sha256_before") != digest or row.get("sha256_after") != digest
         or row.get("stable_during_compile") is not True,
         "First-search dependency OLean differs or changed during compile: " + module)
    return row


def kernel_refs(tree) -> set[str]:
    found: set[str] = set()
    def visit(node):
        if not isinstance(node, list):
            return
        if node and node[0] == "const" and len(node) == 3 and isinstance(node[1], str):
            found.add(node[1])
        for part in node:
            visit(part)
    visit(tree)
    return found


def compile_records(manifest: dict, preparation: dict):
    names = list(preparation["order"])
    records = {}
    for index, filename in enumerate(names, 1):
        source = STAGE / filename
        mp = STAGE / f"c{index}.json"
        doc = read(mp)
        fail(doc.get("mode") != "modecheck",
             "Compiler manifest mode differs: " + filename)
        module = ".".join(source.relative_to(STAGE).with_suffix("").parts)
        current = context.record(source, mp, doc["mode"], module, STAGE)
        fail(current["data"].get("exit_code") != 0 or current["data"].get("timed_out") is not False
             or current["data"].get("seconds", 10**9) > 300,
             "Exact staged file did not pass its bounded compiler run: " + filename)
        records[filename] = current
    return records


def certify() -> dict:
    # Reconstruct every staged byte and reject stale or hand-edited manifests.
    prep.check_outputs(prep.stage_files())
    manifest, preparation = read(STAGE / "manifest.json"), read(STAGE / "preparation.json")
    fail(manifest.get("validated") is not False or manifest.get("submission_ready") is not False
         or manifest.get("proposal_status") != "Draft", "Staging manifest state is not an unvalidated Draft")
    fail(preparation.get("validated") is not False or preparation.get("Lean_started") is not False
         or preparation.get("API_used") is not False or preparation.get("single_compiler_sequential") is not True,
         "Preparation state claims compilation/API use or loses the sequential budget")

    statement_path = STAGE / "Theorems/Thm_OAI_PiExponent_exists_parameters.lean"
    solution_path = STAGE / "Solutions/Sol_OAI_PiExponent_exists_parameters.lean"
    assembled = (manifest["preamble"] + manifest["formal_statement"]).encode("utf-8")
    fail(statement_path.read_bytes() != assembled,
         "Compiled Thm bytes differ from exact manifest.preamble + manifest.formal_statement")
    fail(sha_bytes(assembled) != preparation["compiled_statement_assembly_sha256"],
         "Frozen theorem statement assembly digest differs")
    fail(manifest["formal_statement"].splitlines()[0].startswith("theorem " + prep.NAME + " ") is False,
         "Platform theorem target is not the source's fully qualified public name")

    structural = read(V / manifest["definition_dependency"]["structural_certificate"])
    child = read(V / manifest["proved_child_dependency"]["actual_child_certificate"])
    fail(sha(V / manifest["definition_dependency"]["structural_certificate"])
         != manifest["definition_dependency"]["structural_certificate_sha256"]
         or structural.get("validated") is not True or structural.get("types_equal") is not True
         or structural.get("definition_values_equal") is not True
         or structural.get("axioms_equal_and_std3") is not True
         or structural.get("platform_module") != prep.DEF_MODULE
         or structural.get("family_root") != prep.DEF_NAME,
         "Actual public Parameters structural certificate is not exact or complete")
    fail(child.get("validated") is not True or child.get("Std3_only") is not True
         or child.get("module") != prep.CHILD_MODULE
         or child.get("actual_module_owner", {}).get("module") != prep.CHILD_MODULE
         or child.get("actual_module_owner", {}).get("kind") != "ImportedModule"
         or child.get("child_olean_sha256") != manifest["proved_child_dependency"]["olean_sha256"],
         "Actual c2 proved child module/owner/Std3 binding differs")

    records = compile_records(manifest, preparation)
    thm_file = Path("Theorems/Thm_OAI_PiExponent_exists_parameters.lean").as_posix()
    sol_file = Path("Solutions/Sol_OAI_PiExponent_exists_parameters.lean").as_posix()
    thm_pf, sol_pf = records[thm_file], records[sol_file]
    params_dep = dependency(thm_pf, prep.DEF_MODULE, V / manifest["definition_dependency"]["first_search_olean"],
                            manifest["definition_dependency"]["first_search_olean_sha256"])
    child_dep = dependency(thm_pf, prep.CHILD_MODULE, V / manifest["proved_child_dependency"]["olean"],
                           manifest["proved_child_dependency"]["olean_sha256"])
    dependency(sol_pf, prep.DEF_MODULE, V / manifest["definition_dependency"]["first_search_olean"],
               manifest["definition_dependency"]["first_search_olean_sha256"])
    dependency(sol_pf, prep.CHILD_MODULE, V / manifest["proved_child_dependency"]["olean"],
               manifest["proved_child_dependency"]["olean_sha256"])

    source_pf = records["SnapshotOriginal.lean"]
    generated_pf = records["SnapshotGeneratedWithRefs.lean"]
    dependency(generated_pf, prep.DEF_MODULE, V / manifest["definition_dependency"]["first_search_olean"],
               manifest["definition_dependency"]["first_search_olean_sha256"])
    dependency(generated_pf, prep.CHILD_MODULE, V / manifest["proved_child_dependency"]["olean"],
               manifest["proved_child_dependency"]["olean_sha256"])
    original = kernel.kernel_rows(STAGE / "original-type.json", [prep.HELPER, prep.NAME], source_pf)
    generated = kernel.kernel_rows(STAGE / "generated-type.json", [prep.HELPER, prep.NAME, "solution"], generated_pf)
    kernel.same_type(original[0], generated[0])
    kernel.same_type(original[1], generated[1])
    kernel.same_type(original[1], generated[2])

    refs_doc = output_json(STAGE / "proof-references.json", generated_pf)
    fail(set(refs_doc) != {"schemaVersion", "probeMainModule", "rows"}
         or refs_doc["schemaVersion"] != 1
         or refs_doc["probeMainModule"] != generated_pf["data"]["actual_module_identity"],
         "Actual proof-reference JSON schema/module owner differs")
    refs_rows = refs_doc["rows"]
    fail(not isinstance(refs_rows, list)
         or [row.get("name") for row in refs_rows] != [prep.HELPER, "solution"],
         "Actual solution/helper proof-reference rows differ from exact expected domain")
    by_name = {row["name"]: row for row in refs_rows}
    generated_by_name = {row["name"]: row for row in generated}
    for name, row in by_name.items():
        fail(set(row) != {"name", "kind", "levelParams", "closedType", "closedValue",
                          "typeRefs", "valueRefs", "axioms", "owner"}
             or row["kind"] != "theorem" or row["closedType"] is not True
             or row["closedValue"] is not True
             or row["owner"] != {"kind": "OwnModule", "module": generated_pf["data"]["actual_module_identity"]}
             or row["levelParams"] != sorted(set(row["levelParams"]))
             or not isinstance(row["axioms"], list)
             or not set(row["axioms"]) <= context.STD3
             or row["typeRefs"] != sorted(set(row["typeRefs"]))
             or row["valueRefs"] != sorted(set(row["valueRefs"]))
             or name not in generated_by_name
             or set(row["typeRefs"]) != kernel_refs(generated_by_name[name]["type"]),
             "Actual proof-reference schema or axiom set differs: " + name)
    solution_refs = set(by_name["solution"]["valueRefs"])
    fail(prep.CHILD not in solution_refs or prep.HELPER not in solution_refs
         or prep.NAME in solution_refs or "solution" in solution_refs,
         "Solution proof reference graph omits its proved child/helper or is self/target-referential")
    project_refs = {name for row in refs_rows for field in ("typeRefs", "valueRefs")
                    for name in row[field]
                    if name.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions."))}
    allowed_project_refs = set(manifest["allowed_project_proof_references"])
    fail(not project_refs <= allowed_project_refs,
         "P1 solution references project declarations outside the exact Params CI/child/helper set: "
         + str(sorted(project_refs - allowed_project_refs)))
    source_axioms = {
        prep.HELPER: standalone.audit_axioms(context.file(source_pf["data"]["log"]), prep.HELPER),
        prep.NAME: standalone.audit_axioms(context.file(source_pf["data"]["log"]), prep.NAME),
    }
    solution_axioms = standalone.audit_axioms(context.file(sol_pf["data"]["log"]), "solution")
    fail(any(not set(a) <= context.STD3 for a in source_axioms.values())
         or not set(solution_axioms) <= context.STD3,
         "Source theorem/helper or generated solution uses axioms outside Std3")

    outputs = [STAGE / "original-type.json", STAGE / "generated-type.json", STAGE / "proof-references.json"]
    report = {
        "schema_version": 1, "artifact_kind": "ap5-p1-parameters-strict-existing-certificate",
        "stage": rel(STAGE), "node": manifest["node"], "theorem_name": prep.NAME,
        "source_commit": prep.COMMIT, "stage_manifest_sha256": sha(STAGE / "manifest.json"),
        "preparation_sha256": sha(STAGE / "preparation.json"),
        "implementation_hashes": {rel(Path(prep.__file__)): sha(Path(prep.__file__)),
            rel(SELF): sha(SELF), rel(Path(context.__file__)): sha(Path(context.__file__)),
            rel(Path(kernel.__file__)): sha(Path(kernel.__file__)),
            rel(Path(standalone.__file__)): sha(Path(standalone.__file__))},
        "actual_definition_certificate": {"path": manifest["definition_dependency"]["structural_certificate"],
            "sha256": sha(V / manifest["definition_dependency"]["structural_certificate"]),
            "first_search_olean": rel(V / manifest["definition_dependency"]["first_search_olean"]),
            "first_search_olean_sha256": manifest["definition_dependency"]["first_search_olean_sha256"],
            "imported_thm_record": params_dep},
        "actual_proved_child": {"certificate": manifest["proved_child_dependency"]["actual_child_certificate"],
            "certificate_sha256": sha(V / manifest["proved_child_dependency"]["actual_child_certificate"]),
            "olean": rel(V / manifest["proved_child_dependency"]["olean"]),
            "olean_sha256": manifest["proved_child_dependency"]["olean_sha256"],
            "imported_dependency": child_dep},
        "compiled_Thm_exact_assembly": {"preamble_sha256": sha_bytes(manifest["preamble"].encode()),
            "formal_statement_sha256": sha_bytes(manifest["formal_statement"].encode()),
            "compiled_file_sha256": sha(statement_path), "byte_equal": True},
        "preflights": records,
        "type_equalities": [
            {"source": prep.HELPER, "generated": prep.HELPER, "equal": True},
            {"source": prep.NAME, "generated": prep.NAME, "equal": True},
            {"source": prep.NAME, "generated": "solution", "equal": True},
        ],
        "source_axioms": {k: sorted(v) for k, v in source_axioms.items()},
        "solution_axioms": sorted(solution_axioms), "proof_references": refs_rows,
        "project_proof_references": sorted(project_refs),
        "output_json_sha256": {rel(p): sha(p) for p in outputs},
        "max_file_seconds": max(x["data"]["seconds"] for x in records.values()),
        "validated": True, "Lean_started_by_consumer": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft",
    }
    raw = (json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    if CERT.exists() and CERT.read_bytes() != raw:
        raise ValueError("Existing p1 certificate differs; preserve it instead of overwriting")
    if not CERT.exists():
        CERT.write_bytes(raw)
    return report


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certify-existing", action="store_true", required=True)
    args = parser.parse_args()
    print(json.dumps(certify(), ensure_ascii=False, indent=2))
