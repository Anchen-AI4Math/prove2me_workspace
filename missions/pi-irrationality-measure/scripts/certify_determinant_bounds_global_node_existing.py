"""Strictly certify existing determinant-bounds preflight and snapshot evidence.

This consumer is offline: it reads only saved compiler sidecars, Lean-exported
JSON, source pins, and the staged OLean. It never invokes Lean or an API.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import prepare_determinant_bounds_global_node as stage

TASK, ROOT, V, STAGE = stage.TASK, stage.ROOT, stage.V, stage.STAGE
SELF = Path(__file__).resolve()
SOLUTION_MODULE = "Solutions.Sol_OAI_PiExponent_determinant_bounds_inconsistent_global"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CERT = STAGE / "node-validation.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def sidecar(source: Path):
    path = source.with_suffix(source.suffix + ".preflight.json")
    record = read(path)
    log = TASK / record["log"]
    need(log.is_file() and sha(log) == record["log_sha256"], "Compiler log hash differs: " + str(path))
    need(record.get("success") is True and record.get("exit_code") == 0
         and record.get("timed_out") is False and 0 < record.get("seconds", 0) <= 300,
         "Preflight did not succeed within 300 seconds: " + str(path))
    need(record.get("source_sha256_before") == sha(source)
         and record.get("source_sha256_after") == sha(source), "Preflight source pin differs")
    return path, record


def expr_normalize(value, old_prefix: str, new_prefix: str):
    if isinstance(value, list):
        if len(value) >= 2 and value[0] == "const" and isinstance(value[1], str) and value[1].startswith(old_prefix):
            value = list(value)
            value[1] = new_prefix + value[1][len(old_prefix):]
        return [expr_normalize(x, old_prefix, new_prefix) for x in value]
    return value


def main(certify: bool):
    stage.check_only()
    prep = read(STAGE / "manifest.json")
    original_target = STAGE / stage.SOURCE_OUTPUT
    solution = STAGE / stage.SOLUTION_OUTPUT
    source_snapshot = STAGE / stage.SOURCE_SNAPSHOT
    generated_snapshot = STAGE / stage.GENERATED_SNAPSHOT
    records = {}
    for path in [original_target, solution, source_snapshot, generated_snapshot]:
        sidecar_path, rec = sidecar(path)
        records[path.name] = {"sidecar": stage.rel(sidecar_path), "sidecar_sha256": sha(sidecar_path),
                              "seconds": rec["seconds"], "output_olean": rec.get("output_olean"),
                              "output_olean_sha256": rec.get("output_olean_sha256")}
    target_row = read(STAGE / "source-type.json")
    generated_row = read(STAGE / "generated-type.json")
    need(isinstance(target_row, list) and len(target_row) == 1
         and target_row[0]["name"] == stage.NAME, "Source snapshot theorem row differs")
    need(isinstance(generated_row, list) and len(generated_row) == 1
         and generated_row[0]["name"] == "solution", "Generated snapshot solution row differs")
    need(target_row[0]["type"] == generated_row[0]["type"], "Source theorem type differs from solution type")

    source_evidence = read(STAGE / "source-proof-references.json")["theorem"]
    generated_evidence = read(STAGE / "generated-proof-references.json")["theorem"]
    need(source_evidence["name"] == stage.NAME and generated_evidence["name"] == "solution",
         "Proof-reference theorem identities differ")
    for evidence in [source_evidence, generated_evidence]:
        need(evidence["closedType"] is True and evidence["closedValue"] is True,
             "Theorem CI is not closed")
        need(set(evidence["axioms"]) <= ALLOWED_AXIOMS, "Theorem proof is not Std3")
    need(source_evidence["owner"] == {"kind": "ImportedModule", "module": stage.MODULE,
                                       "moduleIndex": source_evidence["owner"].get("moduleIndex")},
         "Source theorem owner is not the actual Comparison source module")
    need(generated_evidence["owner"] == {"kind": "OwnModule", "module": SOLUTION_MODULE,
                                          "moduleIndex": None},
         "Solution theorem is not owned by its compiled solution module")

    source_refs = source_evidence["valueRefs"]
    generated_refs = generated_evidence["valueRefs"]
    need(expr_normalize(source_evidence["value"], stage.NAME + "._proof_", "solution._proof_")
         == generated_evidence["value"], "Generated proof value differs from exact source proof after declaration-name normalization")
    normalized_refs = sorted("solution._proof_" + x[len(stage.NAME + "._proof_"):]
                             if x.startswith(stage.NAME + "._proof_") else x for x in source_refs)
    need(normalized_refs == sorted(generated_refs), "Source and generated proof value reference sets differ")
    source_helpers = source_evidence["automaticInlineHelpers"]
    generated_helpers = generated_evidence["automaticInlineHelpers"]
    need(len(source_helpers) == len(generated_helpers), "Inline helper count differs")
    for srow, grow in zip(source_helpers, generated_helpers):
        expected_generated = "solution" + srow["name"][len(stage.NAME):]
        need(grow["name"] == expected_generated, "Generated helper is not the exact renamed source helper")
        need(srow["type"] == grow["type"] and
             expr_normalize(srow["value"], srow["name"], grow["name"]) == grow["value"],
             "Paired inline helper CI differs")
        need(srow["closedType"] and srow["closedValue"] and grow["closedType"] and grow["closedValue"],
             "Inline helper CI is not closed")
        need(set(srow["axioms"]) <= ALLOWED_AXIOMS and set(grow["axioms"]) <= ALLOWED_AXIOMS,
             "Inline helper proof is not Std3")
        need(srow["owner"] == source_evidence["owner"] and grow["owner"] == generated_evidence["owner"],
             "Inline helper owner differs from its theorem owner")

    solution_record = records[solution.name]
    need(solution_record["output_olean"] is not None and solution_record["output_olean_sha256"],
         "Solution compiler did not emit an OLean")
    olean = TASK / solution_record["output_olean"]
    need(olean.is_file() and sha(olean) == solution_record["output_olean_sha256"], "Solution OLean hash differs")
    need(records[original_target.name]["output_olean"] is None,
         "Target comparator unexpectedly emitted an OLean")
    need(prep["compiled_statement_equals_preamble_plus_formal_statement"] is True
         and (STAGE / "wire-theorem-source.lean").read_bytes() ==
         (prep["preamble"] + prep["formal_statement"]).encode("utf-8")
         and original_target.read_bytes() == (prep["preamble"] + prep["formal_statement"]).encode("utf-8"),
         "Exact target assembly differs from preamble + formal statement")
    result = {
        "schema_version": 1,
        "artifact_kind": "ap7-actual-source-determinant-bounds-node-validation",
        "validated": True,
        "source_name": stage.NAME,
        "solution_name": "solution",
        "source_commit": stage.SOURCE_COMMIT,
        "source_url": stage.SOURCE_URL,
        "source_sha256": prep["source_sha256"],
        "source_unit_sha256": prep["source_unit_sha256"],
        "source_type_equals_solution_type": True,
        "solution_proof_values_equal_after_name_normalization": True,
        "inline_helpers": [x["name"] for x in source_helpers],
        "proof_axioms": sorted(set(generated_evidence["axioms"])),
        "solution_module": SOLUTION_MODULE,
        "solution_olean": solution_record["output_olean"],
        "solution_olean_sha256": solution_record["output_olean_sha256"],
        "preflights": records,
        "submission_ready": False,
        "proposal_status": "Draft",
    }
    if certify:
        if CERT.exists():
            need(read(CERT) == result, "Existing node validation differs; refusing overwrite")
        else:
            CERT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--certify-existing", action="store_true")
    group.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(main(args.certify_existing), indent=2))
