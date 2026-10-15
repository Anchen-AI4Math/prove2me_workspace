"""Pure strict replay of the five actual conditional/Open chain preflights.

An Open sketch certificate is an interface/reference certificate, never a
closed proof or platform submission certificate. No Lean/API is started.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path

import certify_grouped_collision_rate_node as typeaudit
import stage_graph_conditional_open_chain as stage
import validate_namespace_context_providers as context
from validate_formal_log_node import checked_expr


TASK, STAGE = stage.TASK, stage.STAGE
SELF = Path(__file__).resolve()
CERT = STAGE / "open-chain-interface-validation.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}
FILES = [("c1.json", stage.NFD_FILE, "emit-olean", stage.NFD_MODULE),
         ("c2.json", stage.A1_FILE, "emit-olean", stage.A1_MODULE),
         ("c3.json", stage.SOLUTION_FILE, "emit-olean", stage.SOLUTION_MODULE),
         ("c4.json", stage.SOURCE_SNAPSHOT, "modecheck", "SourceSnapshot"),
         ("c5.json", stage.GENERATED_SNAPSHOT, "modecheck", "GeneratedSnapshot")]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode()


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def compact(pf):
    data = pf["data"]
    return {"record": pf["record"], "record_sha256": pf["record_sha256"],
            "mode": data["mode"], "module": data["actual_module_identity"],
            "seconds": data["seconds"], "success": data["success"],
            "log": data["log"], "log_sha256": data["log_sha256"],
            "output_olean": data["output_olean"],
            "output_olean_sha256": data["output_olean_sha256"],
            "dependency_oleans": [
                {"module": d["module"], "path": d["path"], "sha256": d["sha256_before"]}
                for d in data["dependency_oleans"]]}


def snapshot_rows(path, pf, expected_names, expected_owners, open_sketch):
    data = pf["data"]
    finished = datetime.fromisoformat(data["at_utc"]).timestamp()
    need(path.is_file() and finished - data["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "Type/ref output was not written in the actual compiler window: " + rel(path))
    rows = read(path)
    need(isinstance(rows, list) and len(rows) == len(expected_names)
         and [row.get("name") for row in rows] == expected_names,
         "Snapshot actual theorem CI domain/order differs: " + rel(path))
    expected_keys = {"name", "levelParams", "type", "value", "closedType", "closedValue",
                     "isProp", "actualOwner", "axioms", "typeRefs", "valueRefs",
                     "Open_sketch_type_check"}
    for row, owner in zip(rows, expected_owners, strict=True):
        need(set(row) == expected_keys and row["actualOwner"] == owner
             and row["value"] is None and row["closedType"] is True
             and row["closedValue"] is True and row["isProp"] is True
             and row["Open_sketch_type_check"] is open_sketch,
             "Theorem CI owner/closedness/type-only metadata differs: " + row.get("name", "?"))
        levels = row["levelParams"]
        need(isinstance(levels, list) and all(isinstance(x, str) for x in levels)
             and len(levels) == len(set(levels)), "Malformed theorem universe binders")
        checked_expr(row["type"], set(levels))
        for refs in (row["typeRefs"], row["valueRefs"]):
            need(isinstance(refs, list) and all(isinstance(x, str) for x in refs)
                 and refs == sorted(set(refs)), "Actual CI references are not a finite sorted set")
        axioms = row["axioms"]
        need(isinstance(axioms, list) and axioms == sorted(set(axioms))
             and set(axioms) <= (STD3 | ({"sorryAx"} if open_sketch else set()))
             and (("sorryAx" in axioms) == open_sketch),
             "Open sketch/sorryAx was confused with a closed Std3 proof")
    return rows


def validate(write=False):
    stage.check()
    prep = read(STAGE / stage.PREP)
    need(prep["validated"] is False and prep["submission_ready"] is False
         and prep["A1_reference"]["actual_platform_status"] == "ACCEPTED_AND_PROVED"
         and prep["A1_reference"]["local_stub_only_for_type_and_reference_resolution"] is True
         and prep["NoFixedData"]["name"] == stage.previous.NO_FIXED,
         "Pure Open-chain preparation state differs")
    pfs = {}
    for manifest, filename, mode, module in FILES:
        pf = context.record(STAGE / filename, STAGE / manifest, mode, module, STAGE)
        d = pf["data"]
        need(d["success"] is True and d["exit_code"] == 0
             and d.get("original_exit_code") is None and d["timed_out"] is False
             and d["source_unchanged"] is True and d["manifest_unchanged"] is True
             and 0 < d["seconds"] <= 300
             and sha(context.file(d["log"])) == d["log_sha256"],
             "Actual bounded source/Open-chain preflight failed: " + filename)
        pfs[manifest] = pf
    source_names = prep["source_snapshot_names"]
    generated_names = prep["generated_snapshot_names"]
    source_owners = ["OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters",
                     "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction",
                     "OAI.NumberTheory.PiExponent.Approximation.DeterminantContradiction"]
    generated_owners = [stage.A1_MODULE, stage.NFD_MODULE,
                        stage.CONDITIONAL_MODULE, stage.SOLUTION_MODULE]
    source = snapshot_rows(STAGE / stage.SOURCE_JSON, pfs["c4.json"],
                           source_names, source_owners, False)
    generated = snapshot_rows(STAGE / stage.GENERATED_JSON, pfs["c5.json"],
                              generated_names, generated_owners, True)
    for left, right in ((source[0], generated[0]), (source[1], generated[1]),
                        (source[2], generated[2]), (source[2], generated[3])):
        need(len(left["levelParams"]) == len(right["levelParams"])
             and typeaudit.normalized_expr(left, "type") == typeaudit.normalized_expr(right, "type")
             and left["typeRefs"] == right["typeRefs"],
             "Original source / Open target / global solution kernel types differ")
    src_refs = set(source[2]["valueRefs"])
    sol_refs = set(generated[3]["valueRefs"])
    need("OAI.PiExponent.exists_admissible_parameters" in src_refs
         and stage.previous.NO_FIXED in src_refs
         and stage.previous.A1 in sol_refs and stage.previous.NO_FIXED in sol_refs
         and "OAI.PiExponent.exists_admissible_parameters" not in sol_refs
         and stage.previous.TARGET not in sol_refs,
         "Conditional solution does not actually reference the public A1 and genuine NoFixedData parent")
    src_project = {x for x in src_refs if x.startswith("OAI.")}
    sol_project = {x for x in sol_refs if x.startswith("OAI.")}
    replaced = (src_project - {"OAI.PiExponent.exists_admissible_parameters"}) | {stage.previous.A1}
    need(replaced == sol_project,
         "Conditional project proof references changed beyond the one accepted A1 name")
    # The source theorem is closed, while every generated local theorem is an
    # explicit Open/type sketch. This certificate can authorize NoFixedData's
    # type-preserving Open publication; it cannot claim any new proved child.
    result = {
        "schema_version": 1,
        "artifact_kind": "graph-conditional-open-NoFixedData-type-and-reference-validation",
        "validated_interface": True, "validated_closed_proof": False,
        "NoFixedData_open_publication_type_ready": True,
        "conditional_sketch_only": True, "submission_ready": False,
        "proposal_status": "Draft",
        "source_commit": prep["source_commit"],
        "NoFixedData_name": stage.previous.NO_FIXED,
        "NoFixedData_source_command_sha256": prep["NoFixedData"]["source_command_sha256"],
        "NoFixedData_exact_wire_sha256": prep["NoFixedData"]["complete_compiled_wire_sha256"],
        "A1_platform_accepted_and_proved": True,
        "A1_local_reference_stub_carries_sorryAx": True,
        "conditional_published_Open_theorem_id": prep["conditional"]["platform_theorem_id"],
        "source_to_generated_type_equal": True,
        "theorem_proof_values_exported": False,
        "source_axioms": {row["name"]: row["axioms"] for row in source},
        "generated_local_sketch_axioms": {row["name"]: row["axioms"] for row in generated},
        "source_actual_owners": {row["name"]: row["actualOwner"] for row in source},
        "generated_actual_owners": {row["name"]: row["actualOwner"] for row in generated},
        "conditional_actual_source_project_valueRefs": sorted(src_project),
        "conditional_actual_solution_project_valueRefs": sorted(sol_project),
        "conditional_exact_A1_reference_replacement": [
            "OAI.PiExponent.exists_admissible_parameters", stage.previous.A1],
        "all_five_preflights": {name: compact(pfs[name]) for name, *_ in FILES},
        "source_snapshot": rel(STAGE / stage.SOURCE_JSON),
        "source_snapshot_sha256": sha(STAGE / stage.SOURCE_JSON),
        "generated_snapshot": rel(STAGE / stage.GENERATED_JSON),
        "generated_snapshot_sha256": sha(STAGE / stage.GENERATED_JSON),
        "stage_preparation_sha256": sha(STAGE / stage.PREP),
        "NoFixedData_exact_name_lookup_sha256": sha(stage.NO_FIXED_GET),
        "A1_actual_publication_sha256": sha(stage.previous.A1_RECORD),
        "conditional_actual_public_readback_sha256": sha(stage.CONDITIONAL_READBACK),
        "implementation_sha256": {rel(SELF): sha(SELF),
                                  rel(Path(stage.__file__)): sha(Path(stage.__file__)),
                                  rel(Path(context.__file__)): sha(Path(context.__file__))},
        "Lean_started_by_consumer": False, "API_used": False,
    }
    if write:
        raw = encode(result)
        if CERT.exists():
            need(CERT.read_bytes() == raw, "Frozen Open-chain interface certificate differs")
        else:
            CERT.write_bytes(raw)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--certify-existing", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    cert = validate(write=args.certify_existing)
    if args.check_only:
        need(CERT.is_file() and CERT.read_bytes() == encode(cert),
             "Saved Open-chain certificate differs from read-only actual replay")
    print(json.dumps({"validated_interface": True, "validated_closed_proof": False,
                      "NoFixedData_open_type_ready": True,
                      "max_file_seconds": max(row["seconds"] for row in cert["all_five_preflights"].values()),
                      "Lean_started": False, "API_used": False}, ensure_ascii=False))


if __name__ == "__main__":
    main()
