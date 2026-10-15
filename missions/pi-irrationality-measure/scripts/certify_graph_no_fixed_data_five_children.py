"""Pure replay of the six-plus-seven genuine NoFixedData theorem interfaces.

This certifies only an Open graph sketch. Local child stubs carry sorryAx;
accepted platform proofs are independently pinned by their public readbacks.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path

import certify_grouped_collision_rate_node as typeaudit
import stage_graph_no_fixed_data_five_children as stage
import validate_namespace_context_providers as context
from validate_formal_log_node import checked_expr


TASK, STAGE = stage.TASK, stage.STAGE
SELF = Path(__file__).resolve()
CERT = STAGE / "five-child-interface-validation.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(doc):
    return (json.dumps(doc, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode()


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def rows(path, pf, names, owners, open_sketch):
    data = pf["data"]
    end = datetime.fromisoformat(data["at_utc"]).timestamp()
    need(path.is_file() and end - data["seconds"] - 2 <= path.stat().st_mtime <= end + 2,
         "Snapshot JSON was not written in actual bounded compiler window: " + rel(path))
    got = read(path)
    keys = {"name", "levelParams", "type", "value", "closedType", "closedValue",
            "isProp", "actualOwner", "axioms", "typeRefs", "valueRefs",
            "Open_sketch_type_check"}
    need(isinstance(got, list) and len(got) == len(names) and
         [row.get("name") for row in got] == names, "Snapshot CI name/order differs")
    for row, owner in zip(got, owners, strict=True):
        need(set(row) == keys and row["actualOwner"] == owner and
             row["value"] is None and row["closedType"] is True and
             row["closedValue"] is True and row["isProp"] is True and
             row["Open_sketch_type_check"] is open_sketch,
             "Actual theorem CI contract differs: " + row.get("name", "?"))
        levels = row["levelParams"]
        need(isinstance(levels, list) and all(isinstance(x, str) for x in levels) and
             len(levels) == len(set(levels)), "Theorem universe binders differ")
        checked_expr(row["type"], set(levels))
        for field in ("typeRefs", "valueRefs"):
            refs = row[field]
            need(isinstance(refs, list) and all(isinstance(x, str) for x in refs) and
                 refs == sorted(set(refs)), "Actual CI references are malformed")
        ax = row["axioms"]
        need(isinstance(ax, list) and ax == sorted(set(ax)) and
             set(ax) <= STD3 | ({"sorryAx"} if open_sketch else set()) and
             ("sorryAx" in ax) == open_sketch,
             "Original Std3 theorem confused with generated Open/sorryAx sketch")
    return got


def compact(pf):
    data = pf["data"]
    return {"record": pf["record"], "record_sha256": pf["record_sha256"],
            "mode": data["mode"], "actual_module_identity": data["actual_module_identity"],
            "seconds": data["seconds"], "log": data["log"],
            "log_sha256": data["log_sha256"], "output_olean": data["output_olean"],
            "output_olean_sha256": data["output_olean_sha256"],
            "dependency_oleans": [{"module": dep["module"], "path": dep["path"],
                                   "sha256_before": dep["sha256_before"]}
                                  for dep in data["dependency_oleans"]]}


def validate(write=False):
    stage.check()
    prep = read(STAGE / "preparation.json")
    need(prep["validated"] is False and prep["submission_ready"] is False and
         prep["NoFixedData"]["name"] == stage.NFD and
         prep["global_solution_own_sorry"] is False and
         prep["global_solution_dependency_sorryAx"] is True and
         len(prep["source_proof_changes"]) == 2,
         "Frozen five-child sketch preparation contract differs")
    rows_spec = [("c1.json", stage.CHILDREN[0][3].replace(".", "/") + ".lean", "emit-olean", stage.CHILDREN[0][3]),
                 ("c2.json", stage.CHILDREN[1][3].replace(".", "/") + ".lean", "emit-olean", stage.CHILDREN[1][3]),
                 ("c3.json", stage.CHILDREN[2][3].replace(".", "/") + ".lean", "emit-olean", stage.CHILDREN[2][3]),
                 ("c4.json", stage.CHILDREN[3][3].replace(".", "/") + ".lean", "emit-olean", stage.CHILDREN[3][3]),
                 ("c5.json", stage.ARITH_MODULE.replace(".", "/") + ".lean", "emit-olean", stage.ARITH_MODULE),
                 ("c6.json", stage.SOL_FILE, "emit-olean", stage.SOL_MODULE),
                 ("c7.json", "SourceSnapshot.lean", "modecheck", "SourceSnapshot"),
                 ("c8.json", "GeneratedSnapshot.lean", "modecheck", "GeneratedSnapshot")]
    preflights = {}
    for manifest, filename, mode, module in rows_spec:
        pf = context.record(STAGE / filename, STAGE / manifest, mode, module, STAGE)
        d = pf["data"]
        need(d["success"] is True and d["exit_code"] == 0 and
             d.get("original_exit_code") is None and d["timed_out"] is False and
             d["source_unchanged"] is True and d["manifest_unchanged"] is True and
             0 < d["seconds"] <= 300 and
             sha(context.file(d["log"])) == d["log_sha256"],
             "Actual bounded compiler preflight differs: " + manifest)
        preflights[manifest] = pf
    source = rows(STAGE / stage.SOURCE_JSON, preflights["c7.json"],
                  prep["source_snapshot_names"], prep["source_snapshot_owners"], False)
    generated = rows(STAGE / stage.GENERATED_JSON, preflights["c8.json"],
                     prep["generated_snapshot_names"], prep["generated_snapshot_owners"], True)
    for i in range(6):
        left, right = source[i], generated[i]
        need(len(left["levelParams"]) == len(right["levelParams"]) and
             typeaudit.normalized_expr(left, "type") == typeaudit.normalized_expr(right, "type") and
             left["typeRefs"] == right["typeRefs"],
             "Original/source017 child kernel types differ at index " + str(i))
    need(typeaudit.normalized_expr(source[0], "type") ==
         typeaudit.normalized_expr(generated[6], "type") and
         source[0]["typeRefs"] == generated[6]["typeRefs"],
         "Original NoFixedData, published comparator, and global solution types differ")
    source_direct = set(source[0]["valueRefs"])
    solution_direct = set(generated[6]["valueRefs"])
    source_five = [stage.CHILDREN[0][2], stage.CHILDREN[1][2],
                   stage.CHILDREN[2][2], stage.CHILDREN[3][2], stage.ARITH_SOURCE]
    generated_five = [stage.CHILDREN[0][1], stage.CHILDREN[1][1],
                      stage.CHILDREN[2][1], stage.CHILDREN[3][1], stage.ARITH]
    need(all(name in source_direct for name in source_five) and
         all(name in solution_direct for name in generated_five) and
         stage.NFD not in solution_direct and
         stage.CHILDREN[0][2] not in solution_direct and
         stage.ARITH_SOURCE not in solution_direct,
         "Actual source/generated proof values do not contain exact five child references")
    source_project = {name for name in source_direct if name.startswith("OAI.")}
    generated_project = {name for name in solution_direct if name.startswith("OAI.")}
    expected_project = (source_project - {source_five[0], source_five[4]}) | {
        generated_five[0], generated_five[4]}
    need(generated_project == expected_project,
         "Project proof-reference difference exceeds the two recorded source name replacements")
    public = prep["public_children_at_staging"]
    need(set(public) == {"collision", "minor", "comparison", "mean"} and
         all(public[label]["platform_proved_at_staging"] for label in ("collision", "minor", "comparison")) and
         public["mean"]["status_at_staging"] == "Open" and
         public["mean"]["platform_proved_at_staging"] is False,
         "Saved authoritative child status distinctions differ")
    current_mean = read(stage.CHILDREN[3][4])
    mean_now_proved = (current_mean.get("confirmed_proved") is True and
                       current_mean.get("target_readback", {}).get("body", {}).get("status") == "Proved" and
                       current_mean.get("last_verify_verdict", {}).get("body", {}).get("status") == "ACCEPTED" and
                       current_mean.get("theorem_id") == public["mean"]["theorem_id"])
    result = {"schema_version": 1,
              "artifact_kind": "NoFixedData-five-child-actual-type-reference-interface-validation",
              "validated_interface": True, "validated_closed_proof": False,
              "five_child_graph_sketch_only": True, "submission_ready": False,
              "proposal_status": "Draft", "source_commit": prep["source_commit"],
              "source_to_generated_seven_kernel_type_equal": True,
              "original_source_proof_only_two_name_edits": prep["source_proof_changes"],
              "NoFixedData_original_source_command_sha256": prep["NoFixedData"]["original_source_command_sha256"],
              "NoFixedData_same_v2_comparator_sha256": prep["NoFixedData"]["same_comparator_as_frozen_v2_sha256"],
              "arithmetic_source017_Open_wire_sha256": prep["original_arithmetic"]["source017_open_wire_sha256"],
              "theorem_proof_values_exported": False,
              "source_theorem_axioms": {r["name"]: r["axioms"] for r in source},
              "generated_local_sketch_axioms": {r["name"]: r["axioms"] for r in generated},
              "source_actual_owners": {r["name"]: r["actualOwner"] for r in source},
              "generated_actual_owners": {r["name"]: r["actualOwner"] for r in generated},
              "original_five_actual_direct_proof_refs": source_five,
              "generated_five_actual_direct_proof_refs": generated_five,
              "source_actual_OAI_proof_refs": sorted(source_project),
              "generated_actual_OAI_proof_refs": sorted(generated_project),
              "public_children_at_staging": public,
              "mean_actual_publication_record_current_sha256": sha(stage.CHILDREN[3][4]),
              "mean_platform_proved_now": mean_now_proved,
              "all_eight_preflights": {key: compact(preflights[key]) for key, *_ in rows_spec},
              "source_snapshot": rel(STAGE / stage.SOURCE_JSON),
              "source_snapshot_sha256": sha(STAGE / stage.SOURCE_JSON),
              "generated_snapshot": rel(STAGE / stage.GENERATED_JSON),
              "generated_snapshot_sha256": sha(STAGE / stage.GENERATED_JSON),
              "preparation_sha256": sha(STAGE / "preparation.json"),
              "implementation_sha256": {rel(SELF): sha(SELF), rel(Path(stage.__file__)): sha(Path(stage.__file__))},
              "Lean_started_by_consumer": False, "API_used": False}
    if write:
        raw = encode(result)
        if CERT.exists():
            need(CERT.read_bytes() == raw, "Saved five-child validation differs")
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
             "Actual replay differs from saved five-child certificate")
    print(json.dumps({"validated_interface": True, "validated_closed_proof": False,
                      "mean_platform_proved_now": cert["mean_platform_proved_now"],
                      "max_file_seconds": max(r["seconds"] for r in cert["all_eight_preflights"].values()),
                      "Lean_started": False, "API_used": False}, ensure_ascii=False))


if __name__ == "__main__":
    main()
