"""Pure strict replay of the three successor checks and five reused emitters.

Five copied source helper theorems must be closed Std3 CIs. The NoFixedData
solution remains an Open graph sketch because its arithmetic child is Open.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_graph_no_fixed_data_five_children as original_consumer
import certify_grouped_collision_rate_node as typeaudit
import stage_graph_no_fixed_data_five_children_v2 as stage
import validate_namespace_context_providers as context


TASK, STAGE = stage.TASK, stage.STAGE
SELF = Path(__file__).resolve()
CERT = STAGE / "five-child-source-helper-interface-validation.json"
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


def compact(pf):
    d = pf["data"]
    return {"record": pf["record"], "record_sha256": pf["record_sha256"],
            "mode": d["mode"], "actual_module_identity": d["actual_module_identity"],
            "seconds": d["seconds"], "log": d["log"], "log_sha256": d["log_sha256"],
            "output_olean": d["output_olean"], "output_olean_sha256": d["output_olean_sha256"],
            "dependency_oleans": [{"module": x["module"], "path": x["path"],
                                   "sha256_before": x["sha256_before"]}
                                  for x in d["dependency_oleans"]]}


def preflight(file, manifest, mode, module, root):
    pf = context.record(root / file, root / manifest, mode, module, root)
    d = pf["data"]
    need(d["success"] is True and d["exit_code"] == 0 and
         d.get("original_exit_code") is None and d["timed_out"] is False and
         d["source_unchanged"] is True and d["manifest_unchanged"] is True and
         0 < d["seconds"] <= 300 and
         sha(context.file(d["log"])) == d["log_sha256"],
         "Actual bounded compiler context differs: " + str(root / file))
    return pf


def type_equal(left, right):
    return (len(left["levelParams"]) == len(right["levelParams"]) and
            typeaudit.normalized_expr(left, "type") == typeaudit.normalized_expr(right, "type") and
            left["typeRefs"] == right["typeRefs"])


def validate(write=False):
    stage.check()
    prep = read(STAGE / "preparation.json")
    need(prep["validated"] is False and prep["submission_ready"] is False and
         prep["original_41_line_NoFixedData_proof_only_two_name_replacements"] is True and
         len(prep["five_original_helper_commands"]) == 5 and
         len(prep["five_reused_actual_Open_child_emitters"]) == 5,
         "Frozen successor source-helper preparation differs")
    old_pfs = {}
    for i, item in enumerate(prep["five_reused_actual_Open_child_emitters"], 1):
        module = item["module"]
        file = module.replace(".", "/") + ".lean"
        pf = preflight(file, f"c{i}.json", "emit-olean", module, stage.old.STAGE)
        d = pf["data"]
        need(item["source_sha256"] == sha(TASK / item["source"]) and
             item["manifest_sha256"] == sha(TASK / item["manifest"]) and
             item["sidecar_sha256"] == sha(TASK / item["sidecar"]) and
             item["output_olean_sha256"] == d["output_olean_sha256"] ==
                 sha(TASK / item["output_olean"]),
             "Reused child is not the exact five proved compiler emitter preimage")
        old_pfs[f"old-c{i}"] = pf
    new_specs = [("c1.json", stage.SOL_FILE, "emit-olean", stage.SOL_MODULE),
                 ("c2.json", stage.SOURCE_FILE, "modecheck", "SourceSnapshot"),
                 ("c3.json", stage.GENERATED_FILE, "modecheck", "GeneratedSnapshot")]
    new_pfs = {manifest: preflight(file, manifest, mode, module, STAGE)
               for manifest, file, mode, module in new_specs}
    source = original_consumer.rows(STAGE / stage.SOURCE_JSON, new_pfs["c2.json"],
                                    prep["source_snapshot_names"], prep["source_snapshot_owners"], False)
    generated_helpers = original_consumer.rows(
        STAGE / stage.GENERATED_HELPERS_JSON, new_pfs["c3.json"],
        prep["generated_helper_names"], prep["generated_helper_owners"], False)
    generated_open = original_consumer.rows(
        STAGE / stage.GENERATED_SEVEN_JSON, new_pfs["c3.json"],
        prep["generated_open_names"], prep["generated_open_owners"], True)
    need(len(source) == 11 and len(generated_helpers) == 5 and len(generated_open) == 7,
         "Actual source/helper/Open theorem CI domains differ")
    for i in range(5):
        need(type_equal(source[i], generated_helpers[i]),
             "Original source/generated helper kernel type differs: " + source[i]["name"])
        src_project = {x for x in source[i]["valueRefs"] if x.startswith("OAI.")}
        gen_project = {x for x in generated_helpers[i]["valueRefs"] if x.startswith("OAI.")}
        need(src_project == gen_project,
             "Original copied helper actual project proof references differ: " + source[i]["name"])
    helper_set = set(prep["source_helper_names"])
    expected_helper_edges = [set(), set(), set(),
                             {stage.SOURCE_NAMES[0], stage.SOURCE_NAMES[2]},
                             {stage.SOURCE_NAMES[1], stage.SOURCE_NAMES[2]}]
    actual_helper_edges = []
    for row, expected in zip(generated_helpers, expected_helper_edges, strict=True):
        refs = set(row["valueRefs"]) & helper_set
        need(refs == expected,
             "Actual copied source-helper graph contains missing/new theorem dependencies: " + row["name"])
        actual_helper_edges.append({"name": row["name"], "actual_helper_valueRefs": sorted(refs)})
    for i in range(6):
        need(type_equal(source[5 + i], generated_open[i]),
             "Original source/generated Open child kernel type differs at index " + str(i))
    need(type_equal(source[5], generated_open[6]),
         "Original NoFixedData/source comparator/global solution full kernel type differs")
    source_nfd_refs = set(source[5]["valueRefs"])
    solution_refs = set(generated_open[6]["valueRefs"])
    source_five = [stage.old.CHILDREN[0][2], stage.old.CHILDREN[1][2],
                   stage.old.CHILDREN[2][2], stage.old.CHILDREN[3][2], stage.old.ARITH_SOURCE]
    generated_five = [stage.old.CHILDREN[0][1], stage.old.CHILDREN[1][1],
                      stage.old.CHILDREN[2][1], stage.old.CHILDREN[3][1], stage.old.ARITH]
    need(all(x in source_nfd_refs for x in source_five) and
         all(x in solution_refs for x in generated_five) and
         all(x in source_nfd_refs and x in solution_refs for x in
             (stage.SOURCE_NAMES[3], stage.SOURCE_NAMES[4])) and
         source_five[0] not in solution_refs and source_five[4] not in solution_refs and
         stage.old.NFD not in solution_refs,
         "Actual NoFixedData proof value does not use the exact five child references")
    source_project = {x for x in source_nfd_refs if x.startswith("OAI.")}
    solution_project = {x for x in solution_refs if x.startswith("OAI.")}
    expected_project = (source_project - {source_five[0], source_five[4]}) | {
        generated_five[0], generated_five[4]}
    need(solution_project == expected_project,
         "Global solution project proof references changed beyond the two source017 names")
    for item in prep["five_original_helper_commands"]:
        filename = item["name"].rsplit(".", 1)[1] + ".lean.txt"
        command = STAGE / "original-helper-commands" / filename
        need(sha(command) == item["original_command_sha256"] and
             hashlib.sha256(command.read_bytes().partition(b":= by")[2]).hexdigest() ==
                 item["original_proof_sha256"],
             "Original source helper AST/proof byte hash differs")
    result = {"schema_version": 1,
              "artifact_kind": "NoFixedData-five-child-five-original-helper-interface-validation",
              "validated_interface": True, "validated_closed_proof": False,
              "five_child_graph_sketch_only": True, "submission_ready": False,
              "proposal_status": "Draft", "source_commit": prep["source_commit"],
              "five_original_helpers_closed_Std3": True,
              "source_to_generated_twelve_kernel_types_equal": True,
              "NoFixedData_original_proof_only_two_name_replacements": True,
              "original_NoFixedData_comparator_sha256": prep["original_NoFixedData_comparator_sha256"],
              "original_arithmetic_Open_wire_sha256": prep["original_arithmetic_Open_wire_sha256"],
              "theorem_proof_values_exported": False,
              "source_theorem_axioms": {r["name"]: r["axioms"] for r in source},
              "generated_helper_axioms": {r["name"]: r["axioms"] for r in generated_helpers},
              "generated_Open_axioms": {r["name"]: r["axioms"] for r in generated_open},
              "source_actual_owners": {r["name"]: r["actualOwner"] for r in source},
              "generated_helper_actual_owners": {r["name"]: r["actualOwner"] for r in generated_helpers},
              "generated_Open_actual_owners": {r["name"]: r["actualOwner"] for r in generated_open},
              "source_actual_OAI_proof_refs": sorted(source_project),
              "solution_actual_OAI_proof_refs": sorted(solution_project),
              "five_actual_helper_edges": actual_helper_edges,
              "source_five_actual_child_refs": source_five,
              "generated_five_actual_child_refs": generated_five,
              "five_reused_child_preflights": {key: compact(pf) for key, pf in old_pfs.items()},
              "three_new_preflights": {key: compact(pf) for key, pf in new_pfs.items()},
              "source_snapshot_sha256": sha(STAGE / stage.SOURCE_JSON),
              "generated_helpers_snapshot_sha256": sha(STAGE / stage.GENERATED_HELPERS_JSON),
              "generated_Open_snapshot_sha256": sha(STAGE / stage.GENERATED_SEVEN_JSON),
              "stage_preparation_sha256": sha(STAGE / "preparation.json"),
              "failed_v1_sidecar_sha256": prep["old_failed_solution_preimage"]["sidecar_sha256"],
              "failed_v1_log_sha256": prep["old_failed_solution_preimage"]["log_sha256"],
              "implementation_sha256": {rel(SELF): sha(SELF),
                                        rel(Path(stage.__file__)): sha(Path(stage.__file__))},
              "Lean_started_by_consumer": False, "API_used": False}
    if write:
        raw = encode(result)
        if CERT.exists():
            need(CERT.read_bytes() == raw, "Frozen successor interface certificate differs")
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
             "Saved successor certificate differs from actual pure replay")
    print(json.dumps({"validated_interface": True, "validated_closed_proof": False,
                      "five_original_helpers_closed_Std3": True,
                      "max_new_file_seconds": max(x["seconds"] for x in cert["three_new_preflights"].values()),
                      "Lean_started": False, "API_used": False}, ensure_ascii=False))


if __name__ == "__main__":
    main()
