"""Strict offline certification of AP19's two-child Open analytic sketch.

The certificate proves type/interface fidelity and real bounded compilation.
It explicitly records generated sorryAx; it does not certify a closed proof.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import json
from pathlib import Path

import finalize_analytic_aggregate_two_child_reduction as stage
import validate_namespace_context_providers as context
from certify_full_row_minor_node import imported_dep, normalized_type, refs
from validate_formal_log_node import checked_expr


TASK, V, STAGE = stage.TASK, stage.V, stage.STAGE
SELF = Path(__file__).resolve()
CERT = V / "ap19/analytic-aggregate-two-child-reduction-validation-v2/open-sketch-interface-validation-v2.json"
ORIGINAL_CONSUMER = TASK / "scripts/certify_analytic_aggregate_two_child_reduction.py"
HELPER_CERT = V / "ap10/determinant/actual-provider-validation-helper-v2.json"
HELPER_CERT_SHA256 = "d17d1a485e9b7310e16741d70f6ac0cd4b5a37fbfd4c2913a1b58cfb0f98a30e"
STD3 = {"propext", "Classical.choice", "Quot.sound"}
ROW_KEYS = {"name", "levelParams", "type", "value", "closedType", "closedValue",
            "isProp", "actualOwner", "axioms", "typeRefs", "valueRefs",
            "Open_sketch_type_check"}
OWNED_KEYS = {"name", "actualOwner", "privateUserName", "kind", "levelParams",
              "type", "value", "closedType", "closedValue", "isProp",
              "typeRefs", "valueRefs", "axioms"}

need, read, sha, encode, rel = stage.need, stage.read, stage.sha, stage.encode, stage.rel


def certified_helper_pair():
    need(sha(HELPER_CERT) == HELPER_CERT_SHA256,
         "Previously certified determinant closed-Prop helper pair changed")
    cert = read(HELPER_CERT)
    pair = cert["certified_actual_helper_pair"]
    need(cert["validated"] is True and cert["Std3_only"] is True
         and cert["source_and_generated_types_equal"] is True
         and cert["definition_values_equal_after_certified_proof_CI_substitution"] is True
         and cert["normalization_domain"] == {
             "constant_pairs": 1, "parent_values": 2,
             "types_modified": False, "source_files_modified": False}
         and pair["source_name"] ==
             "OAI.PiExponent.DeterminantContradiction.collisionConstant._proof_1"
         and pair["generated_name"] ==
             "OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement._proof_1"
         and pair["actual_closed_propositional_types_equal"] is True
         and pair["actual_full_proof_values_equal"] is True,
         "Actual certified closed-Prop helper pair or normalization scope differs")
    for path, expected in {**cert["output_json_sha256"],
                           **cert["implementation_hashes"]}.items():
        need(sha(TASK / path) == expected,
             "Certified determinant helper witness changed: " + path)
    for witness in cert["preflights"].values():
        need(sha(TASK / witness["record"]) == witness["record_sha256"],
             "Certified determinant helper compiler record changed")
    return pair


def written(path, witness):
    row = witness["data"]
    finished = datetime.fromisoformat(row["at_utc"]).timestamp()
    need(path.is_file() and finished - row["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "Actual snapshot JSON was not written during its compiler invocation: " + rel(path))
    return read(path)


def check_refs(names, field):
    need(isinstance(names, list) and all(isinstance(x, str) for x in names)
         and names == sorted(set(names)), "Malformed actual " + field + " reference list")


def type_row(row, name, owner, open_sketch):
    need(isinstance(row, dict) and set(row) == ROW_KEYS
         and row["name"] == name and row["actualOwner"] == owner
         and row["closedType"] is True and row["closedValue"] is True
         and row["isProp"] is True and row["value"] is None
         and row["Open_sketch_type_check"] is open_sketch,
         "Actual theorem CI identity/owner/closure/value domain differs: " + name)
    levels = row["levelParams"]
    need(isinstance(levels, list) and all(isinstance(x, str) for x in levels)
         and len(levels) == len(set(levels)), "Invalid actual universe binders: " + name)
    checked_expr(row["type"], set(levels))
    normalized_type(row)
    check_refs(row["typeRefs"], "type")
    check_refs(row["valueRefs"], "proof")
    need(refs(row["type"]) == row["typeRefs"], "Complete theorem type refs differ: " + name)
    axioms = row["axioms"]
    check_refs(axioms, "axiom")
    if open_sketch:
        need("sorryAx" in axioms and set(axioms) <= STD3 | {"sorryAx"},
             "Open generated theorem is missing sorryAx or has another axiom: " + name)
    else:
        need(set(axioms) <= STD3 and "sorryAx" not in axioms,
             "Original source theorem is not Std3 closed: " + name)
    return row


def owned_inventory(path, witness, expected):
    doc = written(path, witness)
    need(isinstance(doc, dict) and set(doc) == {"schemaVersion", "probeMainModule",
                                                   "ownerModules", "rawOwnedCIs"}
         and doc["schemaVersion"] == 1
         and doc["probeMainModule"] == Path(stage.candidate.GENERATED_SNAPSHOT).stem
         and doc["ownerModules"] == [stage.candidate.theorem_module(n)
                                       for n, *_ in stage.candidate.CHILDREN]
                                    + [stage.candidate.SOLUTION_MODULE],
         "Generated raw-owned CI inventory envelope differs")
    rows = doc["rawOwnedCIs"]
    names = [r["name"] for r in rows]
    need(names == sorted(expected),
         "Unexpected actual generated owned CIs; full raw inventory preserved: " + repr(names))
    by_name = {r["name"]: r for r in rows}
    for name, theorem in expected.items():
        row = by_name[name]
        need(set(row) == OWNED_KEYS and row["actualOwner"] == theorem["actualOwner"]
             and row["privateUserName"] is None and row["kind"] == "theorem"
             and row["closedType"] is True and row["closedValue"] is True
             and row["isProp"] is True and row["value"] is None
             and all(row[k] == theorem[k] for k in
                     ["levelParams", "type", "typeRefs", "valueRefs", "axioms"]),
             "Raw generated owner CI is not the same complete imported theorem: " + name)
    return doc


def validate():
    stage.check_only()
    plan = read(STAGE / "preparation.json")
    need(plan["validated"] is False and plan["submission_ready"] is False
         and plan["proposal_status"] == "Draft"
         and plan["parent_existing_wire_sha256"] == sha(STAGE / "parent-existing-wire.lean")
         and plan["parent_wire_unchanged"] is True
         and plan["child_closed_proofs"] is False
         and plan["Open_child_sorryAx_expected"] is True
         and plan["closed_proof"] is False,
         "Final Open sketch preparation or original parent wire differs")
    names = [n for n, *_ in stage.candidate.CHILDREN]
    files = ([stage.candidate.theorem_module(n).replace(".", "/") + ".lean" for n in names]
             + [stage.candidate.SOLUTION_FILE,
                stage.candidate.SOURCE_SNAPSHOT, stage.candidate.GENERATED_SNAPSHOT])
    modes = ["emit-olean", "emit-olean", "emit-olean", "modecheck", "modecheck"]
    preflights = {}
    for file, mode in zip(files, modes, strict=True):
        manifest = STAGE / plan["files"][file]["manifest"]
        module = ".".join(Path(file).with_suffix("").parts)
        witness = context.record(STAGE / file, manifest, mode, module, STAGE)
        row = witness["data"]
        need(row["success"] is True and row["exit_code"] == 0
             and row["timed_out"] is False and 0 < row["seconds"] <= 300
             and row["timeout_seconds"] == 300 and row["mode"] == mode
             and "emit_olean" not in row
             and read(manifest)["mode"] == mode
             and read(manifest)["emit_olean"] is (mode == "emit-olean"),
             "Actual bounded context/mode/budget differs: " + file)
        preflights[file] = witness
    child_witnesses = [preflights[x] for x in files[:2]]
    solution_witness = preflights[files[2]]
    source_witness = preflights[files[3]]
    generated_witness = preflights[files[4]]
    oleans = {}
    for file, witness in zip(files[:3], child_witnesses + [solution_witness], strict=True):
        module = ".".join(Path(file).with_suffix("").parts)
        expected = V / "staged-build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
        actual = witness["data"]
        need(context.file(actual["output_olean"]) == expected.resolve()
             and sha(expected) == actual["output_olean_sha256"],
             "Open theorem/solution emitted OLean differs: " + module)
        oleans[module] = {"path": rel(expected), "sha256": sha(expected)}
    for witness in [source_witness, generated_witness]:
        need(witness["data"]["output_olean"] is None
             and witness["data"]["output_olean_sha256"] is None,
             "Type/ref snapshot emitted an OLean")
    for module in [stage.candidate.PROVIDER_MODULE, stage.candidate.CORE_MODULE]:
        dep = imported_dep(child_witnesses[0], module)
        need(dep["stable_during_compile"] is True,
             "Child comparator first-search Definition import was unstable")
    for module, witness in zip([stage.candidate.theorem_module(n) for n in names],
                               child_witnesses, strict=True):
        dep = imported_dep(solution_witness, module)
        need(dep["sha256_before"] == oleans[module]["sha256"],
             "Parent solution did not import exact just-emitted child OLean")
    solution_dep = imported_dep(generated_witness, stage.candidate.SOLUTION_MODULE)
    need(solution_dep["sha256_before"] == oleans[stage.candidate.SOLUTION_MODULE]["sha256"],
         "Generated snapshot did not import exact parent solution OLean")
    imported_dep(source_witness, stage.candidate.SOURCE_MODULE)
    source = written(STAGE / stage.SOURCE_JSON, source_witness)
    generated = written(STAGE / stage.GENERATED_JSON, generated_witness)
    need(isinstance(source, list) and isinstance(generated, list)
         and len(source) == len(generated) == 3,
         "Source/generated complete theorem CI domain differs")
    left, right = {}, {}
    for i, name in enumerate(names + [stage.candidate.PARENT]):
        left[name] = type_row(source[i], name, stage.candidate.SOURCE_MODULE, False)
    for i, name in enumerate(names + ["solution"]):
        owner = (stage.candidate.theorem_module(name) if name != "solution"
                 else stage.candidate.SOLUTION_MODULE)
        right[name] = type_row(generated[i], name, owner, True)
    for name in names:
        need(normalized_type(left[name]) == normalized_type(right[name]),
             "Original/Open child full kernel type differs: " + name)
    need(normalized_type(left[stage.candidate.PARENT]) == normalized_type(right["solution"]),
         "Original existing parent/global solution full kernel type differs")
    parent_left = left[stage.candidate.PARENT]
    parent_right = right["solution"]
    source_project = sorted(x for x in parent_left["valueRefs"] if x.startswith("OAI."))
    generated_project = sorted(x for x in parent_right["valueRefs"] if x.startswith("OAI."))
    pair = certified_helper_pair()
    need(len(source_project) == len(generated_project) == 25
         and sorted(set(source_project) - set(generated_project)) == [pair["source_name"]]
         and sorted(set(generated_project) - set(source_project)) == [pair["generated_name"]]
         and len(set(source_project) & set(generated_project)) == 24
         and sorted(pair["generated_name"] if x == pair["source_name"] else x
                    for x in source_project) == generated_project,
         "Project proof refs differ beyond the one actual certified closed-Prop pair: "
         + repr({"source": source_project, "generated": generated_project}))
    need(all(n in generated_project for n in names),
         "Global solution did not actually reference both Open immediate children")
    expected_owned = {name: right[name] for name in names}
    expected_owned["solution"] = right["solution"]
    owned_inventory(STAGE / stage.OWNED_JSON, generated_witness, expected_owned)
    # The actual source proof remains Std3. Imported Open child theorem values
    # make the generated sketch depend on sorryAx, which this report preserves.
    return {"schema_version": 1,
            "artifact_kind": "ap19-analyticAggregate-two-child-actual-Open-sketch-validation",
            "validated": True, "source_Std3_only": True,
            "generated_sorryAx_from_exactly_two_Open_child_interfaces": True,
            "generated_Std3_only": False, "closed_proof": False,
            "Open_sketch_only": True, "submission_ready": False,
            "proposal_status": "Draft", "parent_existing_theorem_id": stage.candidate.PARENT_ID,
            "parent_existing_wire_sha256": plan["parent_existing_wire_sha256"],
            "child_names": names, "child_comparator_status": "Open placeholders, not proofs",
            "source_names": names + [stage.candidate.PARENT],
            "generated_names": names + ["solution"],
            "source_generated_full_kernel_types_equal": True,
            "source_generated_project_proof_refs_equal": False,
            "source_generated_project_proof_refs_equal_after_one_certified_closed_Prop_pair": True,
            "certified_closed_Prop_helper_pair": {
                "source_name": pair["source_name"],
                "generated_name": pair["generated_name"],
                "actual_closed_propositional_types_equal": True,
                "actual_full_proof_values_equal": True},
            "certified_closed_Prop_helper_pair_certificate": rel(HELPER_CERT),
            "certified_closed_Prop_helper_pair_certificate_sha256": HELPER_CERT_SHA256,
            "original_frozen_consumer_preimage": rel(ORIGINAL_CONSUMER),
            "original_frozen_consumer_sha256": sha(ORIGINAL_CONSUMER),
            "source_parent_project_valueRefs": source_project,
            "generated_solution_project_valueRefs": generated_project,
            "original_parent_proof_suffix_sha256": plan["solution_original_proof_suffix_sha256"],
            "actual_owned_CI_names": sorted(expected_owned),
            "actual_owners": {"source": {name: row["actualOwner"] for name, row in left.items()},
                              "generated": {name: row["actualOwner"] for name, row in right.items()}},
            "axioms": {"source": {name: row["axioms"] for name, row in left.items()},
                       "generated": {name: row["axioms"] for name, row in right.items()}},
            "boundary": plan["boundary"],
            "preparation_sha256": sha(STAGE / "preparation.json"),
            "compiler_manifest_sha256": {f"c{i}.json": sha(STAGE / f"c{i}.json") for i in range(1, 6)},
            "preflights": preflights, "emitted_oleans": oleans,
            "output_json_sha256": {rel(STAGE / n): sha(STAGE / n)
                                   for n in [stage.SOURCE_JSON, stage.GENERATED_JSON, stage.OWNED_JSON]},
            "implementation_hashes": {rel(p): sha(p) for p in
                                     [SELF, ORIGINAL_CONSUMER, HELPER_CERT, stage.SELF, Path(stage.candidate.__file__),
                                      Path(stage.data.__file__), Path(stage.data_certifier.__file__)]},
            "max_file_seconds": max(x["data"]["seconds"] for x in preflights.values()),
            "Lean_started_by_consumer": False, "API_used": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    flags = parser.add_mutually_exclusive_group(required=True)
    flags.add_argument("--certify-existing", action="store_true")
    flags.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = validate()
    raw = encode(result)
    if CERT.exists():
        need(CERT.read_bytes() == raw, "Existing Open sketch certificate differs; refusing overwrite")
    elif args.certify_existing:
        CERT.parent.mkdir(parents=True, exist_ok=True)
        CERT.write_bytes(raw)
    else:
        need(False, "Check-only requires genuine existing five-context certificate")
    print(json.dumps({"certificate": rel(CERT), "certificate_sha256": sha(CERT),
                      "validated": True, "Open_sketch_only": True,
                      "closed_proof": False, "max_file_seconds": result["max_file_seconds"],
                      "Lean_started_by_consumer": False, "API_used": False},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
