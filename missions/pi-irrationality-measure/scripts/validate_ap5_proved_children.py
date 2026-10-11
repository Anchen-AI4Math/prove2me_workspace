"""Validate actual imported ap5 proved-child OLeans without running Lean/API."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_ap5_proved_children as stage
import stage_parameter_proved_children as producer
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

V = stage.V
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def type_row(row, name):
    require(isinstance(row, dict) and set(row) == {"levelParams", "name", "prettyType", "type", "value"},
            "Bad type-only theorem row")
    require(row["name"] == name and row["value"] is None, "Unexpected type-only identity/value")
    return row


def type_normalized(row):
    level_map = {x: "u" + str(i) for i, x in enumerate(row["levelParams"])}
    def walk(x):
        if isinstance(x, list):
            if len(x) == 2 and x[0] == "param" and x[1] in level_map:
                return ["param", level_map[x[1]]]
            return [walk(y) for y in x]
        return x
    return (len(row["levelParams"]), walk(row["type"]))


def kernel_refs(expr):
    found = set()
    def walk(node):
        if not isinstance(node, list):
            return
        if len(node) == 3 and node[0] == "const" and isinstance(node[1], str):
            found.add(node[1])
        elif len(node) >= 3 and node[0] == "projection" and isinstance(node[1], str):
            found.add(node[1])
        for child in node[1:]:
            walk(child)
    walk(expr)
    return sorted(found)


def single_ref(path: Path, name: str, owner: str, module: str, *, exact_std3: bool):
    doc = stage.read(path)
    require(set(doc) == {"schemaVersion", "probeMainModule", "rows"} and doc["schemaVersion"] == 1
            and doc["probeMainModule"] == module and len(doc["rows"]) == 1,
            "Bad actual proof-reference probe schema: " + str(path))
    row = doc["rows"][0]
    require(set(row) == {"name", "kind", "levelParams", "closedType", "closedValue",
                         "typeRefs", "valueRefs", "axioms", "owner"}, "Bad actual CI row")
    require(row["name"] == name and row["kind"] == "theorem"
            and row["closedType"] is True and row["closedValue"] is True
            and set(row["axioms"]).issubset(STD3)
            and (not exact_std3 or set(row["axioms"]) == STD3),
            "Actual CI identity, closure or Std3 mismatch")
    own = row["owner"]
    require(set(own) == {"kind", "module", "index"} and own["kind"] == "ImportedModule"
            and own["module"] == owner and type(own["index"]) is int and own["index"] >= 0,
            "Actual imported module owner mismatch")
    for key in ("levelParams", "typeRefs", "valueRefs", "axioms"):
        values = row[key]
        require(isinstance(values, list) and all(isinstance(x, str) for x in values)
                and len(values) == len(set(values)), "Malformed actual CI list: " + key)
    require(row["typeRefs"] == sorted(row["typeRefs"]) and row["valueRefs"] == sorted(row["valueRefs"]),
            "Unsorted actual references")
    require(name not in row["typeRefs"] and name not in row["valueRefs"]
            and "solution" not in row["valueRefs"], "Self/solution proof reference")
    return row


def validate(which: str):
    c = stage.configure(which)
    producer.check_only(c)
    stage.verify_seal(c)
    stage.verify_child_seal(c)
    m, pv, publication, accepted_row = stage.accepted_pins(c)
    parent = c["parent"]
    child_source_pf = context.record(c["source"], c["source_manifest"], "emit-olean", c["module"], V/"ap5"/which)
    source_pf = context.record(c["source_snapshot"], c["source_snapshot_manifest"], "modecheck", "SourceSnapshot", V/"ap5"/which)
    child_pf = context.record(c["snapshot"], c["snapshot_manifest"], "modecheck", "ChildSnapshot", V/"ap5"/which)
    for path, pf in ((c["source_type"], source_pf), (c["source_refs"], source_pf),
                     (c["child_type"], child_pf), (c["child_refs"], child_pf)):
        producer.written_during(path, pf["data"])
    original, generated = (stage.read(parent / f) for f in ("original-type.json", "generated-type.json"))
    source, child = stage.read(c["source_type"]), stage.read(c["child_type"])
    require(len(original) == 1 and len(generated) == 2 and len(source) == len(child) == (4 if which == "c2" else 1),
            "Type-only theorem/catalog domains differ")
    generated_map = {row["name"]: row for row in generated}
    source_map = {row["name"]: row for row in source}
    child_map = {row["name"]: row for row in child}
    names = [c["theorem"]] + (list(stage.HELPERS) if which == "c2" else [])
    require(set(source_map) == set(child_map) == set(names), "Fresh source/child named domains differ")
    main_rows = [type_row(original[0], c["theorem"]),
                 type_row(generated_map[c["theorem"]], c["theorem"]),
                 type_row(generated_map["solution"], "solution"),
                 type_row(source_map[c["theorem"]], c["theorem"]),
                 type_row(child_map[c["theorem"]], c["theorem"])]
    require(len({json.dumps(type_normalized(x), sort_keys=True) for x in main_rows}) == 1,
            "Imported theorem type differs from source, target or certified solution")
    source_module = m["source_components"][0]["source_module"]
    source_ref = single_ref(c["source_refs"], c["theorem"], source_module, "SourceSnapshot", exact_std3=True)
    child_ref = single_ref(c["child_refs"], c["theorem"], c["module"], "ChildSnapshot", exact_std3=True)
    for row, ref in ((main_rows[3], source_ref), (main_rows[4], child_ref)):
        require(row["levelParams"] == ref["levelParams"]
                and kernel_refs(row["type"]) == ref["typeRefs"],
                "Actual theorem typeRefs/universe parameters differ from type-only kernel Expr")
    parent_ref_doc = stage.read(parent / "proof-references.json")
    parent_ref_map = {r["name"]: r for r in parent_ref_doc["rows"]}
    require(main_rows[2]["levelParams"] == parent_ref_map["solution"]["levelParams"]
            and kernel_refs(main_rows[2]["type"]) == parent_ref_map["solution"]["typeRefs"],
            "Certified parent solution typeRefs/universes differ from kernel type")
    parent_proof_refs = [x.replace("solution._proof_", c["theorem"] + "._proof_", 1)
                         if x.startswith("solution._proof_") else x
                         for x in parent_ref_map["solution"]["valueRefs"]]
    require(set(child_ref["valueRefs"]) == set(parent_proof_refs),
            "Child proof references differ from certified solution")
    helper_rows = []
    if which == "c2":
        definition = stage.read(parent / "definition-input.json")
        require(definition["validated"] is True and stage.sha(stage.TASK / definition["certificate"]) == definition["certificate_sha256"]
                and stage.sha(stage.TASK / definition["output_olean"]) == definition["output_olean_sha256"],
                "Certified normalizedLogWeights provider input changed")
        for catalog_name, expected_module, snap in (
            ("source-helper-catalog.json", source_module, c["source_snapshot"]),
            ("child-helper-catalog.json", c["module"], c["snapshot"])):
            catalog = stage.read(V / "ap5" / which / catalog_name)
            require(catalog["provided_names"] == list(stage.HELPERS)
                    and catalog["module"] == expected_module
                    and catalog["snapshot_sha256"] == stage.sha(snap)
                    and catalog["source_validation_sha256"] == stage.sha(c["parent_validation"])
                    and catalog["normalizedLogWeights_definition_input_sha256"] == stage.sha(parent / "definition-input.json"),
                    "Helper provided-name catalog changed")
        original_helpers = {r["name"]: r for r in stage.read(parent / "original-public-inline-types.json")}
        generated_helpers = {r["name"]: r for r in stage.read(parent / "generated-public-inline-types.json")}
        require(set(original_helpers) == set(generated_helpers) == set(stage.HELPERS), "Parent helper catalog differs")
        for i, name in enumerate(stage.HELPERS, 1):
            rows = [type_row(original_helpers[name], name), type_row(generated_helpers[name], name),
                    type_row(source_map[name], name), type_row(child_map[name], name)]
            require(len({json.dumps(type_normalized(x), sort_keys=True) for x in rows}) == 1,
                    "Genuine source/helper kernel type mismatch: " + name)
            sr = c["source"].parents[1] / ("source-helper-references-" + str(i) + ".json")
            cr = c["source"].parents[1] / ("child-helper-references-" + str(i) + ".json")
            producer.written_during(sr, source_pf["data"])
            producer.written_during(cr, child_pf["data"])
            srow = single_ref(sr, name, source_module, "SourceSnapshot", exact_std3=False)
            crow = single_ref(cr, name, c["module"], "ChildSnapshot", exact_std3=False)
            require(rows[2]["levelParams"] == srow["levelParams"]
                    and rows[3]["levelParams"] == crow["levelParams"]
                    and kernel_refs(rows[2]["type"]) == srow["typeRefs"]
                    and kernel_refs(rows[3]["type"]) == crow["typeRefs"],
                    "Helper typeRefs/universe parameters differ from type-only kernel Expr")
            require(set(crow["valueRefs"]) == set(parent_ref_map[name]["valueRefs"]),
                    "Child helper proof references differ from certified helper: " + name)
            helper_rows.append({"name": name, "source_owner": srow["owner"], "child_owner": crow["owner"],
                                "source_ref_sha256": stage.sha(sr), "child_ref_sha256": stage.sha(cr)})
    logs = (child_source_pf["data"]["log"], source_pf["data"]["log"], child_pf["data"]["log"])
    for log in logs:
        require(set(standalone.audit_axioms(context.file(log), c["theorem"])) == STD3,
                "Compiler axiom audit differs from Std3")
    for name in stage.HELPERS if which == "c2" else ():
        for log in (source_pf["data"]["log"], child_pf["data"]["log"]):
            require(set(standalone.audit_axioms(context.file(log), name)).issubset(STD3),
                    "Inline helper axiom audit differs from Std3: " + name)
    maximum = max(pv["max_file_seconds"], *(pf["data"]["seconds"] for pf in (child_source_pf, source_pf, child_pf)))
    require(maximum <= 300, "A node file exceeded the 300-second budget")
    output_paths = [c["source_type"], c["source_refs"], c["child_type"], c["child_refs"]]
    if which == "c2":
        output_paths += [V/"ap5"/which/(prefix + str(i) + ".json")
                         for prefix in ("source-helper-references-", "child-helper-references-")
                         for i in range(1, 4)]
    cert = {"schema_version": 1, "artifact_kind": "successive-approximations-proved-child-actual-import-validation",
            "validated": True, "stage": "verification/ap5/" + which, "theorem_name": c["theorem"],
            "module": c["module"], "child_source": producer.rel(c["source"]),
            "child_source_sha256": stage.sha(c["source"]),
            "child_olean": stage.read(c["snapshot_manifest"])["child_olean"],
            "child_olean_sha256": stage.read(c["snapshot_manifest"])["child_olean_sha256"],
            "parent_validation_sha256": stage.sha(c["parent_validation"]),
            "parent_implementation_hashes": pv["implementation_hashes"],
            "parent_output_json_sha256": pv["output_json_sha256"],
            "own_accepted_receipt_sha256": stage.sha(c["publication"]),
            "accepted_row": accepted_row, "actual_module_owner": child_ref["owner"],
            "source_module_owner": source_ref["owner"], "source_proof_references": source_ref["valueRefs"],
            "child_proof_references": child_ref["valueRefs"], "helper_rows": helper_rows,
            "source_snapshot_sha256": stage.sha(c["source_snapshot"]),
            "child_snapshot_sha256": stage.sha(c["snapshot"]),
            "source_type_sha256": stage.sha(c["source_type"]),
            "child_type_sha256": stage.sha(c["child_type"]),
            "output_json_sha256": {producer.task_rel(path): stage.sha(path) for path in output_paths},
            "implementation_hashes": stage.implementations(),
            "source_manifest_sha256": stage.sha(c["source_manifest"]),
            "source_snapshot_manifest_sha256": stage.sha(c["source_snapshot_manifest"]),
            "child_snapshot_manifest_sha256": stage.sha(c["snapshot_manifest"]),
            "source_helper_catalog_sha256": stage.sha(V/"ap5"/which/"source-helper-catalog.json") if which == "c2" else None,
            "child_helper_catalog_sha256": stage.sha(V/"ap5"/which/"child-helper-catalog.json") if which == "c2" else None,
            "kernel_type_equal_to_source_target_and_solution": True,
            "source_child_helpers_complete": which != "c2" or len(helper_rows) == 3,
            "Std3_only": True, "max_file_seconds": maximum,
            "source_preflight_replay": source_pf, "child_source_preflight_replay": child_source_pf,
            "child_snapshot_preflight_replay": child_pf,
            "submission_ready": False, "Lean_started_by_validator": False, "API_used": False}
    out = V / "ap5" / which / "actual-child-validation.json"
    producer.dump(out, cert)
    return {"validated": True, "certificate": producer.task_rel(out), "certificate_sha256": stage.sha(out),
            "module": c["module"], "theorem_name": c["theorem"], "max_file_seconds": maximum,
            "Std3_only": True, "helper_count": len(helper_rows)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", choices=stage.SPECS, required=True)
    args = ap.parse_args()
    print(json.dumps(validate(args.stage), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
