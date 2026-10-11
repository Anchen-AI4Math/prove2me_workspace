"""Pure-Python postcompile consumer for actual ap6 imported proved children."""
from __future__ import annotations

import argparse
import json

import stage_ap6_proved_children as stage
import stage_parameter_proved_children as producer
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

V = stage.V
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def need(ok, why):
    if not ok:
        raise ValueError(why)


def kernel_refs(expr):
    found = set()
    def visit(x):
        if not isinstance(x, list):
            return
        if len(x) == 3 and x[0] == "const" and isinstance(x[1], str):
            found.add(x[1])
        elif len(x) >= 3 and x[0] == "projection" and isinstance(x[1], str):
            found.add(x[1])
        for y in x[1:]:
            visit(y)
    visit(expr)
    return sorted(found)


def typed(row, name, *, proof_value):
    need(isinstance(row, dict) and set(row) == {"levelParams", "name", "prettyType", "type", "value"},
         "Wrong type snapshot row schema")
    need(row["name"] == name and (row["value"] is not None) == proof_value,
         "Parent proof-value schema or theorem identity differs")
    return row


def normalized_type(row):
    levels = {n: "u" + str(i) for i, n in enumerate(row["levelParams"])}
    def walk(x):
        if isinstance(x, list):
            if len(x) == 2 and x[0] == "param" and x[1] in levels:
                return ["param", levels[x[1]]]
            return [walk(y) for y in x]
        return x
    return (len(row["levelParams"]), walk(row["type"]))


def imported_ref(path, name, owner, snapshot_module, *, main):
    doc = stage.read(path)
    need(set(doc) == {"schemaVersion", "probeMainModule", "rows"} and doc["schemaVersion"] == 1
         and doc["probeMainModule"] == snapshot_module and len(doc["rows"]) == 1,
         "Actual imported reference probe schema differs")
    r = doc["rows"][0]
    need(set(r) == {"name", "kind", "levelParams", "closedType", "closedValue",
                    "typeRefs", "valueRefs", "axioms", "owner"}, "Actual imported CI row schema differs")
    need(r["name"] == name and r["kind"] == "theorem" and r["closedType"] is True
         and r["closedValue"] is True and set(r["axioms"]).issubset(STD3),
         "Actual imported proof identity/axioms differ")
    own = r["owner"]
    need(set(own) == {"kind", "module", "index"} and own["kind"] == "ImportedModule"
         and own["module"] == owner and type(own["index"]) is int and own["index"] >= 0,
         "Actual imported module owner differs")
    for key in ("levelParams", "typeRefs", "valueRefs", "axioms"):
        x = r[key]
        need(isinstance(x, list) and all(isinstance(y, str) for y in x) and len(x) == len(set(x)),
             "Malformed imported CI parameter/reference/axiom list")
    need(r["typeRefs"] == sorted(r["typeRefs"]) and r["valueRefs"] == sorted(r["valueRefs"])
         and name not in r["valueRefs"] and "solution" not in r["valueRefs"],
         "Actual imported proof references are not canonical or contain self/solution")
    return r


def parent_axioms(c, parent, *, generated):
    preflights = parent["preflights"]
    prefix = "Sol_" if generated else "SnapshotOriginal.lean"
    rows = [(key, value) for key, value in preflights.items() if key.startswith(prefix)]
    need(len(rows) == 1, "Expected one certified parent source/solution axiom log")
    name = "solution" if generated else c["theorem"]
    row = rows[0][1]
    log = row.get("log") or row.get("summary", {}).get("log") or row.get("data", {}).get("log")
    need(isinstance(log, str), "Certified parent axiom log path missing")
    axioms = set(standalone.audit_axioms(context.file(log), name))
    need(axioms.issubset(STD3), "Certified parent source/solution has non-Std3 axiom")
    return axioms


def parent_seconds(parent):
    out = []
    for row in parent["preflights"].values():
        value = row.get("seconds", row.get("summary", {}).get("seconds", row.get("data", {}).get("seconds")))
        need(type(value) in (int, float), "Certified parent compiler timing missing")
        out.append(value)
    return max(out)


def compare_type_to_refs(type_row, ref):
    need(type_row["levelParams"] == ref["levelParams"]
         and kernel_refs(type_row["type"]) == ref["typeRefs"],
         "Actual typeRefs/levelParams differ from kernel type Expr")


def normalize_parent_proof_refs(refs, theorem):
    return sorted(x.replace("solution._proof_", theorem + "._proof_", 1)
                  if x.startswith("solution._proof_") else x for x in refs)


def validate(which):
    c = stage.configure(which)
    producer.check_only(c)
    stage.check_seal(c)
    stage.check_child_seal(c)
    m, parent, publication, accepted = stage.accepted_pins(c)
    d = V / "ap6" / which
    child_source_pf = context.record(c["source"], c["source_manifest"], "emit-olean", c["module"], d)
    source_pf = context.record(c["source_snapshot"], c["source_snapshot_manifest"], "modecheck", "SourceSnapshot", d)
    child_pf = context.record(c["snapshot"], c["snapshot_manifest"], "modecheck", "ChildSnapshot", d)
    for path, pf in ((c["source_type"], source_pf), (c["source_refs"], source_pf),
                     (c["child_type"], child_pf), (c["child_refs"], child_pf)):
        producer.written_during(path, pf["data"])
    old_source, old_generated = (stage.read(c["parent"] / n)
                                 for n in ("original-type.json", "generated-type.json"))
    source_types, child_types = stage.read(c["source_type"]), stage.read(c["child_type"])
    helper_names = stage.HELPERS[which]
    need(len(old_source) == 1 and len(old_generated) == 2
         and len(source_types) == len(child_types) == 1 + len(helper_names),
         "Parent/fresh type domains differ")
    old_gen = {r["name"]: r for r in old_generated}
    source_map = {r["name"]: r for r in source_types}
    child_map = {r["name"]: r for r in child_types}
    need(set(source_map) == set(child_map) == {c["theorem"], *helper_names},
         "Actual source/child theorem and provided-name domains differ")
    legacy = which in ("c1", "c2")
    main_rows = [typed(old_source[0], c["theorem"], proof_value=legacy),
                 typed(old_gen[c["theorem"]], c["theorem"], proof_value=legacy),
                 typed(old_gen["solution"], "solution", proof_value=legacy),
                 typed(source_map[c["theorem"]], c["theorem"], proof_value=False),
                 typed(child_map[c["theorem"]], c["theorem"], proof_value=False)]
    need(len({json.dumps(normalized_type(r), sort_keys=True) for r in main_rows}) == 1,
         "Actual child theorem kernel type differs from parent source/target/solution")
    source_module = stage.source_component(m)["source_module"]
    source_ref = imported_ref(c["source_refs"], c["theorem"], source_module, "SourceSnapshot", main=True)
    child_ref = imported_ref(c["child_refs"], c["theorem"], c["module"], "ChildSnapshot", main=True)
    source_axioms = parent_axioms(c, parent, generated=False)
    solution_axioms = parent_axioms(c, parent, generated=True)
    need(set(source_ref["axioms"]) == source_axioms and set(child_ref["axioms"]) == solution_axioms,
         "Fresh source/child main axioms differ from exact certified parent proof")
    compare_type_to_refs(main_rows[3], source_ref)
    compare_type_to_refs(main_rows[4], child_ref)
    if legacy:
        expected_parent_refs = kernel_refs(main_rows[2]["value"])
    else:
        parent_refs = stage.read(c["parent"] / "proof-references.json")["rows"]
        own = next((r for r in parent_refs if r.get("name") == "solution"), None)
        need(own is not None and main_rows[2]["levelParams"] == own["levelParams"]
             and kernel_refs(main_rows[2]["type"]) == own["typeRefs"],
             "Modern parent solution CI proof/type reference row differs")
        expected_parent_refs = own["valueRefs"]
    need(child_ref["valueRefs"] == normalize_parent_proof_refs(expected_parent_refs, c["theorem"]),
         "Actual child proof references differ from certified parent solution")
    helper_certificates = []
    old_helpers = {r["name"]: r for r in stage.read(c["parent"] / "original-public-inline-types.json")} if which == "c3" else {}
    generated_helpers = {r["name"]: r for r in stage.read(c["parent"] / "generated-public-inline-types.json")} if which == "c3" else {}
    if which == "c3":
        need(set(old_helpers) == set(generated_helpers) == set(helper_names),
             "Certified dimension public helper catalog differs")
    for i, name in enumerate(helper_names, 1):
        st = typed(source_map[name], name, proof_value=False)
        ct = typed(child_map[name], name, proof_value=False)
        compared = [st, ct]
        if which == "c3":
            compared += [typed(old_helpers[name], name, proof_value=False),
                         typed(generated_helpers[name], name, proof_value=False)]
        need(len({json.dumps(normalized_type(r), sort_keys=True) for r in compared}) == 1,
             "Actual child helper type differs from genuine source: " + name)
        srpath = d / ("source-helper-references-" + str(i) + ".json")
        crpath = d / ("child-helper-references-" + str(i) + ".json")
        producer.written_during(srpath, source_pf["data"])
        producer.written_during(crpath, child_pf["data"])
        sr = imported_ref(srpath, name, source_module, "SourceSnapshot", main=False)
        cr = imported_ref(crpath, name, c["module"], "ChildSnapshot", main=False)
        compare_type_to_refs(st, sr)
        compare_type_to_refs(ct, cr)
        if which == "c3":
            parent_row = next((r for r in stage.read(c["parent"] / "proof-references.json")["rows"]
                               if r.get("name") == name), None)
            need(parent_row is not None and cr["valueRefs"] == parent_row["valueRefs"],
                 "Dimension helper proof references differ from parent: " + name)
        helper_certificates.append({"name": name, "source_owner": sr["owner"],
            "child_owner": cr["owner"], "source_ref_sha256": stage.sha(srpath),
            "child_ref_sha256": stage.sha(crpath), "source_axioms": sr["axioms"],
            "child_axioms": cr["axioms"]})
    for pf, expected in ((child_source_pf, solution_axioms), (source_pf, source_axioms),
                         (child_pf, solution_axioms)):
        need(set(standalone.audit_axioms(context.file(pf["data"]["log"]), c["theorem"])) == expected,
             "Main theorem compiler axiom audit differs from certified parent proof")
    for name in helper_names:
        for pf in (source_pf, child_pf):
            need(set(standalone.audit_axioms(context.file(pf["data"]["log"]), name)).issubset(STD3),
                 "Helper compiler axiom audit exceeds Std3: " + name)
    maximum = max(*(pf["data"]["seconds"] for pf in (child_source_pf, source_pf, child_pf)),
                  parent_seconds(parent))
    need(maximum <= 300, "A proved-child file exceeded the 300-second limit")
    output_paths = [c["source_type"], c["source_refs"], c["child_type"], c["child_refs"]]
    output_paths += [d/(prefix + str(i) + ".json")
                     for prefix in ("source-helper-references-", "child-helper-references-")
                     for i in range(1, 1 + len(helper_names))]
    cert = {"schema_version": 1, "artifact_kind": "ap6-proved-child-actual-import-validation",
        "validated": True, "stage": "verification/ap6/" + which, "module": c["module"],
        "theorem_name": c["theorem"], "parent_validation_sha256": stage.sha(c["parent_validation"]),
        "own_accepted_publication_sha256": stage.sha(c["publication"]),
        "accepted_row": accepted, "source_proof_sha256": stage.sha(stage.ROOT / m["solution"]),
        "child_source_sha256": stage.sha(c["source"]),
        "child_olean": stage.read(c["snapshot_manifest"])["child_olean"],
        "child_olean_sha256": stage.read(c["snapshot_manifest"])["child_olean_sha256"],
        "source_owner": source_ref["owner"], "actual_child_owner": child_ref["owner"],
        "parent_source_value_schema": "legacy-full-proof" if legacy else "modern-type-only",
        "fresh_source_and_child_values_null": True,
        "kernel_type_equal_to_parent_source_target_solution": True,
        "actual_typeRefs_equal_kernel_type_constants": True,
        "child_proof_references_equal_parent_solution": True,
        "provided_names": list(helper_names), "helper_certificates": helper_certificates,
        "source_axioms": sorted(source_axioms), "child_axioms": sorted(solution_axioms),
        "Std3_only": True, "max_file_seconds": maximum,
        "output_json_sha256": {producer.task_rel(path): stage.sha(path) for path in output_paths},
        "implementation_hashes": stage.impl_hashes(),
        "source_manifest_sha256": stage.sha(c["source_manifest"]),
        "source_snapshot_manifest_sha256": stage.sha(c["source_snapshot_manifest"]),
        "child_snapshot_manifest_sha256": stage.sha(c["snapshot_manifest"]),
        "source_helper_catalog_sha256": stage.sha(d/"source-helper-catalog.json") if helper_names else None,
        "child_helper_catalog_sha256": stage.sha(d/"child-helper-catalog.json") if helper_names else None,
        "source_preflight_replay": source_pf, "child_source_preflight_replay": child_source_pf,
        "child_snapshot_preflight_replay": child_pf,
        "submission_ready": False, "Lean_started_by_validator": False, "API_used": False}
    out = d / "actual-child-validation.json"
    producer.dump(out, cert)
    return {"validated": True, "certificate": producer.task_rel(out),
            "certificate_sha256": stage.sha(out), "module": c["module"],
            "helper_count": len(helper_names), "max_file_seconds": maximum,
            "Std3_only": True}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", choices=stage.SPECS, required=True)
    args = ap.parse_args()
    print(json.dumps(validate(args.stage), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
