"""Pure evidence consumer for the two-module ap6/c3e Dimension proved child."""
from __future__ import annotations

import json

import stage_ap6_c3e_dimension_child as stage
import stage_parameter_proved_children as producer
import validate_ap6_proved_children as base
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone


def validate():
    c = stage.config()
    stage.check(c, child=True)
    m, parent, publication, accepted = stage.old.accepted_pins(c)
    owners = stage.owners(c)
    d = stage.D
    child_source_pf = context.record(c["source"], c["source_manifest"], "emit-olean", c["module"], d)
    source_pf = context.record(c["source_snapshot"], c["source_snapshot_manifest"], "modecheck", "SourceSnapshot", d)
    child_pf = context.record(c["snapshot"], c["snapshot_manifest"], "modecheck", "ChildSnapshot", d)
    for path, pf in ((c["source_type"], source_pf), (c["source_refs"], source_pf),
                     (c["child_type"], child_pf), (c["child_refs"], child_pf)):
        producer.written_during(path, pf["data"])
    old_source, old_generated = (stage.old.read(c["parent"] / n)
                                 for n in ("original-type.json", "generated-type.json"))
    source_types, child_types = stage.old.read(c["source_type"]), stage.old.read(c["child_type"])
    old_gen = {r["name"]: r for r in old_generated}
    source_map = {r["name"]: r for r in source_types}
    child_map = {r["name"]: r for r in child_types}
    base.need(len(old_source) == 1 and len(old_generated) == 2
              and len(source_types) == len(child_types) == 8
              and set(source_map) == set(child_map) == set(owners),
              "Certified/fresh Dimension type domains differ")
    main_rows = [base.typed(old_source[0], c["theorem"], proof_value=False),
                 base.typed(old_gen[c["theorem"]], c["theorem"], proof_value=False),
                 base.typed(old_gen["solution"], "solution", proof_value=False),
                 base.typed(source_map[c["theorem"]], c["theorem"], proof_value=False),
                 base.typed(child_map[c["theorem"]], c["theorem"], proof_value=False)]
    base.need(len({json.dumps(base.normalized_type(r), sort_keys=True) for r in main_rows}) == 1,
              "Dimension main kernel type differs across parent/source/child")
    sr = base.imported_ref(c["source_refs"], c["theorem"], owners[c["theorem"]],
                           "SourceSnapshot", main=True)
    cr = base.imported_ref(c["child_refs"], c["theorem"], c["module"],
                           "ChildSnapshot", main=True)
    base.compare_type_to_refs(main_rows[3], sr)
    base.compare_type_to_refs(main_rows[4], cr)
    source_axioms = base.parent_axioms(c, parent, generated=False)
    solution_axioms = base.parent_axioms(c, parent, generated=True)
    base.need(set(sr["axioms"]) == source_axioms and set(cr["axioms"]) == solution_axioms,
              "Fresh main axioms differ from certified Dimension parent")
    parent_refs = stage.old.read(c["parent"] / "proof-references.json")["rows"]
    parent_solution = next((r for r in parent_refs if r.get("name") == "solution"), None)
    base.need(parent_solution is not None
              and parent_solution["levelParams"] == main_rows[2]["levelParams"]
              and parent_solution["typeRefs"] == base.kernel_refs(main_rows[2]["type"]),
              "Certified parent solution CI type references differ")
    base.need(cr["valueRefs"] == base.normalize_parent_proof_refs(parent_solution["valueRefs"], c["theorem"]),
              "Actual proved child references differ from parent solution")
    old_helpers = {r["name"]: r for r in stage.old.read(c["parent"] / "original-public-inline-types.json")}
    gen_helpers = {r["name"]: r for r in stage.old.read(c["parent"] / "generated-public-inline-types.json")}
    base.need(set(old_helpers) == set(gen_helpers) == set(stage.HELPERS),
              "Seven certified public helpers differ")
    helper_certificates = []
    output_paths = [c["source_type"], c["source_refs"], c["child_type"], c["child_refs"]]
    for i, name in enumerate(stage.HELPERS, 1):
        rows = [base.typed(source_map[name], name, proof_value=False),
                base.typed(child_map[name], name, proof_value=False),
                base.typed(old_helpers[name], name, proof_value=False),
                base.typed(gen_helpers[name], name, proof_value=False)]
        base.need(len({json.dumps(base.normalized_type(r), sort_keys=True) for r in rows}) == 1,
                  "Dimension helper kernel type differs: " + name)
        srpath = d / ("source-helper-references-" + str(i) + ".json")
        crpath = d / ("child-helper-references-" + str(i) + ".json")
        producer.written_during(srpath, source_pf["data"])
        producer.written_during(crpath, child_pf["data"])
        helper_sr = base.imported_ref(srpath, name, owners[name], "SourceSnapshot", main=False)
        helper_cr = base.imported_ref(crpath, name, c["module"], "ChildSnapshot", main=False)
        base.compare_type_to_refs(rows[0], helper_sr)
        base.compare_type_to_refs(rows[1], helper_cr)
        parent_row = next((r for r in parent_refs if r.get("name") == name), None)
        base.need(parent_row is not None and parent_row["levelParams"] == rows[3]["levelParams"]
                  and parent_row["typeRefs"] == base.kernel_refs(rows[3]["type"])
                  and helper_cr["valueRefs"] == parent_row["valueRefs"],
                  "Dimension helper actual proof references differ: " + name)
        helper_certificates.append({"name": name, "source_owner": helper_sr["owner"],
            "child_owner": helper_cr["owner"], "source_refs_sha256": stage.old.sha(srpath),
            "child_refs_sha256": stage.old.sha(crpath), "source_axioms": helper_sr["axioms"],
            "child_axioms": helper_cr["axioms"]})
        output_paths += [srpath, crpath]
    for pf, axioms in ((child_source_pf, solution_axioms), (source_pf, source_axioms),
                       (child_pf, solution_axioms)):
        base.need(set(standalone.audit_axioms(context.file(pf["data"]["log"]), c["theorem"])) == axioms,
                  "Fresh Dimension main axiom log differs")
    for name in stage.HELPERS:
        for pf in (source_pf, child_pf):
            base.need(set(standalone.audit_axioms(context.file(pf["data"]["log"]), name)).issubset(base.STD3),
                      "Dimension helper axiom log exceeds Std3: " + name)
    maximum = max(*(pf["data"]["seconds"] for pf in (child_source_pf, source_pf, child_pf)),
                  base.parent_seconds(parent))
    base.need(maximum <= 300, "Dimension child file exceeded 300 seconds")
    sm = stage.old.read(c["snapshot_manifest"])
    cert = {"schema_version": 1, "artifact_kind": "ap6-c3e-two-module-proved-child-actual-validation",
        "validated": True, "stage": "verification/ap6/c3e", "theorem_name": c["theorem"],
        "module": c["module"], "parent_validation_sha256": stage.old.sha(c["parent_validation"]),
        "own_accepted_publication_sha256": stage.old.sha(c["publication"]), "accepted_row": accepted,
        "source_proof_sha256": stage.old.sha(stage.ROOT / m["solution"]),
        "child_source_sha256": stage.old.sha(c["source"]),
        "child_olean": sm["child_olean"], "child_olean_sha256": sm["child_olean_sha256"],
        "source_owner_by_name": owners, "actual_source_main_owner": sr["owner"],
        "actual_child_main_owner": cr["owner"], "actual_helper_certificates": helper_certificates,
        "parent_and_fresh_values_null": True, "main_and_seven_helper_kernel_types_equal": True,
        "type_refs_equal_kernel_type_constants": True,
        "child_proof_refs_equal_parent_solution_and_helpers": True,
        "source_axioms": sorted(source_axioms), "child_axioms": sorted(solution_axioms),
        "Std3_only": True, "max_file_seconds": maximum,
        "output_json_sha256": {producer.task_rel(p): stage.old.sha(p) for p in output_paths},
        "implementation_hashes": stage.impl_hashes(),
        "source_manifest_sha256": stage.old.sha(c["source_manifest"]),
        "source_snapshot_manifest_sha256": stage.old.sha(c["source_snapshot_manifest"]),
        "child_snapshot_manifest_sha256": stage.old.sha(c["snapshot_manifest"]),
        "source_helper_catalog_sha256": stage.old.sha(d/"source-helper-catalog.json"),
        "child_helper_catalog_sha256": stage.old.sha(d/"child-helper-catalog.json"),
        "source_preflight_replay": source_pf, "child_source_preflight_replay": child_source_pf,
        "child_snapshot_preflight_replay": child_pf,
        "submission_ready": False, "Lean_started_by_validator": False, "API_used": False}
    out = d / "actual-child-validation.json"
    producer.dump(out, cert)
    return {"validated": True, "certificate": producer.task_rel(out),
            "certificate_sha256": stage.old.sha(out), "max_file_seconds": maximum,
            "helper_count": len(helper_certificates), "Std3_only": True,
            "Lean_started": False, "API_used": False}


if __name__ == "__main__":
    print(json.dumps(validate(), ensure_ascii=False, indent=2))
