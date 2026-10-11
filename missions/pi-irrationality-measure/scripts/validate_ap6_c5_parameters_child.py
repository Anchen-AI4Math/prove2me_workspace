"""Pure-Python validation of the actual imported ap6/c5 Parameters proved child."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import stage_ap6_c5_parameters_child as stage
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

STD3 = {"propext", "Classical.choice", "Quot.sound"}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def row_map(path: Path, names: set[str]):
    rows = stage.read(path)
    need(isinstance(rows, list) and len(rows) == len(names)
         and {r.get("name") for r in rows} == names,
         "Type-only snapshot declaration domain differs")
    for r in rows:
        need(set(r) == {"levelParams", "name", "prettyType", "type", "value"}
             and r["value"] is None, "Proof value is not null in a modern type-only snapshot")
    return {r["name"]: r for r in rows}


def normalized_type(row):
    levels = {name: "u" + str(i) for i, name in enumerate(row["levelParams"])}
    def walk(x):
        if isinstance(x, list):
            if len(x) == 2 and x[0] == "param" and x[1] in levels:
                return ["param", levels[x[1]]]
            return [walk(y) for y in x]
        return x
    return (len(row["levelParams"]), walk(row["type"]))


def kernel_refs(expr):
    found = set()
    def walk(x):
        if not isinstance(x, list):
            return
        if len(x) == 3 and x[0] == "const" and isinstance(x[1], str):
            found.add(x[1])
        elif len(x) >= 3 and x[0] == "projection" and isinstance(x[1], str):
            found.add(x[1])
        for child in x[1:]:
            walk(child)
    walk(expr)
    return sorted(found)


def refs(path: Path, names: set[str], owner: str, main_module: str):
    doc = stage.read(path)
    need(set(doc) == {"schemaVersion", "probeMainModule", "rows"}
         and doc["schemaVersion"] == 1 and doc["probeMainModule"] == main_module
         and {r.get("name") for r in doc["rows"]} == names,
         "Actual imported proof-reference snapshot domain differs")
    out = {}
    for r in doc["rows"]:
        need(set(r) == {"name", "kind", "levelParams", "closedType", "closedValue",
                        "typeRefs", "valueRefs", "axioms", "owner"}
             and r["kind"] == "theorem" and r["closedType"] is True and r["closedValue"] is True
             and set(r["axioms"]).issubset(STD3),
             "Imported theorem CI closure/kind/axioms differ")
        own = r["owner"]
        need(set(own) == {"kind", "module", "index"} and own["kind"] == "ImportedModule"
             and own["module"] == owner and type(own["index"]) is int and own["index"] >= 0,
             "Actual imported module owner differs")
        for key in ("levelParams", "typeRefs", "valueRefs", "axioms"):
            values = r[key]
            need(isinstance(values, list) and all(isinstance(x, str) for x in values)
                 and len(values) == len(set(values)), "Malformed imported CI refs/levels/axioms")
        need(r["typeRefs"] == sorted(r["typeRefs"]) and r["valueRefs"] == sorted(r["valueRefs"])
             and r["name"] not in r["valueRefs"] and "solution" not in r["valueRefs"],
             "Imported proof references contain self/solution or are unsorted")
        out[r["name"]] = r
    return out


def preflight(path: Path, manifest: Path, mode: str, module: str):
    stage.checked_manifest(path, manifest)
    return context.record(path, manifest, mode, module, stage.STAGE)


def written(path: Path, pf):
    stage.runner.sha_file(path)
    from datetime import datetime
    finish = datetime.fromisoformat(pf["data"]["at_utc"]).timestamp()
    need(finish - pf["data"]["seconds"] - 2 <= path.stat().st_mtime <= finish + 2,
         "JSON output was not written by its exact Lean preflight")


def main():
    stage.check_only()
    m, v, p = stage.certified_parent()
    stage.checked_manifest(stage.CHILD_SNAPSHOT, stage.CHILD_SNAPSHOT_MANIFEST)
    source_pf = preflight(stage.SOURCE_SNAPSHOT, stage.SOURCE_SNAPSHOT_MANIFEST, "modecheck", "SourceSnapshot")
    child_source_pf = preflight(stage.SOURCE, stage.SOURCE_MANIFEST, "emit-olean", stage.MODULE)
    child_pf = preflight(stage.CHILD_SNAPSHOT, stage.CHILD_SNAPSHOT_MANIFEST, "modecheck", "ChildSnapshot")
    source_type = stage.STAGE / "source-type.json"
    child_type = stage.STAGE / "child-type.json"
    source_refs = stage.STAGE / "source-proof-references.json"
    child_refs = stage.STAGE / "child-proof-references.json"
    for path in (source_type, source_refs):
        written(path, source_pf)
    for path in (child_type, child_refs):
        written(path, child_pf)
    domain = {stage.HELPER, stage.THEOREM}
    old_source = row_map(stage.PARENT / "original-type.json", domain)
    old_generated = row_map(stage.PARENT / "generated-type.json", domain | {"solution"})
    fresh_source = row_map(source_type, domain)
    fresh_child = row_map(child_type, domain)
    for name in domain:
        compared = [old_source[name], old_generated[name], fresh_source[name], fresh_child[name]]
        if name == stage.THEOREM:
            compared.append(old_generated["solution"])
        need(len({json.dumps(normalized_type(r), sort_keys=True) for r in compared}) == 1,
             "Actual imported child type differs from source/target/solution: " + name)
    src = refs(source_refs, domain, m["source_module"], "SourceSnapshot")
    child = refs(child_refs, domain, stage.MODULE, "ChildSnapshot")
    parent_refs_doc = stage.read(stage.PARENT / "proof-references.json")
    parent_refs = {r["name"]: r for r in parent_refs_doc["rows"]}
    need(set(parent_refs) == {stage.HELPER, "solution"}, "Certified parent helper/Sol refs domain differs")
    for name in domain:
        for typ, ref in ((fresh_source[name], src[name]), (fresh_child[name], child[name])):
            need(typ["levelParams"] == ref["levelParams"]
                 and kernel_refs(typ["type"]) == ref["typeRefs"],
                 "Actual typeRefs/universe params differ from kernel Expr: " + name)
    need(old_generated["solution"]["levelParams"] == parent_refs["solution"]["levelParams"]
         and kernel_refs(old_generated["solution"]["type"]) == parent_refs["solution"]["typeRefs"],
         "Certified parent solution type refs differ from kernel Expr")
    for name, parent_name in ((stage.THEOREM, "solution"), (stage.HELPER, stage.HELPER)):
        expected = [x.replace("solution._proof_", stage.THEOREM + "._proof_", 1)
                    if x.startswith("solution._proof_") else x
                    for x in parent_refs[parent_name]["valueRefs"]]
        need(child[name]["valueRefs"] == sorted(expected),
             "Actual child proof refs differ from certified parent Sol/helper: " + name)
    for name in domain:
        source_expected = set(v["source_axioms"][name])
        child_expected = set(v["solution_axioms"]) if name == stage.THEOREM else set(parent_refs[name]["axioms"])
        need(set(src[name]["axioms"]) == source_expected and set(child[name]["axioms"]) == child_expected,
             "Actual imported axiom sets differ from certified parent: " + name)
        need(set(standalone.audit_axioms(context.file(source_pf["data"]["log"]), name)) == source_expected
             and set(standalone.audit_axioms(context.file(child_pf["data"]["log"]), name)) == child_expected,
             "Snapshot compiler axiom audit differs from exact parent: " + name)
    need(set(standalone.audit_axioms(context.file(child_source_pf["data"]["log"]), stage.THEOREM)) == set(v["solution_axioms"]),
         "Emitted child compiler axiom audit differs from certified parent solution")
    maximum = max(v["max_file_seconds"], *(x["data"]["seconds"] for x in (source_pf, child_source_pf, child_pf)))
    need(maximum <= 300, "A single ap6/c5 file exceeded the 300-second budget")
    output_paths = (source_type, child_type, source_refs, child_refs)
    cert = {"schema_version": 1, "artifact_kind": "ap6-c5-parameters-proved-child-actual-import-validation",
        "validated": True, "module": stage.MODULE, "theorem_name": stage.THEOREM,
        "provided_names": [stage.HELPER], "parent_validation_sha256": stage.sha(stage.PARENT_VALIDATION),
        "parent_implementation_hashes": v["implementation_hashes"],
        "parent_output_json_sha256": v["output_json_sha256"],
        "own_accepted_publication_sha256": stage.sha(stage.PUBLICATION),
        "child_source_sha256": stage.sha(stage.SOURCE),
        "child_olean": stage.read(stage.CHILD_SNAPSHOT_MANIFEST)["child_olean"],
        "child_olean_sha256": stage.read(stage.CHILD_SNAPSHOT_MANIFEST)["child_olean_sha256"],
        "source_actual_owners": {name: src[name]["owner"] for name in domain},
        "child_actual_owners": {name: child[name]["owner"] for name in domain},
        "parent_and_fresh_proof_values_null": True,
        "source_target_solution_and_child_types_equal": True,
        "actual_typeRefs_equal_kernel_type_constants": True,
        "proof_references_equal_certified_parent": True,
        "source_axioms": v["source_axioms"], "child_axioms": {name: child[name]["axioms"] for name in domain},
        "Std3_only": True, "max_file_seconds": maximum,
        "output_json_sha256": {stage.task_rel(path): stage.sha(path) for path in output_paths},
        "implementation_hashes": stage.impl(),
        "source_manifest_sha256": stage.sha(stage.SOURCE_MANIFEST),
        "source_snapshot_manifest_sha256": stage.sha(stage.SOURCE_SNAPSHOT_MANIFEST),
        "child_snapshot_manifest_sha256": stage.sha(stage.CHILD_SNAPSHOT_MANIFEST),
        "source_preflight_replay": source_pf, "child_source_preflight_replay": child_source_pf,
        "child_snapshot_preflight_replay": child_pf,
        "submission_ready": False, "Lean_started_by_consumer": False, "API_used": False}
    out = stage.STAGE / "actual-child-validation.json"
    stage.dump(out, cert)
    print(json.dumps({"validated": True, "certificate": stage.task_rel(out),
        "certificate_sha256": stage.sha(out), "module": stage.MODULE,
        "helper": stage.HELPER, "max_file_seconds": maximum,
        "Std3_only": True, "Lean_started": False, "API_used": False},
        ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
