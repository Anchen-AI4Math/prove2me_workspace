"""Strict AP19 four-Def full CI/value/owner/Std3 replay, with actual owned CI inventory."""
from __future__ import annotations

import argparse
from datetime import datetime
import json
from pathlib import Path

import stage_analytic_remainder_data_provider as prep
import validate_namespace_context_providers as context
from certify_command_emission_probe import checked_expr

SELF = Path(__file__).resolve()
STD3 = {"propext", "Classical.choice", "Quot.sound"}
ROW_FIELDS = {"schemaVersion", "kernelMetadataSchema", "sourceName", "resolvedName",
    "sourceModule", "declGraphSha256", "declGraphRowSha256", "graphKind", "envKind",
    "ownerKind", "ownerId", "commandUnit", "familyRoot", "levelParams", "closedType",
    "closedValue", "type", "value", "axioms", "kindMetadata", "familyReferences", "transitiveNames"}


def need(ok, message): prep.need(ok, message)


def rows(path, record, expected_count):
    result = [json.loads(x) for x in path.read_text(encoding="utf-8").splitlines() if x.strip()]
    need(len(result) == expected_count, "Actual full-CI snapshot domain differs")
    end = datetime.fromisoformat(record["data"]["at_utc"]).timestamp()
    need(end - record["data"]["seconds"] - 2 <= path.stat().st_mtime <= end + 2,
         "Snapshot write was outside the actual compiler interval")
    return result



def owned_inventory(stage,pf,generated):
    path=stage/prep.INVENTORY_JSON;doc=prep.read(path)
    end=datetime.fromisoformat(pf["data"]["at_utc"]).timestamp()
    need(end-pf["data"]["seconds"]-2<=path.stat().st_mtime<=end+2,"Owned inventory was not written in the actual compiler interval")
    need(set(doc)=={"schemaVersion","probeMainModule","providerModule","rawOwnedCIs"}
         and doc["schemaVersion"]==1 and doc["probeMainModule"]=="GeneratedSnapshot"
         and doc["providerModule"]==prep.PLATFORM_MODULE,"Raw owned inventory envelope differs")
    rows=doc["rawOwnedCIs"];names=[r["name"] for r in rows]
    need(names==sorted(prep.NAMES),"Unexpected owned compiler CIs; full early inventory is preserved for exact audit")
    by_name={r["resolvedName"]:r for r in generated}
    from certify_full_row_minor_node import refs
    for r in rows:
        need(set(r)=={"name","owner","privateUserName","kind","levelParams","closedType","closedValue","isProp","type","value","typeRefs","valueRefs","axioms"}
             and r["owner"]==prep.PLATFORM_MODULE and r["privateUserName"] is None and r["kind"]=="def"
             and r["closedType"] is True and r["closedValue"] is True and r["isProp"] is False,
             "Actual raw owned CI kind/closure/owner differs")
        primary=by_name[r["name"]]
        need(all(r[k]==primary[k] for k in ["levelParams","type","value","axioms"])
             and r["typeRefs"]==refs(r["type"]) and r["valueRefs"]==refs(r["value"]),
             "Actual raw owned CI is not the same full exported primary Def")
    return doc


def validate(key):
    prep.check_only(key)
    c = prep.config(key); stage = c["stage"]
    p = prep.read(stage / "preparation.json")
    need(p["validated"] is False and p["submission_ready"] is False and p["proposal_status"] == "Draft",
         "Preparation stage flags differ")
    units = prep.authority()
    records = {}
    for i, (filename, mode, module) in enumerate([
            (c["provider_file"], "emit-olean", c["platform_module"]),
            (prep.SOURCE_SNAPSHOT, "modecheck", "SourceSnapshot"),
            (prep.GENERATED_SNAPSHOT, "modecheck", "GeneratedSnapshot")], 1):
        record = context.record(stage / filename, stage / f"c{i}.json", mode, module, stage)
        data = record["data"]
        need(data["mode"] == mode and 0 < data["seconds"] <= 300 and data["timeout_seconds"] == 300
             and data["exit_code"] == 0 and data["timed_out"] is False and data["success"] is True,
             "Actual bounded compiler witness did not pass")
        need("emit_olean" not in data, "Unknown legacy compiler record shape")
        need(data.get('runner')==prep.rel(prep.RUNNER) and data.get('runner_sha256')==prep.sha(prep.RUNNER) and data.get('legacy_runner_sha256')==prep.sha(prep.base.PREFLIGHT) and data.get('cleanup_completed') is True,'Actual bounded runner provenance differs')
        records[filename] = record
    emitted = records[c["provider_file"]]["data"]
    expected = prep.TASK / p["expected_provider_olean"]
    need(emitted["output_olean"] == prep.rel(expected)
         and emitted["output_olean_sha256"] == prep.sha(expected), "Provider OLean path/hash differs")
    for filename in [prep.SOURCE_SNAPSHOT, prep.GENERATED_SNAPSHOT]:
        need(records[filename]["data"]["output_olean"] is None
             and records[filename]["data"]["output_olean_sha256"] is None, "Snapshot emitted an OLean")
    from certify_full_row_minor_node import imported_dep
    dep=imported_dep(records[prep.GENERATED_SNAPSHOT],c['platform_module'])
    need(Path(dep['path']).resolve()==expected.resolve() and dep['sha256_before']==prep.sha(expected),'Actual generated full CI probe imported a different provider OLean')
    source_rows = rows(stage / prep.SOURCE_JSON, records[prep.SOURCE_SNAPSHOT], len(units))
    generated_rows = rows(stage / prep.GENERATED_JSON, records[prep.GENERATED_SNAPSHOT], len(units))
    inherited,_=prep.inherited_binding(); differences=[]
    axioms = {}; owners = {"source": {}, "generated": {}}
    for unit, left, right in zip(units, source_rows, generated_rows, strict=True):
        owner = unit["owner"]; name = unit["name"]
        for side, row, module in [("source", left, unit["source_module"]), ("generated", right, c["platform_module"])]:
            need(set(row) == ROW_FIELDS and row["schemaVersion"] == 2
                 and row["kernelMetadataSchema"] == "lean-4.33.1-ConstantInfo-complete-v1"
                 and row["sourceName"] == name and row["resolvedName"] == name
                 and row["sourceModule"] == module and row["graphKind"] == "def" and row["envKind"] == "def"
                 and row["declGraphSha256"] == owner["decl_graph_sha256"]
                 and row["declGraphRowSha256"] == owner["decl_graph_row_sha256"]
                 and row["ownerKind"] == owner["owner_kind"] and row["ownerId"] == owner["owner_id"]
                 and row["commandUnit"] == owner["command_unit"] and row["familyRoot"] == name
                 and row["closedType"] is True and row["closedValue"] is True and row["value"] is not None
                 and row["kindMetadata"] == {"valueExported": True, "safety": "Lean.DefinitionSafety.safe"},
                 "Exact CI kind/closure/source/module-owner binding differs: " + side + ":" + name)
            levels = row["levelParams"]
            need(isinstance(levels, list) and all(isinstance(x,str) for x in levels) and len(set(levels)) == len(levels), "Universe domain invalid")
            checked_expr(row["type"],set(levels));checked_expr(row["value"],set(levels))
            need(isinstance(row["axioms"],list) and row["axioms"] == sorted(set(row["axioms"]))
                 and set(row["axioms"]) <= STD3, "Provider contains nonstandard axioms")
            need(row["familyReferences"] == [] and row["transitiveNames"] == [], "Unexpected structural CI closure in tiny Def provider")
            axioms[side + ":" + name] = row["axioms"]; owners[side][name] = module
        expected_value=left["value"]
        if expected_value!=right["value"]:
            expected_value=prep.core_cert.pair.replace_constant(expected_value)
            need(expected_value!=left["value"],"Unknown full Def value difference: "+name)
            differences.append({"name":name,"source_value_sha256":prep.sha_bytes(prep.encode(left["value"])),
                "generated_value_sha256":prep.sha_bytes(prep.encode(right["value"])),
                "exact_inherited_closed_Prop_helper_pair":[inherited["certified_actual_helper_pair"]["source_name"],
                    inherited["certified_actual_helper_pair"]["generated_name"]]})
        need(left["levelParams"] == right["levelParams"] and left["type"] == right["type"]
             and expected_value == right["value"] and left["axioms"] == right["axioms"],
             "Source/generated kernel type, complete value or Std3 differs: " + name)
    inventory=owned_inventory(stage,records[prep.GENERATED_SNAPSHOT],generated_rows)
    core_dep=imported_dep(records[c["provider_file"]],prep.CORE_MODULE)
    need(core_dep["sha256_before"]==prep.CORE_OLEAN_SHA,"Actual emitter used a different canonical CoreData OLean")
    return {
        "schema_version": 1, "artifact_kind": "ap19-analytic-remainder-four-Def-actual-provider-validation",
        "source_commit": prep.COMMIT, "source_modules": prep.SOURCE_MODULES,
        "source_module_by_name": {u["name"]:u["source_module"] for u in units},
        "platform_module": c["platform_module"], "provided_names": c["names"],
        "provider_source_sha256": prep.sha(stage / c["provider_file"]),
        "provider_olean": prep.rel(expected), "provider_olean_sha256": prep.sha(expected),
        "preparation_sha256": prep.sha(stage / "preparation.json"),
        "compiler_manifest_sha256": {f"c{i}.json":prep.sha(stage/f"c{i}.json") for i in range(1,4)},
        "preflights": records, "source_and_generated_types_equal": True,
        "definition_values_equal_and_exported": not differences, "contains_theorems": False,
        "raw_definition_values_equal": not differences,"raw_equal_definition_count":len(units)-len(differences),
        "definition_values_equal_after_exact_inherited_closed_Prop_substitution":True,
        "actual_definition_value_proof_cache_differences":differences,
        "canonical_CoreData_certificate_sha256":prep.sha(prep.CORE_CERT),
        "canonical_CoreData_definition_id":"03bc0316-3599-4c4d-97a8-3fce8ad984af",
        "canonical_CoreData_OLean_sha256":prep.CORE_OLEAN_SHA,
        "canonical_CoreData_raw_equal_definitions":12,
        "canonical_CoreData_actual_closed_Prop_substitution_defs":2,
        "raw_owned_CI_inventory_exact":True,"actual_owned_public_names":[r["name"] for r in inventory["rawOwnedCIs"]],
        "actual_owners": owners, "axioms": axioms, "Std3_only": True,
        "output_json_sha256": {prep.rel(stage/x):prep.sha(stage/x) for x in [prep.SOURCE_JSON,prep.GENERATED_JSON,prep.INVENTORY_JSON]},
        "implementation_hashes": {prep.rel(x):prep.sha(x) for x in [SELF,prep.SELF,prep.CORE,prep.RUNNER,prep.base.PREFLIGHT,prep.base.CONTEXT,Path(checked_expr.__code__.co_filename),Path(prep.core_cert.__file__)]},
        "max_file_seconds": max(x["data"]["seconds"] for x in records.values()),
        "validated": True, "Lean_started_by_consumer": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft",
    }


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--provider",choices=list(prep.CONFIGS),required=True)
    modes=parser.add_mutually_exclusive_group(required=True);modes.add_argument("--certify-existing",action="store_true");modes.add_argument("--check-only",action="store_true");args=parser.parse_args()
    result=validate(args.provider);target=prep.config(args.provider)["stage"]/"actual-provider-validation.json";raw=prep.encode(result)
    if target.exists():need(target.read_bytes()==raw,"Existing certificate differs; refusing overwrite")
    elif args.certify_existing:target.write_bytes(raw)
    else:need(False,"Check-only requires genuine existing full-CI certificate")
    print(json.dumps({"provider":args.provider,"certificate":prep.rel(target),
        "certificate_sha256":prep.sha(target) if target.exists() else None,
        "provided_names":result["provided_names"],"validated":result["validated"],
        "Std3_only":result["Std3_only"],"max_file_seconds":result["max_file_seconds"],
        "Lean_started_by_consumer":False,"API_used":False},ensure_ascii=False,indent=2))


if __name__=="__main__":main()
