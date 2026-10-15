"""Strict, read-only replay of the AP14 RowTranslation data provider's three compiled witnesses."""
from __future__ import annotations

import argparse
from datetime import datetime
import json
from pathlib import Path

import stage_row_translation_data_provider as prep
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


def validate(key):
    prep.check_only(key)
    c = prep.config(key); stage = c["stage"]
    p = prep.read(stage / "preparation.json")
    need(p["validated"] is False and p["submission_ready"] is False and p["proposal_status"] == "Draft",
         "Preparation stage flags differ")
    units = prep.authority(c)
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
        records[filename] = record
    emitted = records[c["provider_file"]]["data"]
    expected = prep.TASK / p["expected_provider_olean"]
    need(emitted["output_olean"] == prep.rel(expected)
         and emitted["output_olean_sha256"] == prep.sha(expected), "Provider OLean path/hash differs")
    for filename in [prep.SOURCE_SNAPSHOT, prep.GENERATED_SNAPSHOT]:
        need(records[filename]["data"]["output_olean"] is None
             and records[filename]["data"]["output_olean_sha256"] is None, "Snapshot emitted an OLean")
    source_rows = rows(stage / prep.SOURCE_JSON, records[prep.SOURCE_SNAPSHOT], len(units))
    generated_rows = rows(stage / prep.GENERATED_JSON, records[prep.GENERATED_SNAPSHOT], len(units))
    axioms = {}; owners = {"source": {}, "generated": {}}
    for unit, left, right in zip(units, source_rows, generated_rows, strict=True):
        owner = unit["owner"]; name = unit["name"]
        for side, row, module in [("source", left, c["source_module"]), ("generated", right, c["platform_module"])]:
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
        need(left["levelParams"] == right["levelParams"] and left["type"] == right["type"]
             and left["value"] == right["value"] and left["axioms"] == right["axioms"],
             "Source/generated kernel type, complete value or Std3 differs: " + name)
    return {
        "schema_version": 1, "artifact_kind": "ap14-row-translation-data-actual-provider-validation",
        "source_commit": prep.COMMIT, "source_module": c["source_module"],
        "platform_module": c["platform_module"], "provided_names": c["names"],
        "provider_source_sha256": prep.sha(stage / c["provider_file"]),
        "provider_olean": prep.rel(expected), "provider_olean_sha256": prep.sha(expected),
        "preparation_sha256": prep.sha(stage / "preparation.json"),
        "compiler_manifest_sha256": {f"c{i}.json":prep.sha(stage/f"c{i}.json") for i in range(1,4)},
        "preflights": records, "source_and_generated_types_equal": True,
        "definition_values_equal_and_exported": True, "contains_theorems": False,
        "actual_owners": owners, "axioms": axioms, "Std3_only": True,
        "output_json_sha256": {prep.rel(stage/x):prep.sha(stage/x) for x in [prep.SOURCE_JSON,prep.GENERATED_JSON]},
        "implementation_hashes": {prep.rel(x):prep.sha(x) for x in [SELF,prep.SELF,prep.CORE,prep.ap9.PREFLIGHT,prep.ap9.CONTEXT,Path(checked_expr.__code__.co_filename)]},
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
    print(json.dumps({"provider":args.provider,"certificate":prep.rel(target),
        "certificate_sha256":prep.sha(target) if target.exists() else None,
        "provided_names":result["provided_names"],"validated":result["validated"],
        "Std3_only":result["Std3_only"],"max_file_seconds":result["max_file_seconds"],
        "Lean_started_by_consumer":False,"API_used":False},ensure_ascii=False,indent=2))


if __name__=="__main__":main()
