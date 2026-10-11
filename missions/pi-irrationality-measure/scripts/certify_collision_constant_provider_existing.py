"""Strict read-only consumer for compiled ap7 collisionConstant provider evidence."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import stage_collision_constant_provider as prep
import validate_namespace_context_providers as context


TASK, STAGE = prep.TASK, prep.STAGE
CERT = STAGE / "actual-provider-validation.json"
SELF = Path(__file__).resolve()
STD3 = {"propext", "Classical.choice", "Quot.sound"}
ROW_FIELDS = {
    "schemaVersion", "kernelMetadataSchema", "sourceName", "resolvedName",
    "sourceModule", "declGraphSha256", "declGraphRowSha256", "graphKind",
    "envKind", "ownerKind", "ownerId", "commandUnit", "familyRoot",
    "levelParams", "closedType", "closedValue", "type", "value", "axioms",
    "kindMetadata", "familyReferences", "transitiveNames",
}


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def rows(path):
    result = [json.loads(line) for line in Path(path).read_text(encoding="utf-8").splitlines()
              if line.strip()]
    context.fail(len(result) != 2, "Expected exactly two full-CI snapshot rows")
    return result


def certify():
    prep.check_outputs(prep.stage_files())
    preparation = read(STAGE / "preparation.json")
    records = {}
    modes = ["emit-olean", "modecheck", "modecheck"]
    for index, (filename, mode) in enumerate(zip(preparation["order"][:3], modes), 1):
        source = STAGE / filename
        manifest = STAGE / f"c{index}.json"
        module = prep.PLATFORM_MODULE if index == 1 else Path(filename).stem
        record = context.record(source, manifest, mode, module, STAGE)
        data = record["data"]
        context.fail(data["exit_code"] != 0 or data["timed_out"] is not False
                     or data["seconds"] > 300, "Bounded compiler record did not pass: " + filename)
        records[filename] = record

    provider_record = records[prep.PROVIDER_FILE]["data"]
    expected_olean = TASK / preparation["expected_provider_olean"]
    context.fail(provider_record.get("emit_olean") is not True,
                 "Provider record did not emit an OLean")
    context.fail(Path(provider_record["output_olean"]).resolve() != expected_olean.resolve()
                 or provider_record.get("output_olean_sha256") != prep.sha(expected_olean),
                 "Provider OLean path/hash differs")
    for filename in ("SourceSnapshot.lean", "GeneratedSnapshot.lean"):
        data = records[filename]["data"]
        context.fail(data.get("emit_olean") is not False
                     or data.get("output_olean") is not None
                     or data.get("output_olean_sha256") is not None,
                     "Snapshot unexpectedly emitted an OLean: " + filename)

    source_rows = rows(STAGE / "source-full-ci.jsonl")
    generated_rows = rows(STAGE / "generated-full-ci.jsonl")
    context.fail([row.get("resolvedName") for row in source_rows] != prep.NAMES
                 or [row.get("resolvedName") for row in generated_rows] != prep.NAMES,
                 "Full-CI row order/domain differs")
    axioms = {}
    owners = {"source": {}, "generated": {}}
    for index, spec in enumerate(prep.UNIT_SPECS):
        source_row, generated_row = source_rows[index], generated_rows[index]
        for label, row, expected_module in (
                ("source", source_row, prep.SOURCE_MODULE),
                ("generated", generated_row, prep.PLATFORM_MODULE)):
            context.fail(set(row) != ROW_FIELDS or row["schemaVersion"] != 2
                         or row["kernelMetadataSchema"] != "lean-4.33.1-ConstantInfo-complete-v1"
                         or row["sourceName"] != spec["name"]
                         or row["resolvedName"] != spec["name"]
                         or row["sourceModule"] != expected_module
                         or row["declGraphSha256"] != prep.DECL_GRAPH_SHA256
                         or row["declGraphRowSha256"] != spec["row_sha256"]
                         or row["graphKind"] != spec["kind"] or row["envKind"] != spec["kind"]
                         or row["ownerKind"] != spec["owner_kind"]
                         or row["ownerId"] != spec["command_unit"]
                         or row["commandUnit"] != spec["command_unit"]
                         or row["familyRoot"] != spec["name"]
                         or row["closedType"] is not True
                         or row["levelParams"] != sorted(set(row["levelParams"]))
                         or not set(row["axioms"]) <= STD3,
                         "Full-CI schema/provenance/closure differs: " + label + ":" + spec["name"])
            owners[label][spec["name"]] = expected_module
            axioms[label + ":" + spec["name"]] = row["axioms"]
        context.fail(source_row["type"] != generated_row["type"],
                     "Source/generated type differs: " + spec["name"])
        context.fail(source_row["axioms"] != generated_row["axioms"],
                     "Source/generated axioms differ: " + spec["name"])
        if spec["kind"] == "def":
            context.fail(source_row["closedValue"] is not True
                         or generated_row["closedValue"] is not True
                         or source_row["value"] is None
                         or source_row["value"] != generated_row["value"]
                         or source_row["kindMetadata"].get("valueExported") is not True
                         or generated_row["kindMetadata"].get("valueExported") is not True,
                         "Definition value was not exported exactly")
        else:
            context.fail(source_row["closedValue"] is not None
                         or generated_row["closedValue"] is not None
                         or source_row["value"] is not None or generated_row["value"] is not None
                         or source_row["kindMetadata"] != {"proofValueExported": False}
                         or generated_row["kindMetadata"] != {"proofValueExported": False},
                         "Theorem snapshot must expose type/axioms and a null proof value")

    output_paths = [STAGE / "source-full-ci.jsonl", STAGE / "generated-full-ci.jsonl"]
    report = {
        "schema_version": 1,
        "artifact_kind": "ap7-collision-constant-actual-provider-validation",
        "source_commit": prep.COMMIT,
        "source_module": prep.SOURCE_MODULE,
        "platform_module": prep.PLATFORM_MODULE,
        "provided_names": prep.NAMES,
        "provider_source_sha256": prep.sha(STAGE / prep.PROVIDER_FILE),
        "provider_olean": prep.task_rel(expected_olean),
        "provider_olean_sha256": prep.sha(expected_olean),
        "preparation_sha256": prep.sha(STAGE / "preparation.json"),
        "compiler_manifest_sha256": {f"c{i}.json": prep.sha(STAGE / f"c{i}.json")
                                      for i in range(1, 4)},
        "preflights": records,
        "source_and_generated_types_equal": True,
        "definition_values_equal_and_exported": True,
        "theorem_values_null": True,
        "actual_owners": owners,
        "axioms": axioms,
        "Std3_only": True,
        "output_json_sha256": {prep.task_rel(path): prep.sha(path) for path in output_paths},
        "implementation_hashes": {
            prep.task_rel(prep.PRODUCER): prep.sha(prep.PRODUCER),
            prep.task_rel(SELF): prep.sha(SELF),
            prep.task_rel(Path(context.__file__)): prep.sha(Path(context.__file__)),
            prep.task_rel(prep.PREFLIGHT): prep.sha(prep.PREFLIGHT),
            prep.task_rel(prep.CORE): prep.sha(prep.CORE),
        },
        "max_file_seconds": max(row["data"]["seconds"] for row in records.values()),
        "validated": True,
        "Lean_started_by_consumer": False,
        "API_used": False,
        "submission_ready": False,
        "proposal_status": "Draft",
    }
    raw = prep.encode(report)
    if CERT.exists() and CERT.read_bytes() != raw:
        raise ValueError("Existing collisionConstant certificate differs; refusing overwrite")
    if not CERT.exists():
        CERT.write_bytes(raw)
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certify-existing", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(certify(), ensure_ascii=False, indent=2))
