"""Compile exact staged bytes and compare their kernel types against the pinned source."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from generate_independent_node import check_stage_inputs

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize_type(row):
    parameters = {name: index for index, name in enumerate(row["levelParams"])}
    def normalize(value):
        if not isinstance(value, list):
            return value
        if len(value) == 2 and value[0] == "param":
            return ["param", parameters[value[1]]]
        return [normalize(item) for item in value]
    return normalize(row["type"])


def main():
    stage = (DEST / "independent" / sys.argv[1]).resolve()
    if not stage.is_relative_to((DEST / "independent").resolve()):
        raise SystemExit("Stage path escapes the task")
    manifest_path = stage / "manifest.json"
    manifest = read(manifest_path)
    check_stage_inputs(stage, manifest)
    records = {}
    filenames = [Path(manifest["statement"]).name, Path(manifest["solution"]).name,
                 "SnapshotOriginal.lean", "SnapshotGenerated.lean"]
    for filename in filenames:
        relative = (stage / filename).relative_to(DEST).as_posix()
        result = subprocess.run([sys.executable, str(TASK / "scripts/preflight_logged.py"),
                                 "--verification", relative], cwd=ROOT)
        record = read(DEST / "latest-preflight.json")
        records[filename] = record
        (stage / (filename + ".preflight.json")).write_text(
            json.dumps(record, indent=2) + "\n", encoding="utf-8")
        if (result.returncode or record["exit_code"] or record["timed_out"]
                or not record["source_unchanged"] or not 0 < record["seconds"] <= 300
                or not 0 < record["timeout_seconds"] <= 300
                or record["runtime_sha256"] != manifest["runtime_sha256"]
                or ROOT / record["source"] != stage / filename
                or record["source_sha256"] != digest(stage / filename)):
            raise SystemExit("Stage did not pass strict 300-second compilation")
        record["log_sha256"] = digest(ROOT / record["log"])
    check_stage_inputs(stage, manifest)
    solution_record = records[Path(manifest["solution"]).name]
    audit = "'solution' depends on axioms: [propext, Classical.choice, Quot.sound]"
    if audit not in (ROOT / solution_record["log"]).read_text(encoding="utf-8"):
        raise ValueError("The exact upload proof has no clean standard-axiom audit")
    original = read(stage / "original-type.json")
    generated = read(stage / "generated-type.json")
    if (len(original) != 1 or original[0]["name"] != manifest["theorem_name"]
            or {row["name"] for row in generated} != {manifest["theorem_name"], "solution"}):
        raise ValueError("Type snapshots contain unexpected declarations")
    expected = normalize_type(original[0])
    for row in generated:
        if len(row["levelParams"]) != len(original[0]["levelParams"]) or normalize_type(row) != expected:
            raise ValueError("The statement or proof changed the source theorem's kernel type")
    validation = {"at_utc": datetime.now(timezone.utc).isoformat(), "validated": True,
                  "standard_axioms_only": True, "kernel_types_equal": True,
                  "only_universe_parameter_display_names_normalized": True,
                  "original_type_sha256": digest(stage / "original-type.json"),
                  "generated_type_sha256": digest(stage / "generated-type.json"),
                  "preflights": records,
                  "runtime_sha256": manifest["runtime_sha256"],
                  "statement_sha256": manifest["statement_sha256"],
                  "solution_sha256": manifest["solution_sha256"],
                  "snapshot_sha256": manifest["snapshot_sha256"],
                  "source_graph_sha256": manifest["source_graph_sha256"],
                  "facts_sha256": manifest["facts_sha256"],
                  "pretty_types": {"source": original[0]["prettyType"],
                                   **{row["name"]: row["prettyType"] for row in generated}}}
    validation_path = stage / "validation.json"
    validation_path.write_text(json.dumps(validation, indent=2) + "\n", encoding="utf-8")
    manifest.update({"validated": True, "pending": [],
                     "validation": validation_path.relative_to(ROOT).as_posix(),
                     "validation_sha256": digest(validation_path)})
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"theorem_name": manifest["theorem_name"], "validated": True,
                      "kernel_types_equal": True, "standard_axioms_only": True,
                      "max_file_seconds": max(record["seconds"] for record in records.values())}))


if __name__ == "__main__":
    main()
