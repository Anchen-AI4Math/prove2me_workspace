"""Check actual source-only context probe evidence; never authorize publication."""
import hashlib
import json
from pathlib import Path

from generate_independent_node import runtime_pin
from validate_independent_node import normalize_type
from validate_standalone_platform_node import audit_axioms

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
STAGE = TASK / "verification/context-restoration"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def main():
    manifest_path = STAGE / "probe-manifest.json"
    manifest = read(manifest_path)
    source = ROOT / manifest["output"]
    record_path = source.with_suffix(source.suffix + ".preflight.json")
    record = read(record_path)
    for field in ("success", "source_unchanged", "manifest_unchanged", "runtime_unchanged",
                  "dependencies_stable_during_compile", "input_certificates_stable",
                  "source_certificate_stable"):
        if record.get(field) is not True:
            raise ValueError("Scope probe preflight failed a certificate guard: " + field)
    if (record["exit_code"] != 0 or record["timed_out"]
            or not 0 < record["seconds"] <= record["timeout_seconds"] <= 300
            or record["actual_module_identity"] != "ContextScopeProbe"
            or record["source"] != source.relative_to(TASK).as_posix()
            or record["source_sha256_before"] != sha(source)
            or record["source_sha256_after"] != sha(source)
            or manifest["output_sha256"] != sha(source)
            or record["manifest_sha256_before"] != sha(manifest_path)
            or record["manifest_sha256_after"] != sha(manifest_path)
            or record["runtime_sha256"] != manifest["runtime_sha256"]
            or runtime_pin() != manifest["runtime_sha256"]):
        raise ValueError("Scope probe strict compilation lineage is not current")
    for relative, expected in manifest["input_hashes"].items():
        if sha(TASK / relative) != expected:
            raise ValueError("Frozen scope probe input changed: " + relative)
    for field in ("source", "original_source", "facts"):
        if sha(ROOT / manifest["origin"][field]) != manifest["origin"][field + "_sha256"]:
            raise ValueError("Original source/AST witness changed: " + field)
    if sha(TASK / "verification/TypedSnapshotCore.inc") != manifest["snapshot_core_sha256"]:
        raise ValueError("Scope probe kernel exporter changed")
    log = TASK / record["log"]
    if sha(log) != record["log_sha256"]:
        raise ValueError("Actual scope probe compiler log changed")
    rows = read(STAGE / "types.json")
    if (len(rows) != 2 or [row["name"] for row in rows] !=
            [manifest["original_declaration"], manifest["generated_declaration"]]):
        raise ValueError("Scope probe exported unexpected declaration names")
    if (len(rows[0]["levelParams"]) != len(rows[1]["levelParams"])
            or normalize_type(rows[0]) != normalize_type(rows[1])):
        raise ValueError("Scope restoration changed the original kernel type")
    axioms = audit_axioms(log, "scope_probe")
    validation = {"validated": True, "source_only_scope_probe": True,
                  "submission_ready": False, "usable_as_platform_dependency_certificate": False,
                  "kernel_types_equal": True, "standard_axioms_only": True,
                  "axioms": axioms, "original_declaration": rows[0]["name"],
                  "generated_declaration": rows[1]["name"], "seconds": record["seconds"],
                  "manifest_sha256": sha(manifest_path), "source_sha256": sha(source),
                  "preflight_sha256": sha(record_path), "log_sha256": sha(log),
                  "types_sha256": sha(STAGE / "types.json"),
                  "runtime_sha256": runtime_pin(),
                  "scope_restorer_sha256": sha(TASK / "scripts/restore_node_context.py"),
                  "limits": "One actual source-importing scope restoration test. Does not certify the other 311 contexts or replace platform import validation."}
    output = STAGE / "validation.json"
    output.write_bytes((json.dumps(validation, indent=2)+"\n").encode("utf-8"))
    print(json.dumps({key: validation[key] for key in
                      ("validated", "kernel_types_equal", "standard_axioms_only", "seconds", "submission_ready")}))


if __name__ == "__main__":
    main()
