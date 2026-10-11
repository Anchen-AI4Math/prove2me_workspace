"""Validate exact closed, unrenamed ordinary-def bundles before broader DAG work."""
from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_inputs(manifest):
    for relative, expected in manifest["input_hashes"].items():
        if sha(TASK / relative) != expected:
            raise ValueError("Generation input changed: " + relative)
    for key in ["source", "original_source", "facts", "output"]:
        if sha(ROOT / manifest[key]) != manifest[key + "_sha256"]:
            raise ValueError("Bundle input/output changed: " + key)


def normalize(row, key):
    levels = {name: index for index, name in enumerate(row["levelParams"])}
    def walk(value):
        if not isinstance(value, list):
            return value
        if len(value) == 2 and value[0] == "param":
            return ["param", levels[value[1]]]
        return [walk(item) for item in value]
    return walk(row[key])


def axioms_from(log, names):
    results = {}
    text = log.read_text(encoding="utf-8")
    for name in names:
        prefix = "'" + name + "' depends on axioms: ["
        matches = re.findall(r"^" + re.escape(prefix) + r"([^\]]*)\]\s*$", text, flags=re.MULTILINE)
        empty = "'" + name + "' does not depend on any axioms"
        if sum(empty in line for line in text.splitlines()) == 1 and not matches:
            results[name] = []
            continue
        if len(matches) != 1:
            raise ValueError("Missing unique axiom audit for " + name)
        axioms = set()
        for item in matches[0].split(","):
            if not item.strip():
                continue
            match = re.fullmatch(r"(propext|Classical\.choice|Quot\.sound)(?:\.\{[^{}]*\})?", item.strip())
            if match is None:
                raise ValueError("Unexpected axiom display in " + name + ": " + item.strip())
            axioms.add(match.group(1))
        results[name] = sorted(axioms)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", help="Bundle path relative to verification")
    parser.add_argument("--certify-existing", action="store_true",
                        help="Recheck exact successful compiler certificates without repeating compilation")
    args = parser.parse_args()
    source = (DEST / args.source).resolve()
    if not source.is_relative_to((DEST / "bundles-preview/Definitions").resolve()) or not source.is_file():
        raise ValueError("Expected an existing preview Definition within this task")
    manifest_path = source.with_suffix(".manifest.json")
    manifest = read(manifest_path)
    check_inputs(manifest)
    if manifest["renames"] or manifest["kept_local_instances"] or manifest["elaboration_only_helpers"]:
        raise ValueError("This validator covers closed ordinary defs without renames or helpers")
    if any(name.startswith(("OAI.", "Definitions.", "Theorems.", "Solutions.")) for name in manifest["imports"]):
        raise ValueError("A closed bundle cannot import project or platform dependencies")
    units = {unit["id"]: unit for unit in read(DEST / "platform-unit-plan-preview.json")["units"]}
    graph = {row["name"]: row for row in (json.loads(line) for line in (DEST / "decl_graph.jsonl").read_bytes().splitlines())}
    names = []
    for key in manifest["selected_units"]:
        unit = units[key]
        if unit["is_instance_command"] or unit["deprivate"] or len(unit["graph_names"]) != 1:
            raise ValueError("Unsupported definition command")
        name = unit["graph_names"][0]
        row = graph[name]
        if row["kind"] not in {"def", "definition", "abbrev"} or row["isPrivate"] or row["isInstance"]:
            raise ValueError("Expected one ordinary nonprivate definition")
        if any(dep in graph and dep not in [n for k in manifest["selected_units"] for n in units[k]["graph_names"]]
               for dep in row["typeDeps"] + row["valueDeps"]):
            raise ValueError("Definition has an omitted project dependency")
        names.append(name)
    stage = DEST / "definition-validation" / source.stem
    stage.mkdir(parents=True, exist_ok=True)
    core_path = DEST / "TypedSnapshotCore.inc"
    core = core_path.read_text(encoding="utf-8")
    core_sha = sha(core_path)
    tail = "\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\nrun_meta do\n"
    certificates = []
    for variant, module in [("Original", manifest["source_module"]), ("Generated", manifest["platform_module"])]:
        output = (stage / (variant.lower() + "-definitions.json")).relative_to(ROOT).as_posix()
        body = "import Lean\nimport " + module + "\n\n" + core + tail
        body += "  PiExponentInterfaceSnapshot.exportSnapshot #[" + ", ".join("`" + name for name in names) + "] " + json.dumps(output) + "\n"
        body += "".join("#print axioms " + name + "\n" for name in names)
        path = stage / ("Snapshot" + variant + ".lean")
        path.write_bytes(body.encode("utf-8"))
        snapshot_manifest = {
            "output": path.relative_to(ROOT).as_posix(), "output_sha256": sha(path),
            "source": manifest["source"], "source_sha256": manifest["source_sha256"],
            "original_source": manifest["original_source"], "original_source_sha256": manifest["original_source_sha256"],
            "imports": ["Lean", module], "runtime_sha256": sha(DEST / "lean-runtime.json"),
            "input_hashes": dict(manifest["input_hashes"]) | {
                manifest_path.relative_to(TASK).as_posix(): sha(manifest_path),
                source.relative_to(TASK).as_posix(): sha(source),
                core_path.relative_to(TASK).as_posix(): core_sha}}
        path.with_suffix(".manifest.json").write_text(json.dumps(snapshot_manifest, indent=2) + "\n", encoding="utf-8")
        if not args.certify_existing:
            (stage / (variant.lower() + "-definitions.json")).unlink(missing_ok=True)
    runner = TASK / "scripts/preflight_staged_module.py"
    commands = [(source, "bundles-preview", True), (stage / "SnapshotOriginal.lean", stage.relative_to(DEST).as_posix(), False),
                (stage / "SnapshotGenerated.lean", stage.relative_to(DEST).as_posix(), False)]
    for path, root, emit in commands:
        command = [sys.executable, str(runner), path.relative_to(DEST).as_posix(), "--root", root]
        if emit:
            command.append("--emit-olean")
        result = subprocess.run(command, cwd=TASK) if not args.certify_existing else None
        record = read(path.with_suffix(path.suffix + ".preflight.json"))
        if ((result is not None and result.returncode) or not record["success"]
                or record["exit_code"] or record["timed_out"] or not record["source_unchanged"]
                or not 0 < record["seconds"] <= record["timeout_seconds"] <= 300
                or record["runtime_sha256"] != sha(DEST / "lean-runtime.json")
                or TASK / record["source"] != path):
            raise ValueError("Bundle validation failed strict compilation")
        if (sha(path) != record["source_sha256_before"] or sha(path) != record["source_sha256_after"]
                or sha(TASK / record["log"]) != record["log_sha256"]
                or not record["input_certificates_stable"]):
            raise ValueError("Staged compiler evidence changed")
        cert_manifest = TASK / record["manifest"]
        if sha(cert_manifest) != record["manifest_sha256_before"] or record["manifest_sha256_before"] != record["manifest_sha256_after"]:
            raise ValueError("Compiler source manifest changed")
        for relative, evidence in record["manifest_input_hashes_before"].items():
            if sha(TASK / relative) != evidence["actual_sha256"] or not evidence["matches"]:
                raise ValueError("Compiler input changed: " + relative)
        for dependency in record["dependency_oleans"]:
            if sha(Path(dependency["path"])) != dependency["sha256_before"] or not dependency["stable_during_compile"]:
                raise ValueError("Compiled import changed")
        if emit and (record["actual_module_identity"] != manifest["platform_module"]
                     or sha(TASK / record["output_olean"]) != record["output_olean_sha256"]):
            raise ValueError("Definition module artifact changed")
        certificates.append(record)
    check_inputs(manifest)
    if sha(core_path) != core_sha:
        raise ValueError("Snapshot core changed")
    original, generated = read(stage / "original-definitions.json"), read(stage / "generated-definitions.json")
    if [row["name"] for row in original] != names or [row["name"] for row in generated] != names:
        raise ValueError("Unexpected definition snapshots")
    for left, right in zip(original, generated):
        if len(left["levelParams"]) != len(right["levelParams"]) or any(normalize(left, key) != normalize(right, key) for key in ["type", "value"]):
            raise ValueError("Definition kernel type/value changed: " + left["name"])
    audits = {variant: axioms_from(TASK / record["log"], names) for variant, record in zip(["source", "generated"], certificates[1:])}
    validation = {"at_utc": datetime.now(timezone.utc).isoformat(), "validated": True,
                  "scope": "closed ordinary unrenamed definitions only", "kernel_types_and_values_equal": True,
                  "standard_axioms_only": True, "axioms": audits, "provided_names": names,
                  "source_manifest_sha256": sha(manifest_path), "output_sha256": sha(source),
                  "snapshot_core_sha256": core_sha, "snapshots": {path.name: sha(path) for path in stage.glob("Snapshot*.lean")},
                  "type_value_snapshots": {path.name: sha(path) for path in stage.glob("*-definitions.json")},
                  "preflights": certificates, "submission_ready": False}
    (stage / "validation.json").write_text(json.dumps(validation, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"validated": True, "bundle": manifest["platform_module"], "provided_names": names,
                      "max_file_seconds": max(record["seconds"] for record in certificates)}))


if __name__ == "__main__":
    main()
