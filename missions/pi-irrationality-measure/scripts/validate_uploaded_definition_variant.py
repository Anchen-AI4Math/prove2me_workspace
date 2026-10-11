"""Prepare and optionally validate the exact bytes served for a Definition.

This supplements, and never replaces, the original closed-bundle validation.
The default mode creates immutable uploaded-source inputs only.  --run-preflights
asks the staged runner to typecheck the exact uploaded bytes and a snapshot
module that exports their kernel type/value rows and standard-axiom audit.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
VERIFICATION = TASK / "verification"
STEM = "Def_OAI_NumberTheory_PiExponent_Analysis_Collision"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    return digest(path.read_bytes())


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path, value):
    path.write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))


def write_json_immutable(path, value):
    data = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    if path.exists():
        if path.read_bytes() != data:
            raise ValueError("Existing uploaded-variant manifest differs; refusing to rewrite it")
    else:
        path.write_bytes(data)


def task_file(relative):
    result = (TASK / relative).resolve()
    if not result.is_relative_to(TASK.resolve()):
        raise ValueError("Certificate path escapes mission")
    return result


def root_file(relative):
    result = (ROOT / relative).resolve()
    if not result.is_relative_to(ROOT.resolve()):
        raise ValueError("Lineage path escapes workspace")
    return result


def normalize(row, key):
    levels = {name: index for index, name in enumerate(row["levelParams"])}

    def walk(value):
        if not isinstance(value, list):
            return value
        if len(value) == 2 and value[0] == "param":
            if value[1] not in levels:
                raise ValueError("Snapshot contains unknown universe level")
            return ["param", levels[value[1]]]
        return [walk(item) for item in value]

    return walk(row[key])


def output(root_relative, output_path):
    if not output_path.resolve().is_relative_to(TASK.resolve()):
        raise ValueError("Output escapes mission")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(root_relative)


def prepare():
    stage = VERIFICATION / "definition-validation" / STEM
    uploaded_dir = stage / "uploaded"
    payload_path = stage / "publish-payload.json"
    publication_path = stage / "publication.json"
    prep_path = stage / "prepare-record.json"
    bundle = VERIFICATION / "bundles-preview/Definitions" / (STEM + ".lean")
    bundle_manifest_path = bundle.with_suffix(".manifest.json")
    validation_path = stage / "validation.json"
    original_json = stage / "original-definitions.json"
    core_path = VERIFICATION / "TypedSnapshotCore.inc"

    if not all(path.is_file() for path in (payload_path, publication_path, prep_path, bundle,
                                            bundle_manifest_path, validation_path, original_json, core_path)):
        raise ValueError("A required frozen publication or validation input is missing")
    payload_bytes = payload_path.read_bytes()
    payload = json.loads(payload_bytes.decode("utf-8"))
    publication = read_json(publication_path)
    prepared = read_json(prep_path)
    bundle_manifest = read_json(bundle_manifest_path)
    prior_validation = read_json(validation_path)
    original_rows = read_json(original_json)
    code_text = payload.get("definition")
    if not isinstance(code_text, str):
        raise ValueError("Frozen payload has no exact definition source string")
    code_bytes = code_text.encode("utf-8")
    if (digest(payload_bytes) != prepared.get("payload_sha256")
            or digest(payload_bytes) != publication.get("publish_payload_sha256")
            or payload != publication.get("publish_intent", {}).get("payload")
            or digest(code_bytes) != prepared.get("uploaded_definition_sha256", digest(code_bytes))):
        raise ValueError("Frozen payload, preparation, or publication intent hashes disagree")
    if (payload.get("definition_name") != STEM[len("Def_"):]
            or payload.get("env") != ENV or payload.get("private") is not False
            or bundle_manifest.get("platform_module") != "Definitions." + STEM
            or bundle_manifest.get("output_sha256") != file_sha(bundle)
            or prior_validation.get("validated") is not True
            or prior_validation.get("kernel_types_and_values_equal") is not True):
        raise ValueError("Frozen target identity or original validation is not exact")
    response = publication.get("publish_response", {})
    verdict = publication.get("last_publish_verdict", {})
    readback = publication.get("target_readback", {})
    readback_body = readback.get("body", {})
    definition_id = publication.get("definition_id")
    if (response.get("http_status") != 202 or publication.get("job_id") != response.get("body", {}).get("job_id")
            or verdict.get("body", {}).get("status") != "PUBLISHED"
            or readback.get("http_status") != 200 or not definition_id
            or readback_body.get("theorem_id") != definition_id
            or readback_body.get("theorem_name") != payload["definition_name"]
            or readback_body.get("status") != "Definition"
            or readback_body.get("mathlib_rev") != ENV
            or readback_body.get("visibility") != "public"
            or readback_body.get("definition") != code_text):
        raise ValueError("Stored published job or exact server Definition readback is incomplete")

    names = prior_validation.get("provided_names")
    if (not isinstance(names, list) or not names or len(names) != len(set(names))
            or [row.get("name") for row in original_rows] != names):
        raise ValueError("Original kernel snapshot does not match its validated declaration order")
    if prior_validation.get("type_value_snapshots", {}).get("original-definitions.json") != file_sha(original_json):
        raise ValueError("Original source type/value rows changed after validation")
    imports = bundle_manifest.get("imports")
    if not isinstance(imports, list) or not imports:
        raise ValueError("The exact original import certificate is missing")

    # Freeze uploaded bytes under a new path.  Never rewrite the already-published
    # payload, original snapshots, original OLean, metadata, or publication log.
    uploaded_source = uploaded_dir / "Definitions" / (STEM + ".lean")
    snapshot_path = uploaded_dir / "SnapshotUploaded.lean"
    result_path = stage / "uploaded-definitions.json"
    if uploaded_dir.exists():
        if not uploaded_source.is_file() or uploaded_source.read_bytes() != code_bytes:
            raise ValueError("Uploaded variant directory already exists with different bytes")
        if not snapshot_path.is_file():
            raise ValueError("Uploaded variant directory is incomplete")
    else:
        output(code_bytes, uploaded_source)

    # Lean's source snapshot code is composed from exact certified imports,
    # the exact server code bytes, and the unchanged shared snapshot core.
    core = core_path.read_bytes()
    snapshot_body = b"import Lean\n" + code_bytes
    if not snapshot_body.endswith(b"\n"):
        snapshot_body += b"\n"
    snapshot_body += b"\n" + core
    snapshot_body += ("\nset_option pp.universes true\nset_option pp.fullNames true\n"
                      "set_option pp.explicit true\nrun_meta do\n").encode("utf-8")
    snapshot_body += ("  PiExponentInterfaceSnapshot.exportSnapshot #[" +
                      ", ".join("`" + name for name in names) + "] " +
                      json.dumps(result_path.relative_to(ROOT).as_posix()) + "\n").encode("utf-8")
    snapshot_body += "".join("#print axioms " + name + "\n" for name in names).encode("utf-8")
    if snapshot_path.exists():
        if snapshot_path.read_bytes() != snapshot_body:
            raise ValueError("Existing SnapshotUploaded source differs; refusing to overwrite it")
    else:
        output(snapshot_body, snapshot_path)

    relative_payload = payload_path.relative_to(TASK).as_posix()
    relative_publication = publication_path.relative_to(TASK).as_posix()
    relative_prepare = prep_path.relative_to(TASK).as_posix()
    relative_validation = validation_path.relative_to(TASK).as_posix()
    relative_original = original_json.relative_to(TASK).as_posix()
    relative_core = core_path.relative_to(TASK).as_posix()
    relative_manifest = bundle_manifest_path.relative_to(TASK).as_posix()
    input_hashes = {
        relative_payload: digest(payload_bytes),
        relative_publication: file_sha(publication_path),
        relative_prepare: file_sha(prep_path),
        relative_validation: file_sha(validation_path),
        relative_original: file_sha(original_json),
        relative_core: file_sha(core_path),
        relative_manifest: file_sha(bundle_manifest_path),
        uploaded_source.relative_to(TASK).as_posix(): digest(code_bytes),
    }
    source_manifest = {
        "schema_version": 1,
        "output": uploaded_source.relative_to(ROOT).as_posix(),
        "output_sha256": digest(code_bytes),
        "source": bundle_manifest["source"],
        "source_sha256": bundle_manifest["source_sha256"],
        "original_source": bundle_manifest["original_source"],
        "original_source_sha256": bundle_manifest["original_source_sha256"],
        "imports": imports,
        "input_hashes": input_hashes,
        "definition_id": definition_id,
        "published_payload_sha256": digest(payload_bytes),
        "server_definition_sha256": digest(code_bytes),
    }
    snapshot_manifest = {
        "schema_version": 1,
        "output": snapshot_path.relative_to(ROOT).as_posix(),
        "output_sha256": digest(snapshot_body),
        "source": bundle_manifest["source"],
        "source_sha256": bundle_manifest["source_sha256"],
        "original_source": bundle_manifest["original_source"],
        "original_source_sha256": bundle_manifest["original_source_sha256"],
        "imports": ["Lean", *imports],
        "input_hashes": input_hashes,
        "definition_id": definition_id,
        "published_payload_sha256": digest(payload_bytes),
        "server_definition_sha256": digest(code_bytes),
    }
    write_json_immutable(uploaded_source.with_suffix(".manifest.json"), source_manifest)
    write_json_immutable(snapshot_path.with_suffix(".manifest.json"), snapshot_manifest)
    return {
        "stage": stage,
        "source": uploaded_source,
        "snapshot": snapshot_path,
        "output_json": result_path,
        "payload": payload,
        "payload_sha256": digest(payload_bytes),
        "definition_sha256": digest(code_bytes),
        "names": names,
        "input_hashes": input_hashes,
        "source_manifest": source_manifest,
        "snapshot_manifest": snapshot_manifest,
        "prior_validation": prior_validation,
        "original_rows": original_rows,
        "readback": readback_body,
        "publication_sha256": file_sha(publication_path),
        "original_rows_sha256": file_sha(original_json),
        "core_sha256": file_sha(core_path),
    }


def preflight_one(source, root, should_emit=False):
    runner = TASK / "scripts/preflight_staged_module.py"
    command = [sys.executable, str(runner), source.relative_to(VERIFICATION).as_posix(),
               "--root", root]
    if should_emit:
        command.append("--emit-olean")
    result = subprocess.run(command, cwd=TASK, timeout=310)
    record = read_json(source.with_suffix(source.suffix + ".preflight.json"))
    if (result.returncode != 0 or record.get("mode") != "modecheck"
            or record.get("exit_code") != 0 or record.get("timed_out") is not False
            or record.get("success") is not True or record.get("source_unchanged") is not True
            or not 0 < record.get("timeout_seconds", 0) <= 300
            or not 0 < record.get("seconds", 0) <= 300
            or not record.get("input_certificates_stable")
            or not record.get("runtime_unchanged")
            or not record.get("dependencies_stable_during_compile")
            or record.get("log_sha256") != file_sha(task_file(record["log"]))):
        raise ValueError("Uploaded-definition preflight failed or exceeded 300 seconds")
    return record


def shared_audit_axioms(log_path, name):
    """Use the campaign's established strict universe-aware axiom parser."""
    if str(TASK / "scripts") not in sys.path:
        sys.path.insert(0, str(TASK / "scripts"))
    path = TASK / "scripts/validate_standalone_platform_node.py"
    spec = importlib.util.spec_from_file_location("campaign_standalone_validator", path)
    if spec is None or spec.loader is None:
        raise ValueError("Could not load the established standalone axiom auditor")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.audit_axioms(log_path, name)


def staged_helpers():
    if str(TASK / "scripts") not in sys.path:
        sys.path.insert(0, str(TASK / "scripts"))
    path = TASK / "scripts/preflight_staged_module.py"
    spec = importlib.util.spec_from_file_location("campaign_staged_preflight", path)
    if spec is None or spec.loader is None:
        raise ValueError("Could not load the staged preflight certificate helpers")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def certify_preflight_record(data, source, manifest, sidecar, expected_module):
    helpers = staged_helpers()
    record = read_json(sidecar)
    manifest_path = source.with_suffix(".manifest.json")
    relative_source = source.relative_to(TASK).as_posix()
    relative_manifest = manifest_path.relative_to(TASK).as_posix()
    runtime_path = VERIFICATION / "lean-runtime.json"
    runtime = read_json(runtime_path)
    runtime_sha = file_sha(runtime_path)
    log_path = task_file(record.get("log", ""))
    log_root = VERIFICATION / "staged-preflight-logs"
    dependencies = record.get("dependency_oleans")
    pins = record.get("runtime_project_pins")
    pins_after = record.get("runtime_project_pins_after")
    current_manifest_inputs = helpers.verify_manifest_inputs(manifest)
    current_source_certificate = helpers.verify_source_certificate(source, manifest)
    current_imports = helpers.certified_imports(source, manifest)

    if (record.get("mode") != "modecheck" or record.get("success") is not True
            or record.get("exit_code") != 0 or record.get("timed_out") is not False
            or record.get("source_unchanged") is not True
            or record.get("source") != relative_source
            or record.get("actual_module_identity") != expected_module):
        raise ValueError("Uploaded preflight identity or compiler status differs")
    module_root = source.parent.parent if source == data["source"] else source.parent
    expected_root = (Path("verification") / module_root.relative_to(VERIFICATION)).as_posix()
    if record.get("module_root") != expected_root:
        raise ValueError("Uploaded preflight used an unexpected -R module root")
    if (record.get("manifest") != relative_manifest
            or record.get("manifest_sha256_before") != file_sha(manifest_path)
            or record.get("manifest_sha256_after") != file_sha(manifest_path)
            or record.get("manifest_unchanged") is not True
            or record.get("source_sha256_before") != file_sha(source)
            or record.get("source_sha256_after") != file_sha(source)
            or record.get("source_certificate") != current_source_certificate
            or record.get("source_certificate_after") != current_source_certificate
            or record.get("source_certificate_stable") is not True
            or record.get("imports") != current_imports):
        raise ValueError("Uploaded source, manifest, lineage, or exact-import certificate is stale")
    before_inputs = record.get("manifest_input_hashes_before")
    after_inputs = record.get("manifest_input_hashes_after")
    if before_inputs != current_manifest_inputs or after_inputs != current_manifest_inputs:
        raise ValueError("Uploaded compiler input hashes differ from their current exact inputs")

    if (record.get("runtime_path") != runtime_path.relative_to(TASK).as_posix()
            or record.get("runtime_sha256") != runtime_sha
            or record.get("runtime_sha256_after") != runtime_sha
            or record.get("runtime_unchanged") is not True
            or record.get("captured_environment") != runtime.get("environment")
            or record.get("lean_executable") != runtime.get("executable")
            or record.get("lean_executable_sha256") != runtime.get("executable_sha256")
            or record.get("lean_executable_sha256_after") != runtime.get("executable_sha256")
            or record.get("effective_lean_path") !=
            [str(path) for path in helpers.effective_search_path(runtime["environment"]["LEAN_PATH"])]
            or record.get("timeout_seconds") != 300.0
            or not isinstance(record.get("seconds"), (int, float))
            or not 0 < record["seconds"] <= 300
            or record.get("output_olean") is not None):
        raise ValueError("Uploaded preflight runtime, timeout, or modecheck output differs")
    command = record.get("command", [])
    if ("-o" in command or not command or command[0] != runtime.get("executable")
            or command[-1] != str(source.resolve())):
        raise ValueError("Existing actual compiler command differs from the recorded exact source")
    executable = Path(runtime["executable"])
    if not executable.is_file() or file_sha(executable) != runtime["executable_sha256"]:
        raise ValueError("Pinned Lean executable changed after the captured preflight")

    expected_pins = runtime.get("project_hashes", {})
    if not isinstance(pins, dict) or set(pins) != set(expected_pins) or pins_after != pins:
        raise ValueError("Runtime project pins are missing or changed")
    for name, expected in expected_pins.items():
        project_file = root_file(name)
        row = pins[name]
        if (not project_file.is_file() or file_sha(project_file) != expected
                or row.get("expected_sha256") != expected
                or row.get("actual_sha256") != expected or row.get("matches") is not True):
            raise ValueError("Pinned Lean project configuration changed: " + name)

    if not isinstance(dependencies, list) or not dependencies:
        raise ValueError("Preflight has no imported OLean dependency certificates")
    if record.get("dependencies_stable_during_compile") is not True:
        raise ValueError("Imported OLean dependencies were not stable during compilation")
    for dependency in dependencies:
        dep_path = Path(dependency["path"])
        if (not dep_path.is_file()
                or dependency.get("sha256_before") != dependency.get("sha256_after")
                or dependency.get("sha256_after") != file_sha(dep_path)
                or dependency.get("stable_during_compile") is not True):
            raise ValueError("Imported OLean changed after its recorded preflight: " + dependency.get("module", "?"))

    if (not log_path.is_file() or not log_path.resolve().is_relative_to(log_root.resolve())
            or record.get("log_sha256") != file_sha(log_path)
            or record.get("stdout_and_stderr_sha256") != record.get("log_sha256")):
        raise ValueError("Captured compiler log is absent or changed")
    return record


def certify_existing():
    stage = VERIFICATION / "definition-validation" / STEM
    uploaded_dir = stage / "uploaded"
    cert_path = stage / "uploaded-variant-validation.json"
    required = [
        uploaded_dir / "Definitions" / (STEM + ".lean"),
        uploaded_dir / "SnapshotUploaded.lean",
        uploaded_dir / "Definitions" / (STEM + ".lean.preflight.json"),
        uploaded_dir / "SnapshotUploaded.lean.preflight.json",
        stage / "uploaded-definitions.json",
    ]
    if cert_path.exists():
        raise ValueError("Supplemental certificate already exists; refusing to replace it")
    if not uploaded_dir.is_dir() or not all(path.is_file() for path in required):
        raise ValueError("Both actual uploaded-variant preflights and their JSON output must already exist")

    data = prepare()
    if not data["readback"].get("definition"):
        raise ValueError("Published server readback has no Definition body")
    source_record = certify_preflight_record(
        data, data["source"], data["source_manifest"],
        data["source"].with_suffix(data["source"].suffix + ".preflight.json"),
        "Definitions." + STEM)
    snapshot_record = certify_preflight_record(
        data, data["snapshot"], data["snapshot_manifest"],
        data["snapshot"].with_suffix(data["snapshot"].suffix + ".preflight.json"),
        "SnapshotUploaded")

    uploaded_rows = read_json(data["output_json"])
    names = data["names"]
    original_rows = data["original_rows"]
    if ([row.get("name") for row in uploaded_rows] != names
            or [row.get("name") for row in original_rows] != names):
        raise ValueError("Original and uploaded typed JSON snapshots have different declaration order")
    for original, uploaded in zip(original_rows, uploaded_rows):
        if (len(original.get("levelParams", [])) != len(uploaded.get("levelParams", []))
                or normalize(original, "type") != normalize(uploaded, "type")
                or normalize(original, "value") != normalize(uploaded, "value")):
            raise ValueError("Uploaded bytes change a kernel type or value: " + original["name"])

    axioms = {name: shared_audit_axioms(task_file(snapshot_record["log"]), name)
              for name in names}
    prior_axioms = data["prior_validation"].get("axioms", {}).get("source", {})
    if (set(prior_axioms) != set(names)
            or any(not set(row) <= ALLOWED_AXIOMS for row in prior_axioms.values())):
        raise ValueError("Original source axiom certificate is incomplete or nonstandard")
    runtime_sha = file_sha(VERIFICATION / "lean-runtime.json")
    if source_record["runtime_sha256"] != runtime_sha or snapshot_record["runtime_sha256"] != runtime_sha:
        raise ValueError("The two existing preflights do not share the current pinned runtime")

    cert = {
        "schema_version": 1,
        "at_utc": datetime.now(timezone.utc).isoformat(),
        "validated": True,
        "scope": "exact bytes served by the already-published Collision Definition",
        "theorem_name": data["payload"]["definition_name"],
        "definition_id": data["readback"]["theorem_id"],
        "environment": ENV,
        "visibility": "public",
        "old_publication_sha256": data["publication_sha256"],
        "published_payload_file_sha256": data["payload_sha256"],
        "published_payload_wire_sha256": data["payload_sha256"],
        "server_definition_sha256": data["definition_sha256"],
        "server_definition_bytes": len(data["payload"]["definition"].encode("utf-8")),
        "server_readback_definition_sha256": digest(data["readback"]["definition"].encode("utf-8")),
        "uploaded_lean_source_sha256": file_sha(data["source"]),
        "uploaded_source_manifest_sha256": file_sha(data["source"].with_suffix(".manifest.json")),
        "uploaded_snapshot_source_sha256": file_sha(data["snapshot"]),
        "uploaded_snapshot_manifest_sha256": file_sha(data["snapshot"].with_suffix(".manifest.json")),
        "original_validation_sha256": file_sha(stage / "validation.json"),
        "original_rows_sha256": data["original_rows_sha256"],
        "uploaded_rows_sha256": file_sha(data["output_json"]),
        "kernel_types_and_values_equal": True,
        "only_universe_parameter_display_names_normalized": True,
        "snapshot_core_sha256": data["core_sha256"],
        "runtime_sha256": runtime_sha,
        "standard_axioms_only": True,
        "axioms": {"source": prior_axioms, "uploaded": axioms},
        "provided_names": names,
        "preflights": {data["source"].name: source_record, data["snapshot"].name: snapshot_record},
        "preflight_record_sha256": {
            data["source"].name: file_sha(data["source"].with_suffix(data["source"].suffix + ".preflight.json")),
            data["snapshot"].name: file_sha(data["snapshot"].with_suffix(data["snapshot"].suffix + ".preflight.json")),
        },
        "source_sha256": data["source_manifest"]["source_sha256"],
        "original_source_sha256": data["source_manifest"]["original_source_sha256"],
    }
    write_json_immutable(cert_path, cert)
    return cert


def run_preflights(data):
    source = data["source"]
    snapshot = data["snapshot"]
    source_record = preflight_one(source, source.parent.parent.relative_to(VERIFICATION).as_posix())
    snapshot_record = preflight_one(snapshot, snapshot.parent.relative_to(VERIFICATION).as_posix())
    stage = data["stage"]
    uploaded_rows_path = data["output_json"]
    original_rows = data["original_rows"]
    uploaded_rows = read_json(uploaded_rows_path)
    names = data["names"]
    if ([row.get("name") for row in uploaded_rows] != names
            or [row.get("name") for row in original_rows] != names):
        raise ValueError("Uploaded/original snapshot declaration ordering differs")
    for before, after in zip(original_rows, uploaded_rows):
        if (len(before.get("levelParams", [])) != len(after.get("levelParams", []))
                or normalize(before, "type") != normalize(after, "type")
                or normalize(before, "value") != normalize(after, "value")):
            raise ValueError("Published uploaded variant changes kernel type/value: " + before["name"])
    snapshot_axioms = {name: shared_audit_axioms(task_file(snapshot_record["log"]), name)
                       for name in names}
    original_axioms = data["prior_validation"].get("axioms", {}).get("source", {})
    if set(original_axioms) != set(names):
        raise ValueError("Original axiom certificate does not cover uploaded names")
    if any(not set(values) <= ALLOWED_AXIOMS for values in original_axioms.values()):
        raise ValueError("Original source certificate reports a nonstandard axiom")
    runtime_sha = file_sha(VERIFICATION / "lean-runtime.json")
    if source_record.get("runtime_sha256") != runtime_sha or snapshot_record.get("runtime_sha256") != runtime_sha:
        raise ValueError("The two uploaded checks did not use the same current pinned runtime")

    cert = {
        "schema_version": 1,
        "at_utc": datetime.now(timezone.utc).isoformat(),
        "validated": True,
        "scope": "exact bytes served by the already-published Collision Definition",
        "theorem_name": data["payload"]["definition_name"],
        "definition_id": data["readback"]["theorem_id"],
        "environment": ENV,
        "visibility": "public",
        "old_publication_sha256": data["publication_sha256"],
        "published_payload_file_sha256": data["payload_sha256"],
        "published_payload_wire_sha256": data["payload_sha256"],
        "server_definition_sha256": data["definition_sha256"],
        "server_definition_bytes": len(data["payload"]["definition"].encode("utf-8")),
        "server_readback_definition_sha256": digest(data["readback"]["definition"].encode("utf-8")),
        "uploaded_lean_source_sha256": file_sha(source),
        "uploaded_source_manifest_sha256": file_sha(source.with_suffix(".manifest.json")),
        "uploaded_snapshot_source_sha256": file_sha(snapshot),
        "original_validation_sha256": file_sha(stage / "validation.json"),
        "original_rows_sha256": data["original_rows_sha256"],
        "uploaded_rows_sha256": file_sha(uploaded_rows_path),
        "kernel_types_and_values_equal": True,
        "only_universe_parameter_display_names_normalized": True,
        "snapshot_core_sha256": data["core_sha256"],
        "runtime_sha256": runtime_sha,
        "standard_axioms_only": True,
        "axioms": {"source": original_axioms, "uploaded": snapshot_axioms},
        "provided_names": names,
        "preflights": {
            source.name: source_record,
            snapshot.name: snapshot_record,
        },
        "source_sha256": data["source_manifest"]["source_sha256"],
        "original_source_sha256": data["source_manifest"]["original_source_sha256"],
    }
    cert_path = stage / "uploaded-variant-validation.json"
    write_json(cert_path, cert)
    return cert


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--run-preflights", action="store_true",
                       help="Run two strict staged Lean checks; default only prepares exact byte inputs")
    modes.add_argument("--certify-existing", action="store_true",
                       help="Validate existing actual records without invoking Lean")
    args = parser.parse_args()
    if args.certify_existing:
        cert = certify_existing()
        print(json.dumps({"certified_existing": True, "definition_id": cert["definition_id"],
                          "kernel_types_and_values_equal": cert["kernel_types_and_values_equal"],
                          "max_seconds": max(row["seconds"] for row in cert["preflights"].values()),
                          "certificate": "verification/definition-validation/" + STEM +
                          "/uploaded-variant-validation.json"}))
        return
    data = prepare()
    if args.run_preflights:
        cert = run_preflights(data)
        print(json.dumps({"validated": True, "definition_id": cert["definition_id"],
                          "kernel_types_and_values_equal": True,
                          "max_seconds": max(row["seconds"] for row in cert["preflights"].values())}))
    else:
        print(json.dumps({"prepared_only": True, "source_sha256": data["definition_sha256"],
                          "payload_sha256": data["payload_sha256"],
                          "definition_id": data["readback"]["theorem_id"]}))


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError,
            subprocess.TimeoutExpired) as exc:
        raise SystemExit("uploaded Definition variant audit refused to proceed: " + str(exc))
