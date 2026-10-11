"""Publish the exact kernel-certified FormalLogTruncation provider; retain Draft."""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path

import validate_formal_log_truncation_provider as checker
from publish_context_provider_bundle import TASK, ROOT, ENV, COMMIT, read, sha, encode, save_preserving

MODULE = "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation"
NAME = "OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation"


def mission_file(value, base=TASK):
    path = Path(value)
    if not path.is_absolute():
        path = base / path
    path = path.resolve()
    if not path.is_relative_to(TASK.resolve()) or not path.is_file():
        raise ValueError("Missing or outside task evidence: " + str(value))
    return path


def prepare(metadata_path):
    evidence = checker.validate_formal_log_provider()
    manifest_path = mission_file(evidence["manifest"])
    manifest = read(manifest_path)
    cert_path = mission_file(evidence["certificate"]["path"])
    expected_stage = (TASK / "verification/providers-formal-log-preview/formal-log/validation" / ("Def_" + NAME)).resolve()
    if cert_path.parent != expected_stage:
        raise ValueError("Certificate is outside the exact FormalLog validation stage")
    certificate = evidence["certificate"]["data"]
    if sha(cert_path) != evidence["certificate"]["sha256"] or read(cert_path) != certificate:
        raise ValueError("Actual certificate changed after readonly replay")
    if (mission_file(certificate["manifest"]) != manifest_path
            or certificate["manifest_sha256"] != sha(manifest_path)
            or certificate.get("source_commit") != COMMIT):
        raise ValueError("Certificate does not bind the current exact manifest and source commit")
    for flag in ("validated", "closed_types", "full_def_values_equal", "Std3_only", "theorem_values_null"):
        if certificate.get(flag) is not True:
            raise ValueError("Complete ordinary kernel comparison did not pass: " + flag)
    if manifest["source_module"] != MODULE or manifest["platform_module"] != "Definitions.Def_" + NAME:
        raise ValueError("Unexpected provider module")
    bindings_path = mission_file(manifest["source_catalog_bindings"])
    if sha(bindings_path) != manifest["source_catalog_bindings_sha256"]:
        raise ValueError("Exact source catalog binding changed")
    names = [row["source_graph_name"] for row in read(bindings_path)["requests"]]
    if len(names) != 18 or len(set(names)) != 18 or [r["name"] for r in certificate["comparisons"]] != names:
        raise ValueError("Certificate must cover the exact eighteen public declarations")
    metadata_path = metadata_path.resolve()
    if not metadata_path.is_relative_to(TASK.resolve()):
        raise ValueError("Metadata is outside task")
    metadata = read(metadata_path)
    if metadata.get("declarations") != names or "openai-pi-exponent-017" not in metadata.get("tags", []):
        raise ValueError("Metadata declaration domain or provenance differs")
    for field in ("definition_title", "natural_language_statement", "explanation"):
        if not isinstance(metadata.get(field), str) or not metadata[field].strip():
            raise ValueError("Missing reviewed mathematical metadata: " + field)
    plan_path = mission_file(manifest["provider_plan"])
    if sha(plan_path) != manifest["provider_plan_sha256"]:
        raise ValueError("Source unit plan changed")
    units = {row["id"]: row for row in read(plan_path)["units"]}
    selected = [units[key] for key in manifest["selected_units"]]
    start = min(row["start"]["line"] for row in selected)
    end = max(row["end"]["line"] for row in selected)
    url = f"https://github.com/openai/math/blob/{COMMIT}/lean/{MODULE.replace('.', '/')}.lean#L{start}-L{end}"
    metadata = dict(metadata, source=f"OpenAI math, commit {COMMIT}: {url}", source_commit=COMMIT,
                    source_module=MODULE, platform_module=manifest["platform_module"],
                    selected_source_units=[dict(id=row["id"], start_line=row["start"]["line"],
                        end_line=row["end"]["line"]) for row in selected])
    raw = evidence["source_bytes"]
    source_path = mission_file(evidence["provider_source"])
    output_path = mission_file(manifest["output"], ROOT)
    if source_path != output_path or raw != source_path.read_bytes():
        raise ValueError("Readonly evidence differs from the exact staged source file")
    digest = hashlib.sha256(raw).hexdigest()
    if digest != manifest["output_sha256"] or digest != certificate["provider_source_sha256"]:
        raise ValueError("Raw certified provider source changed")
    payload = dict(definition_name=NAME, definition_title=metadata["definition_title"], definition=raw.decode("utf-8"),
        natural_language_statement=metadata["natural_language_statement"], source=metadata["source"],
        tags=metadata["tags"], env=ENV, private=False)
    wire = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    wire_sha = hashlib.sha256(wire).hexdigest()
    preparation = dict(schema_version=1, prepared_at_utc=datetime.now(timezone.utc).isoformat(), offline_prepare_only=True,
        publisher_script_sha256=sha(Path(__file__)), checker_script_sha256=sha(Path(checker.__file__)),
        definition_name=NAME, definition_module=manifest["platform_module"], environment=ENV, visibility="public",
        mission_proposal_status="Draft", metadata_input_sha256=sha(metadata_path), payload_sha256=wire_sha,
        wire_body_sha256=wire_sha, bundle_source_sha256=digest, bundle_manifest_sha256=sha(manifest_path),
        validation_sha256=sha(cert_path), uploaded_definition_bytes=len(raw), kernel_comparison_declarations=names,
        source18_certificate_sha256=certificate["source18_certificate_sha256"],
        all_types_and_full_definition_values_equal=True, standard_axioms_only=True,
        source_scope_partial=True, full_platform_dependency_closure_complete=False)
    stage = cert_path.parent
    publication = stage / "publication.json"
    if publication.is_file():
        prior = read(publication)
        if ((prior.get("publish_intent") or prior.get("definition_id") or prior.get("publish_payload_sha256"))
                and prior.get("publish_payload_sha256") != wire_sha):
            raise ValueError("Existing publication intent fixes exact payload bytes")
    for filename, data in (("metadata.json", encode(metadata)), ("publish-payload.json", wire),
                           ("prepare-record.json", encode(preparation))):
        save_preserving(stage / filename, data)
    return stage, metadata, payload, preparation


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--metadata-file", default="platform/formal-log-provider-metadata/FormalLogTruncation.json")
    parser.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    stage, metadata, payload, preparation = prepare(TASK / args.metadata_file)
    if args.advance:
        spec = importlib.util.spec_from_file_location("formal_definition_api", TASK / "scripts/publish_closed_definition_bundle.py")
        api = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(api)
        record = api.advance(stage, metadata, payload, preparation)
        result = dict(advanced=True, definition_name=NAME, definition_id=record.get("definition_id"),
            job_id=record.get("job_id"), status=record.get("last_publish_verdict", {}).get("body", {}).get("status"))
    else:
        result = dict(prepared_offline=True, definition_name=NAME, payload_sha256=preparation["payload_sha256"], declarations=18)
    print(json.dumps(result))


if __name__ == "__main__":
    main()
