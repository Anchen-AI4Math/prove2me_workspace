"""Publish only one of the four fully kernel-certified namespace providers."""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re

import validate_namespace_context_providers as checker
import prepare_fast_provider_snapshot as frozen_fast
import replay_fast_provider_snapshot_windows as windows_fast

TASK, ROOT = checker.TASK, checker.ROOT
V = TASK / "verification"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def save_preserving(path, data):
    if path.is_file() and path.read_bytes() != data:
        previous = path.read_bytes()
        directory = V / "publication-record-history"
        directory.mkdir(exist_ok=True)
        archive = directory / (hashlib.sha256(previous).hexdigest() + ".json")
        if archive.is_file() and archive.read_bytes() != previous:
            raise ValueError("Publication archive hash collision")
        archive.write_bytes(previous)
    path.write_bytes(data)


def prepare(module, metadata_path):
    # Only the external ordinary fast helper's filesystem spelling comparison
    # is adapted. Its exact CI exporter/provenance/pins remain frozen, and the
    # replacement rechecks all fields with samefile for drive-case aliases.
    original = frozen_fast.checked_fast_generated_snapshot
    try:
        frozen_fast.checked_fast_generated_snapshot = windows_fast.checked_fast_generated_snapshot
        evidence = checker.validate_context_provider(module)
    finally:
        frozen_fast.checked_fast_generated_snapshot = original
    manifest_path = evidence["manifest"]
    manifest = read(manifest_path)
    cert_path = TASK / evidence["certificate"]["path"]
    certificate = evidence["certificate"]["data"]
    if (evidence.get("validated") is not True or certificate.get("validated") is not True
            or certificate.get("closed_types") is not True
            or certificate.get("full_def_values_equal") is not True
            or certificate.get("Std3_only") is not True
            or certificate.get("theorem_values_null") is not True):
        raise ValueError("Actual complete provider kernel comparison has not passed")
    stem = manifest["platform_module"].removeprefix("Definitions.")
    name = stem.removeprefix("Def_")
    if stem != "Def_" + name or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        raise ValueError("Invalid Definition module/name")
    stage = cert_path.parent
    metadata_path = metadata_path.resolve()
    if not metadata_path.is_relative_to(TASK.resolve()):
        raise ValueError("Metadata is outside mission")
    metadata = read(metadata_path)
    requests = read(TASK / "verification/providers-context-preview/namespace-context/snapshots" /
                    stem / "snapshot-requests.json")["original"]
    names = [row["source_graph_name"] for row in requests]
    if metadata.get("declarations") != names or [row["name"] for row in certificate["comparisons"]] != names:
        raise ValueError("Metadata/certificate/request exact declaration domains differ")
    for field in ("definition_title", "natural_language_statement", "explanation"):
        if not isinstance(metadata.get(field), str) or not metadata[field].strip():
            raise ValueError("Missing reviewed mathematical metadata: " + field)
    if "openai-pi-exponent-017" not in metadata.get("tags", []):
        raise ValueError("Missing original project provenance tag")
    plan_path = TASK / manifest["provider_plan"]
    if sha(plan_path) != manifest["provider_plan_sha256"]:
        raise ValueError("Source unit plan changed")
    units = {row["id"]: row for row in read(plan_path)["units"]}
    selected = [units[unit] for unit in manifest["selected_units"]]
    start, end = min(row["start"]["line"] for row in selected), max(row["end"]["line"] for row in selected)
    url = f"https://github.com/openai/math/blob/{COMMIT}/lean/{module.replace('.', '/')}.lean#L{start}-L{end}"
    metadata = dict(metadata, source=f"OpenAI math, commit {COMMIT}: {url}", source_commit=COMMIT,
                    source_module=module, platform_module=manifest["platform_module"])
    raw = evidence["source_bytes"]
    digest = hashlib.sha256(raw).hexdigest()
    if digest != manifest["output_sha256"] or digest != certificate["provider_source_sha256"]:
        raise ValueError("Certified raw source differs")
    payload = dict(definition_name=name, definition_title=metadata["definition_title"],
                   definition=raw.decode("utf-8"), natural_language_statement=metadata["natural_language_statement"],
                   source=metadata["source"], tags=metadata["tags"], env=ENV, private=False)
    wire = json.dumps(payload, ensure_ascii=False).encode()
    wire_sha = hashlib.sha256(wire).hexdigest()
    record = dict(schema_version=1, prepared_at_utc=datetime.now(timezone.utc).isoformat(),
                  offline_prepare_only=True, publisher_script_sha256=sha(Path(__file__)),
                  definition_name=name, definition_module=manifest["platform_module"],
                  environment=ENV, visibility="public", mission_proposal_status="Draft",
                  metadata_input_sha256=sha(metadata_path), payload_sha256=wire_sha,
                  wire_body_sha256=wire_sha, bundle_source_sha256=digest,
                  bundle_manifest_sha256=sha(manifest_path), validation_sha256=sha(cert_path),
                  source_commit=COMMIT, uploaded_definition_bytes=len(raw),
                  source34_certificate_sha256=certificate["source34_certificate_sha256"],
                  kernel_comparison_declarations=names,
                  all_types_and_full_definition_values_equal=True, standard_axioms_only=True,
                  source_scope_partial=True, full_platform_dependency_closure_complete=False,
                  windows_fast_replay_helper_sha256=sha(Path(windows_fast.__file__)))
    publication = stage / "publication.json"
    if publication.is_file():
        prior = read(publication)
        if ((prior.get("publish_intent") or prior.get("definition_id") or prior.get("publish_payload_sha256"))
                and prior.get("publish_payload_sha256") != wire_sha):
            raise ValueError("Existing publication intent fixes immutable payload bytes")
    for filename, data in (("metadata.json", encode(metadata)), ("publish-payload.json", wire),
                           ("prepare-record.json", encode(record))):
        save_preserving(stage / filename, data)
    return stage, metadata, payload, record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", required=True)
    parser.add_argument("--metadata-file", required=True)
    parser.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    stage, metadata, payload, preparation = prepare(args.module, TASK / args.metadata_file)
    if args.advance:
        spec = importlib.util.spec_from_file_location("closed_definition_api", TASK / "scripts/publish_closed_definition_bundle.py")
        api = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(api)
        record = api.advance(stage, metadata, payload, preparation)
        result = dict(advanced=True, definition_name=payload["definition_name"],
                      definition_id=record.get("definition_id"), job_id=record.get("job_id"),
                      status=record.get("last_publish_verdict", {}).get("body", {}).get("status"))
    else:
        result = dict(prepared_offline=True, definition_name=payload["definition_name"],
                      payload_sha256=preparation["payload_sha256"], declarations=preparation["kernel_comparison_declarations"])
    print(json.dumps(result))


if __name__ == "__main__":
    main()
