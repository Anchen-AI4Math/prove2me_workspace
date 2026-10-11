"""Publish the fully certified Parameters structure with complete kernel replay."""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path

from structural_provider_certificate_evidence_windows import struct_cert_evidence
import structural_provider_certificate_evidence_windows as replay
from publish_context_provider_bundle import read, encode, sha, save_preserving, TASK, ENV, COMMIT

MODULE = "OAI.NumberTheory.PiExponent.Approximation.Parameters"


def prepare(metadata_path):
    evidence = struct_cert_evidence(MODULE)
    cert_path = TASK / evidence["certificate"]
    certificate = read(cert_path)
    manifest_path = TASK / certificate["provider_manifest"]
    manifest = read(manifest_path)
    if sha(manifest_path) != certificate["provider_manifest_sha256"]:
        raise ValueError("Certified provider manifest changed")
    names = evidence["compared_names"]
    if len(names) != 25 or len(set(names)) != 25:
        raise ValueError("Incomplete atomic Parameters CI domain")
    metadata_path = metadata_path.resolve()
    if not metadata_path.is_relative_to(TASK.resolve()):
        raise ValueError("Metadata is outside task")
    metadata = read(metadata_path)
    if metadata.get("declarations") != names:
        raise ValueError("Metadata differs from exact 25 certified declarations")
    for field in ("definition_title", "natural_language_statement", "explanation"):
        if not isinstance(metadata.get(field), str) or not metadata[field].strip():
            raise ValueError("Missing reviewed metadata: " + field)
    if "openai-pi-exponent-017" not in metadata.get("tags", []):
        raise ValueError("Missing project provenance tag")
    plan_path = TASK / manifest["provider_plan"]
    if sha(plan_path) != manifest["provider_plan_sha256"]:
        raise ValueError("Source unit plan changed")
    units = {row["id"]: row for row in read(plan_path)["units"]}
    selected = [units[unit] for unit in manifest["selected_units"]]
    start, end = min(u["start"]["line"] for u in selected), max(u["end"]["line"] for u in selected)
    url = f"https://github.com/openai/math/blob/{COMMIT}/lean/{MODULE.replace('.', '/')}.lean#L{start}-L{end}"
    metadata = dict(metadata, source=f"OpenAI math, commit {COMMIT}: {url}", source_commit=COMMIT,
                    source_module=MODULE, platform_module=certificate["platform_module"])
    source_path = (TASK / certificate["provider_source"]).resolve()
    if not source_path.is_relative_to((TASK / "verification/providers-complete-preview").resolve()):
        raise ValueError("Source is outside the certified structural staging root")
    raw = source_path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != certificate["provider_source_sha256"] or digest != manifest["output_sha256"]:
        raise ValueError("Certified raw provider source changed")
    name = "OAI_NumberTheory_PiExponent_Approximation_Parameters"
    if certificate["platform_module"] != "Definitions.Def_" + name:
        raise ValueError("Wrong structural Definition module")
    payload = dict(definition_name=name, definition_title=metadata["definition_title"],
                   definition=raw.decode("utf-8"), natural_language_statement=metadata["natural_language_statement"],
                   source=metadata["source"], tags=metadata["tags"], env=ENV, private=False)
    wire = json.dumps(payload, ensure_ascii=False).encode()
    wire_sha = hashlib.sha256(wire).hexdigest()
    preparation = dict(schema_version=1, prepared_at_utc=datetime.now(timezone.utc).isoformat(),
        publisher_script_sha256=sha(Path(__file__)), offline_prepare_only=True,
        definition_name=name, definition_module=certificate["platform_module"],
        environment=ENV, visibility="public", mission_proposal_status="Draft",
        metadata_input_sha256=sha(metadata_path), payload_sha256=wire_sha, wire_body_sha256=wire_sha,
        bundle_source_sha256=digest, bundle_manifest_sha256=sha(manifest_path),
        validation_sha256=sha(cert_path), uploaded_definition_bytes=len(raw),
        structural_replay=evidence, structural_replay_helper_sha256=sha(Path(replay.__file__)),
        complete_inductive_constructor_recursor_metadata_equal=True,
        recursor_rule_nfields_and_rhs_equal=True, types_and_values_and_std3_equal=True,
        source_scope_partial=True, full_platform_dependency_closure_complete=False)
    stage = TASK / "verification/providers-complete-preview/all-shared-safe-leaves/validation" / ("Def_" + name)
    stage.mkdir(parents=True, exist_ok=True)
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
    parser.add_argument("--metadata-file", default="platform/structural-provider-metadata/Parameters.json")
    parser.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    stage, metadata, payload, preparation = prepare(TASK / args.metadata_file)
    if args.advance:
        spec = importlib.util.spec_from_file_location("closed_structure_api", TASK / "scripts/publish_closed_definition_bundle.py")
        api = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(api)
        record = api.advance(stage, metadata, payload, preparation)
        result = dict(advanced=True, definition_name=payload["definition_name"],
                      definition_id=record.get("definition_id"), job_id=record.get("job_id"),
                      status=record.get("last_publish_verdict", {}).get("body", {}).get("status"))
    else:
        result = dict(prepared_offline=True, definition_name=payload["definition_name"],
                      payload_sha256=preparation["payload_sha256"], declarations=25)
    print(json.dumps(result))


if __name__ == "__main__":
    main()
