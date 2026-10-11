#!/usr/bin/env python3
"""Prepare/advance a fully certified provider from the complete 875-module plan.

The entire generated Lean file is a Definition payload. This never creates a
sorry-stub problem or treats Python generation as proof verification.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
PROVIDERS = V / "providers-complete-preview"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return digest(path.read_bytes())


def read(path):
    return json.loads(path.read_bytes())


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def prepare(batch, module, metadata_path):
    validator = load(TASK / "scripts/validate_provider_bundle.py", "complete_provider_validator")
    structure = validator.structural_check(batch, module, PROVIDERS)
    manifest_path = TASK / structure["manifest"]
    manifest = read(manifest_path)
    platform_module = manifest["platform_module"]
    name = platform_module.removeprefix("Definitions.Def_")
    if platform_module != "Definitions.Def_" + name or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        raise ValueError("Invalid Definition API name or module identity")
    stem = manifest_path.name.removesuffix(".manifest.json")
    stage = PROVIDERS / batch / "validation" / stem
    ordinary_cert = stage / "provider-validation.json"
    fast_cert = stage / "provider-validation-fast.json"
    if ordinary_cert.is_file() and fast_cert.is_file():
        raise ValueError("Ambiguous ordinary and fast certificates for the same provider")
    cert_path = fast_cert if fast_cert.is_file() else ordinary_cert
    if not cert_path.is_file():
        raise ValueError("Actual local provider certificate is absent; no payload will be written")
    cert = read(cert_path)
    if (cert.get("validated") is not True
            or cert.get("status") != "local-kernel-provider-validated"
            or cert.get("preview_only") is not True
            or cert.get("submission_ready") is not False):
        raise ValueError("Certificate does not establish actual bounded kernel validation")
    for field in ("manifest_sha256", "provider_source_sha256", "graph_sha256",
                  "source_module", "platform_module", "declarations"):
        if cert.get(field) != structure.get(field):
            raise ValueError("Certificate differs from current structural evidence: " + field)
    source_subset = None
    if cert.get("source_subset_certificate") is not None:
        if cert.get("source_snapshot_strategy") != "provider-source-subset-cache; skip original snapshot compile":
            raise ValueError("Unexpected partial source-cache strategy")
        evidence = cert["source_subset_certificate"]
        if evidence.get("cache_validator") not in {
                "scripts/provider_source_subset_cache.py",
                "scripts/provider_source_subset_cache_windows.py"}:
            raise ValueError("Unrecognized source-subset verifier")
        helper = TASK / evidence["cache_validator"]
        if (evidence.get("cache_validator") != helper.relative_to(TASK).as_posix()
                or evidence.get("cache_validator_sha256") != sha(helper)):
            raise ValueError("Source-subset verifier differs from the captured evidence")
        request_doc = read(TASK / structure["snapshot_dir"] / "snapshot-requests.json")
        certificate = (TASK / evidence["certificate"]).resolve()
        if not certificate.is_relative_to(TASK.resolve()) or not certificate.is_file():
            raise ValueError("Source-subset certificate is absent or outside the mission")
        source_subset = validator.validate_provider_source_subset_cache(certificate, request_doc["original"])
        replay = dict(source_subset["evidence"], cache_validator=helper.relative_to(TASK).as_posix(),
                      cache_validator_sha256=sha(helper))
        if evidence != replay:
            raise ValueError("Fresh complete replay differs from the certified partial source evidence")
        if (cert["snapshot_comparison"].get("source_snapshot_strategy") != "provider-source-subset-cache"
                or cert["snapshot_comparison"].get("source_subset_evidence") != source_subset["evidence"]
                or set(cert["snapshot_comparison"].get("snapshot_jsonl_sha256", {})) != {"generated"}):
            raise ValueError("Generated comparison does not bind this authenticated source subset")
    elif cert.get("shared_source_certificate") is not None:
        raise ValueError("Full source-cache certificates require their own exact replay; this publisher does not support them")
    fast_generated = None
    if cert.get("fast_generated_snapshot") is not None:
        if cert_path != fast_cert or source_subset is None:
            raise ValueError("Fast snapshot requires its distinct certificate and authenticated source subset")
        replay_helper = TASK / "scripts/replay_fast_provider_snapshot_windows.py"
        replay_validator = load(replay_helper, "fast_snapshot_windows_replay")
        fast_generated = replay_validator.checked_fast_generated_snapshot(structure)
        helper = TASK / "scripts/prepare_fast_provider_snapshot.py"
        replay = {
            "strategy": "exact-public-Name-direct-env-lookup",
            "helper": helper.relative_to(TASK).as_posix(),
            "helper_sha256": sha(helper),
            "source": fast_generated["source"],
            "source_sha256": sha(V / fast_generated["source"]),
            "generated_jsonl": Path(fast_generated["generated_jsonl"]).resolve().relative_to(TASK).as_posix(),
            "generated_jsonl_sha256": sha(Path(fast_generated["generated_jsonl"])),
            "provenance": fast_generated["fast_generated_provenance"],
            "provenance_sha256": fast_generated["fast_generated_provenance_sha256"],
            "ordinary_public_requests_only": True,
            "private_branch_eligible": False,
        }
        if cert["fast_generated_snapshot"] != replay:
            raise ValueError("Fresh fast snapshot replay differs from certified evidence")
    elif cert_path == fast_cert:
        raise ValueError("Distinct fast certificate lacks exact fast snapshot evidence")
    stages = validator.stage_manifests(structure, include_original_snapshot=source_subset is None,
                                      include_generated_snapshot=fast_generated is None)
    if fast_generated is not None:
        stages.append({key: fast_generated[key] for key in
                       ("source", "root", "manifest", "module", "imports", "mode", "role")})
    preflights = [validator.verify_preflight_record(item) for item in stages]
    if source_subset is not None and [p["role"] for p in preflights] != ["provider-bundle", "generated-snapshot"]:
        raise ValueError("Partial source-cache proof needs exactly two actual preflight records")
    comparison = validator.compare_snapshots(structure, stages, source_subset,
                                             "provider-source-subset" if source_subset is not None else None,
                                             fast_generated)
    if cert.get("preflights") != preflights or cert.get("snapshot_comparison") != comparison:
        raise ValueError("Actual compiler/OLean/log/kernel snapshot evidence differs")
    if not all(comparison.get(field) is True for field in
               ("types_equal", "values_equal", "axioms_equal_and_std3")):
        raise ValueError("Type/value/axiom equality has not passed")
    metadata_path = metadata_path.resolve()
    if not metadata_path.is_relative_to(TASK.resolve()) or not metadata_path.is_file():
        raise ValueError("Metadata must be an existing mission-local file")
    metadata = read(metadata_path)
    names = [item["name"] for item in structure["declarations"]]
    if metadata.get("declarations") != names:
        raise ValueError("Metadata declaration list differs from the exact certified source CI list")
    for field in ("definition_title", "natural_language_statement", "explanation"):
        if not isinstance(metadata.get(field), str) or not metadata[field].strip():
            raise ValueError("Missing reviewed mathematical metadata: " + field)
    tags = metadata.get("tags")
    if not isinstance(tags, list) or not tags or not all(isinstance(t, str) and t for t in tags):
        raise ValueError("Metadata tags are absent")
    if "openai-pi-exponent-017" not in tags:
        raise ValueError("Project provenance tag is required")
    plan = read(TASK / manifest["provider_plan"])
    units = {unit["id"]: unit for unit in plan["units"]}
    source_units = [units[item["unit"]] for item in structure["declarations"]]
    start = min(unit["start"]["line"] for unit in source_units)
    end = max(unit["end"]["line"] for unit in source_units)
    source_module = manifest["source_module"]
    source_path = source_module.replace(".", "/") + ".lean"
    source_url = f"https://github.com/openai/math/blob/{COMMIT}/lean/{source_path}#L{start}-L{end}"
    metadata = dict(metadata, source=f"OpenAI math, commit {COMMIT}: {source_url}",
                    source_commit=COMMIT, source_module=source_module,
                    platform_module=platform_module, source_sha256=manifest["source_sha256"])
    source = (ROOT / manifest["output"]).resolve()
    if not source.is_relative_to(PROVIDERS.resolve()):
        raise ValueError("Provider source is outside the complete-plan staging root")
    raw = source.read_bytes()
    if digest(raw) != manifest["output_sha256"] or digest(raw) != structure["provider_source_sha256"]:
        raise ValueError("Certified complete provider source bytes differ")
    payload = dict(definition_name=name, definition_title=metadata["definition_title"],
                   definition=raw.decode("utf-8"),
                   natural_language_statement=metadata["natural_language_statement"],
                   source=metadata["source"], tags=tags, env=ENV, private=False)
    wire = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    prep = dict(schema_version=1, prepared_at_utc=datetime.now(timezone.utc).isoformat(),
                offline_prepare_only=True, publisher_script_sha256=sha(Path(__file__)),
                definition_name=name, definition_module=platform_module, declarations=names,
                environment=ENV, visibility="public", mission_proposal_status="Draft",
                metadata_input_sha256=sha(metadata_path), metadata_sha256=digest(encoded(metadata)),
                payload_sha256=digest(wire), wire_body_sha256=digest(wire),
                payload_encoding="Exact UTF-8 JSON bytes saved and sent unchanged",
                bundle_source_sha256=digest(raw), uploaded_definition_sha256=digest(raw),
                uploaded_definition_bytes=len(raw), definition_bytes_equal_bundle_source=True,
                bundle_manifest_sha256=sha(manifest_path), validation_sha256=sha(cert_path),
                source_commit=COMMIT, preflight_count=len(preflights),
                max_preflight_seconds=max(record["seconds"] for record in preflights),
                olean_sha256=next(record["output_olean_sha256"] for record in preflights
                                 if record["role"] == "provider-bundle"),
                snapshot_comparison=comparison)
    if source_subset is not None:
        prep["source_subset_certificate"] = cert["source_subset_certificate"]
        prep["source_snapshot_strategy"] = cert["source_snapshot_strategy"]
    if fast_generated is not None:
        prep["fast_generated_snapshot"] = cert["fast_generated_snapshot"]
        prep["fast_snapshot_windows_replay"] = {
            "helper": replay_helper.relative_to(TASK).as_posix(),
            "helper_sha256": sha(replay_helper),
            "normalization": "actual_import_oleans path/search-root drive-letter case only; exact suffix and samefile",
            "all_other_provenance_and_import_fields_exact": True,
        }
    publication_path = stage / "publication.json"
    if publication_path.exists():
        prior = read(publication_path)
        if ((prior.get("publish_intent") or prior.get("definition_id")
             or prior.get("publish_payload_sha256"))
                and prior.get("publish_payload_sha256") != prep["payload_sha256"]):
            raise ValueError("Existing publication intent makes this exact payload immutable")
    for filename, content in (("metadata.json", encoded(metadata)),
                              ("publish-payload.json", wire),
                              ("prepare-record.json", encoded(prep))):
        destination = stage / filename
        if destination.is_file() and destination.read_bytes() != content:
            previous = destination.read_bytes()
            history = V / "publication-record-history"
            history.mkdir(parents=True, exist_ok=True)
            archive = history / (digest(previous) + ".json")
            if archive.is_file() and archive.read_bytes() != previous:
                raise ValueError("Publication history hash collision")
            archive.write_bytes(previous)
        destination.write_bytes(content)
    return stage, metadata, payload, prep


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batch", default="all-shared-safe-leaves",
                        choices=("all-shared-safe-leaves", "minimum-statement"))
    parser.add_argument("--module", required=True)
    parser.add_argument("--metadata-file", required=True)
    parser.add_argument("--advance", action="store_true",
                        help="At most one authorized submit-definition POST or one bounded job poll")
    args = parser.parse_args()
    stage, metadata, payload, prep = prepare(args.batch, args.module, TASK / args.metadata_file)
    if args.advance:
        helper = load(TASK / "scripts/publish_closed_definition_bundle.py", "complete_provider_api")
        record = helper.advance(stage, metadata, payload, prep)
        print(json.dumps(dict(advanced=True, definition_name=payload["definition_name"],
                              definition_id=record.get("definition_id"), job_id=record.get("job_id"),
                              status=record.get("last_publish_verdict", {}).get("body", {}).get("status"))))
    else:
        print(json.dumps(dict(prepared_offline=True, stage=stage.relative_to(TASK).as_posix(),
                              definition_name=payload["definition_name"], payload_sha256=prep["payload_sha256"],
                              declarations=prep["declarations"], uploaded_definition_bytes=prep["uploaded_definition_bytes"])))


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, ValueError, TypeError, json.JSONDecodeError) as exc:
        raise SystemExit("complete provider publisher refused: " + str(exc))
