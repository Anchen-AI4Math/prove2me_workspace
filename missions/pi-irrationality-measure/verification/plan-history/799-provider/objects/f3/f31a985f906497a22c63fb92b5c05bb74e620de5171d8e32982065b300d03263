#!/usr/bin/env python3
"""Prepare or explicitly advance one certified Prove2Me Definition provider.

The provider is uploaded as the complete generated Lean module, including its
proved public theorem declaration.  Offline preparation is the default and is
blocked until actual local staged preflight and kernel snapshot evidence exist.
The explicit API mode reuses the already-tested Definition publisher's exact
name/environment checks, durable at-most-once intent, bounded job poll, and
byte-exact public readback.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
VERIFICATION = TASK / "verification"
PLATFORM = TASK / "platform"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
BATCH = "all-shared-safe-leaves"
SOURCE_MODULE = "OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedComponent"
STEM = "Def_OAI_NumberTheory_PiExponent_LocalAlgebra_LocalizedComponent"
VALIDATOR_PATH = TASK / "scripts" / "validate_provider_bundle.py"
DEFINITION_PUBLISHER_PATH = TASK / "scripts" / "publish_closed_definition_bundle.py"


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value):
    raw = (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return raw


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ValueError(f"Cannot load helper module {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def target_data():
    validator = load_module(VALIDATOR_PATH, "provider_validator_for_publish")
    structural = validator.structural_check(BATCH, SOURCE_MODULE)
    if len(structural["declarations"]) != 1:
        raise ValueError("This provider publisher requires one graph-owned declaration")
    declaration = structural["declarations"][0]
    if declaration["kind"] != "theorem":
        raise ValueError("LocalizedComponent provider must contain an ordinary theorem")
    manifest_path = VERIFICATION / "providers-preview" / BATCH / "Definitions" / f"{STEM}.manifest.json"
    manifest = read(manifest_path)
    snap_dir = VERIFICATION / "providers-preview" / BATCH / "snapshots" / STEM
    requests = read(snap_dir / "snapshot-requests.json")
    original_requests = [r for r in requests.get("original", []) if r.get("source_graph_name") == declaration["name"]]
    generated_requests = [r for r in requests.get("generated", []) if r.get("source_graph_name") == declaration["name"]]
    if len(original_requests) != 1 or len(generated_requests) != 1:
        raise ValueError("Provider requests do not uniquely bind the source theorem")
    original, generated = original_requests[0], generated_requests[0]
    if (original.get("expected_kind") != "theorem" or generated.get("expected_kind") != "theorem"
            or original.get("expected_module") != SOURCE_MODULE
            or original.get("expected_public_name") != declaration["name"]
            or original.get("source_was_private") is not False
            or original.get("command_unit") != declaration["unit"]
            or generated.get("expected_module") != manifest.get("platform_module")
            or generated.get("expected_public_name") != declaration["name"]
            or generated.get("source_was_private") is not False):
        raise ValueError("Graph-owned declaration is not the exact ordinary public theorem requested")
    expected_definition_name = manifest.get("platform_module", "").removeprefix("Definitions.Def_")
    if expected_definition_name != "OAI_NumberTheory_PiExponent_LocalAlgebra_LocalizedComponent":
        raise ValueError("Provider Definition API name differs from the pinned module identity")
    return validator, structural, declaration, manifest, manifest_path, original, generated, expected_definition_name


def verify_actual_certificate(validator, structural, manifest):
    stage = VERIFICATION / "providers-preview" / BATCH / "validation" / STEM
    cert_path = stage / "provider-validation.json"
    if not cert_path.is_file():
        raise ValueError("No actual provider-validation.json exists; preparation stops before writing payloads")
    cert = read(cert_path)
    if cert.get("validated") is not True or cert.get("status") != "local-kernel-provider-validated":
        raise ValueError("Provider certificate does not affirm successful local kernel validation")
    for key, value in (("manifest_sha256", structural["manifest_sha256"]),
                       ("provider_source_sha256", structural["provider_source_sha256"]),
                       ("graph_sha256", structural["graph_sha256"]),
                       ("source_module", SOURCE_MODULE),
                       ("platform_module", manifest["platform_module"])):
        if cert.get(key) != value:
            raise ValueError("Provider certificate binds different source/module state: " + key)
    if cert.get("declarations") != structural["declarations"]:
        raise ValueError("Certificate declaration identities differ from the graph-owned public request")
    if cert.get("submission_ready") is not False or cert.get("preview_only") is not True:
        raise ValueError("Provider evidence must remain a preview certificate")
    stages = validator.stage_manifests(structural)
    preflights = [validator.verify_preflight_record(item) for item in stages]
    if cert.get("preflights") != preflights:
        raise ValueError("Current sidecars/logs/runtime/OLeans differ from certified preflight records")
    snapshots = validator.compare_snapshots(structural, stages)
    if cert.get("snapshot_comparison") != snapshots:
        raise ValueError("Current actual source/generated kernel snapshots differ from certificate")
    if not all(snapshots.get(key) is True for key in ("types_equal", "values_equal", "axioms_equal_and_std3")):
        raise ValueError("Provider has not passed type/value equality and Std3")
    return stage, cert, preflights, snapshots


def metadata_for(declaration, manifest, source_unit):
    first, last = source_unit["start"]["line"], source_unit["end"]["line"]
    source_path = SOURCE_MODULE.replace(".", "/") + ".lean"
    source_url = f"https://github.com/openai/math/blob/{COMMIT}/lean/{source_path}#L{first}-L{last}"
    return {
        "definition_title": "Prime radical membership in the minimal primes",
        "natural_language_statement": (
            "This provider module contains the public Lean theorem stating that, for a "
            "commutative ring R and ideal I, if the radical of I is prime, then that radical "
            "belongs to the set of minimal prime ideals over I. The module includes the "
            "complete proved theorem body."
        ),
        "tags": ["commutative-algebra", "prime-ideals", "number-theory", "openai-pi-exponent-017"],
        "source": (f"OpenAI math, commit {COMMIT}, {source_path}, lines {first}-{last}: {source_url}"),
        "explanation": (
            "The proved public theorem identifies a prime radical with a minimal prime over "
            "the original ideal. Its proof rewrites the minimal-prime set of a prime radical "
            "as a singleton and establishes membership."
        ),
        "declarations": [declaration["name"]],
        "source_module": manifest["source_module"],
        "platform_module": manifest["platform_module"],
        "source_commit": COMMIT,
        "source_sha256": manifest["source_sha256"],
    }


def prepare():
    validator, structural, declaration, manifest, manifest_path, source_request, generated_request, definition_name = target_data()
    stage, cert, preflights, snapshots = verify_actual_certificate(validator, structural, manifest)
    unit_plan = read(TASK / manifest["provider_plan"])
    unit = next((u for u in unit_plan.get("units", []) if u.get("id") == declaration["unit"]), None)
    if (not unit or unit.get("graph_names") != [declaration["name"]] or unit.get("graph_kinds") != ["theorem"]
            or unit.get("private") or unit.get("deprivate") or unit.get("is_instance_command")
            or unit.get("is_local_instance")):
        raise ValueError("Pinned unit is not a single public ordinary proved theorem")
    source = ROOT / manifest["output"]
    source_bytes = source.read_bytes()
    if sha(source) != manifest.get("output_sha256") or sha(source) != structural["provider_source_sha256"]:
        raise ValueError("Complete provider source bytes changed after validation")
    # The whole generated module is uploaded as the Definition body.  This
    # preserves the proof bytes and CRLF/LF mix exactly; no text-mode reread.
    definition_body = source_bytes.decode("utf-8")
    metadata = metadata_for(declaration, manifest, unit)
    payload = {
        "definition_name": definition_name,
        "definition_title": metadata["definition_title"],
        "definition": definition_body,
        "natural_language_statement": metadata["natural_language_statement"],
        "source": metadata["source"],
        "tags": metadata["tags"],
        "env": ENV,
        "private": False,
    }
    payload_bytes = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    prep = {
        "schema_version": 1,
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "offline_prepare_only": True,
        "publisher_script_sha256": sha(Path(__file__).resolve()),
        "definition_name": definition_name,
        "definition_module": manifest["platform_module"],
        "declarations": [declaration["name"]],
        "environment": ENV,
        "visibility": "public",
        "mission_proposal_status": "Draft",
        "metadata_sha256": sha_bytes((json.dumps(metadata, ensure_ascii=False, indent=2) + "\n").encode("utf-8")),
        "payload_sha256": sha_bytes(payload_bytes),
        "payload_encoding": "Exact UTF-8 JSON bytes saved and sent unchanged",
        "wire_body_sha256": sha_bytes(payload_bytes),
        "bundle_source_sha256": sha_bytes(source_bytes),
        "uploaded_definition_sha256": sha_bytes(definition_body.encode("utf-8")),
        "uploaded_definition_bytes": len(definition_body.encode("utf-8")),
        "definition_bytes_equal_bundle_source": definition_body.encode("utf-8") == source_bytes,
        "bundle_manifest_sha256": sha(manifest_path),
        "validation_sha256": sha(stage / "provider-validation.json"),
        "source_commit": COMMIT,
        "preflight_count": len(preflights),
        "max_preflight_seconds": max(item["seconds"] for item in preflights),
        "olean_sha256": next(item["output_olean_sha256"] for item in preflights if item["role"] == "provider-bundle"),
        "snapshot_comparison": snapshots,
        "source_request": source_request,
        "generated_request": generated_request,
    }
    publication_path = stage / "publication.json"
    if publication_path.exists():
        prior = read(publication_path)
        if ((prior.get("publish_intent") or prior.get("definition_id") or prior.get("publish_payload_sha256"))
                and prior.get("publish_payload_sha256") != prep["payload_sha256"]):
            raise ValueError("Existing publication intent/record makes the payload immutable")
    write_json(stage / "metadata.json", metadata)
    (stage / "publish-payload.json").write_bytes(payload_bytes)
    write_json(stage / "prepare-record.json", prep)
    return stage, metadata, payload, prep


def advance(stage, metadata, payload, prep):
    # Reuse the PUBLISHED-definition request/advance/at-most-once/readback path.
    helper = load_module(DEFINITION_PUBLISHER_PATH, "published_definition_helper")
    return helper.advance(stage, metadata, payload, prep)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--prepare-only", action="store_true", help="Offline preparation (the default)")
    mode.add_argument("--advance", action="store_true", help="Explicit exact-name/environment checks and one POST at most")
    args = parser.parse_args()
    stage, metadata, payload, prep = prepare()
    if args.advance:
        record = advance(stage, metadata, payload, prep)
        print(json.dumps({"advanced": True, "definition_name": payload["definition_name"],
                          "definition_id": record.get("definition_id"), "job_id": record.get("job_id"),
                          "status": record.get("last_publish_verdict", {}).get("body", {}).get("status")}, ensure_ascii=False))
    else:
        print(json.dumps({"prepared_offline": True, "stage": stage.relative_to(TASK).as_posix(),
                          "definition_name": payload["definition_name"],
                          "declarations": prep["declarations"], "payload_sha256": prep["payload_sha256"],
                          "uploaded_definition_bytes": prep["uploaded_definition_bytes"]}, ensure_ascii=False))


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, ValueError, TypeError, json.JSONDecodeError) as exc:
        raise SystemExit("provider publisher refused to proceed: " + str(exc))
