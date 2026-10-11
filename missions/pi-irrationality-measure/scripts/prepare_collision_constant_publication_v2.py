"""Freeze the v2-certified collisionConstant Definition publication bundle offline."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_collision_constant_provider_existing_v2 as consumer
import publish_closed_definition_bundle as definition_driver
import stage_collision_constant_provider as stage
import validate_namespace_context_providers as context


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-draft"
CERT = consumer.CERT
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_collision_constant_definition_v2.py"
DEFINITION_NAME = (
    "OAI_NumberTheory_PiExponent_Approximation_"
    "DeterminantContradiction_CollisionConstant"
)
ENV = definition_driver.ENV

CERT_FIELDS = {
    "schema_version", "artifact_kind", "source_commit", "source_module",
    "platform_module", "provided_names", "provider_source_sha256", "provider_olean",
    "provider_olean_sha256", "preparation_sha256", "compiler_manifest_sha256",
    "consumer_provenance",
    "preflights", "source_and_generated_types_equal",
    "definition_values_equal_and_exported", "theorem_values_null", "actual_owners",
    "axioms", "Std3_only", "output_json_sha256", "implementation_hashes",
    "max_file_seconds", "validated", "Lean_started_by_consumer", "API_used",
    "submission_ready", "proposal_status",
}
METADATA_FIELDS = {
    "definition_title", "natural_language_statement", "tags", "source", "explanation",
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(value, *, pretty=True):
    if pretty:
        return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    return json.dumps(value, ensure_ascii=False).encode("utf-8")


def need(condition, message):
    if not condition:
        raise ValueError(message)


def task_rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("frozen collisionConstant publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def static_artifacts():
    stage.check_outputs(stage.stage_files())
    academic = read(STAGE / "academic-metadata.json")
    need(academic["source_commit"] == stage.COMMIT
         and academic["source_module"] == stage.SOURCE_MODULE
         and academic["platform_module"] == stage.PLATFORM_MODULE
         and academic["source_sha256"] == stage.SOURCE_SHA256
         and academic["source_lines"] == [15, 19]
         and academic["declarations"] == stage.NAMES,
         "collisionConstant academic source identity differs")
    need("does not establish the determinant-contradiction argument"
         in academic["mathematical_role"],
         "collisionConstant metadata overstates the provider scope")
    metadata = {
        "definition_title": academic["definition_title"],
        "natural_language_statement": (
            academic["natural_language_statement"] + "\n\n" + academic["mathematical_role"]
        ),
        "tags": academic["tags"],
        "source": academic["source"],
        "explanation": academic["explanation"],
    }
    need(set(metadata) == METADATA_FIELDS, "Definition metadata schema differs")

    provider = STAGE / stage.PROVIDER_FILE
    definition_bytes = provider.read_bytes()
    need(sha(provider) == json.loads((STAGE / "c1.json").read_text(encoding="utf-8"))["output_sha256"],
         "Definition provider differs from its compiler manifest")
    need(b"sorry" not in definition_bytes, "Definition upload contains sorry")
    payload = {
        "definition_name": DEFINITION_NAME,
        "definition_title": metadata["definition_title"],
        "definition": definition_bytes.decode("utf-8"),
        "natural_language_statement": metadata["natural_language_statement"],
        "source": metadata["source"],
        "tags": metadata["tags"],
        "env": ENV,
        "private": False,
    }
    need(set(payload) == {"definition_name", "definition_title", "definition",
                          "natural_language_statement", "source", "tags", "env", "private"},
         "submit-definition payload schema differs")
    need(payload["definition"].encode("utf-8") == definition_bytes,
         "Definition JSON string does not round-trip to exact provider bytes")
    payload_bytes = encode(payload, pretty=False)
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap7-collision-constant-definition-publication-manifest",
        "definition_name": DEFINITION_NAME,
        "definition_module": stage.PLATFORM_MODULE,
        "provided_names": stage.NAMES,
        "environment": ENV,
        "visibility": "public",
        "source_commit": stage.COMMIT,
        "source_module": stage.SOURCE_MODULE,
        "provider_source": task_rel(provider),
        "provider_source_sha256": sha(provider),
        "academic_metadata_sha256": sha(STAGE / "academic-metadata.json"),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "payload_sha256": sha_bytes(payload_bytes),
        "uploaded_definition_sha256": sha_bytes(payload["definition"].encode("utf-8")),
        "definition_bytes_equal_provider_source": True,
        "route": "/submit-definition",
        "expected_readback_status": "Definition",
        "proposal_status": "Draft",
        "submission_ready": False,
    }
    return provider, definition_bytes, metadata, payload, payload_bytes, manifest


def replay_certificate(cert):
    need(set(cert) == CERT_FIELDS, "Actual collisionConstant consumer schema differs")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap7-collision-constant-actual-provider-validation-v2",
         "collisionConstant certificate identity differs")
    need(cert["source_commit"] == stage.COMMIT
         and cert["source_module"] == stage.SOURCE_MODULE
         and cert["platform_module"] == stage.PLATFORM_MODULE
         and cert["provided_names"] == stage.NAMES,
         "collisionConstant certificate source/module domain differs")
    need(cert["validated"] is True and cert["Lean_started_by_consumer"] is False
         and cert["API_used"] is False and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft" and cert["Std3_only"] is True
         and cert["source_and_generated_types_equal"] is True
         and cert["definition_values_equal_and_exported"] is True
         and cert["theorem_values_null"] is True,
         "collisionConstant certificate state/equality gates differ")
    need(cert["provider_source_sha256"] == sha(STAGE / stage.PROVIDER_FILE)
         and cert["preparation_sha256"] == sha(STAGE / "preparation.json"),
         "collisionConstant certificate stage pins differ")
    preparation = read(STAGE / "preparation.json")
    provenance = cert["consumer_provenance"]
    original_consumer = Path(consumer.ORIGINAL_CONSUMER)
    need(set(provenance) == {"active_consumer_path", "active_consumer_sha256",
                             "original_staged_consumer_path",
                             "original_staged_consumer_sha256", "change"},
         "collisionConstant consumer provenance shape differs")
    need(provenance["active_consumer_path"] == task_rel(Path(consumer.__file__))
         and provenance["active_consumer_sha256"] == sha(Path(consumer.__file__))
         and provenance["original_staged_consumer_path"] == task_rel(original_consumer)
         and provenance["original_staged_consumer_sha256"] == sha(original_consumer),
         "collisionConstant active/original consumer provenance differs")
    need(preparation["input_hashes"][task_rel(original_consumer)] == sha(original_consumer),
         "Frozen stage no longer pins the original consumer")
    need(cert["compiler_manifest_sha256"]
         == {f"c{i}.json": sha(STAGE / f"c{i}.json") for i in range(1, 4)},
         "collisionConstant compiler-manifest pins differ")
    need(set(cert["preflights"]) == set(preparation["order"][:3]),
         "collisionConstant actual preflight domain differs")
    modes = ["emit-olean", "modecheck", "modecheck"]
    for index, (filename, mode) in enumerate(zip(preparation["order"][:3], modes), 1):
        source = STAGE / filename
        module = stage.PLATFORM_MODULE if index == 1 else Path(filename).stem
        current = context.record(source, STAGE / f"c{index}.json", mode, module, STAGE)
        need(current == cert["preflights"][filename],
             "collisionConstant actual context.record changed: " + filename)
    olean = TASK / cert["provider_olean"]
    need(olean.is_file() and sha(olean) == cert["provider_olean_sha256"],
         "collisionConstant provider OLean changed")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "collisionConstant implementation changed: " + path)
    for path, expected in cert["output_json_sha256"].items():
        need(sha(TASK / path) == expected, "collisionConstant full-CI output changed: " + path)


def artifacts():
    static = static_artifacts()
    need(CERT.is_file(), "strict collisionConstant provider certificate is pending")
    cert = read(CERT)
    replay_certificate(cert)
    return (*static, cert)


def pins(provider, definition_bytes, metadata, payload_bytes, manifest, cert):
    return {
        "schema_version": 1,
        "artifact_kind": "ap7-collision-constant-definition-publication-preparation",
        "offline_prepare_only": True,
        "publisher_script_sha256": sha(Path(definition_driver.__file__)),
        "offline_wrapper_sha256": sha(SELF),
        "online_wrapper_sha256": sha(ONLINE),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "definition_name": DEFINITION_NAME,
        "definition_module": stage.PLATFORM_MODULE,
        "environment": ENV,
        "visibility": "public",
        "metadata_sha256": sha_bytes(encode(metadata)),
        "payload_sha256": sha_bytes(payload_bytes),
        "payload_encoding": "Exact UTF-8 JSON bytes saved to publish-payload.json and sent unchanged",
        "wire_body_sha256": sha_bytes(payload_bytes),
        "bundle_source_sha256": sha(provider),
        "uploaded_definition_sha256": sha_bytes(definition_bytes),
        "uploaded_definition_bytes": len(definition_bytes),
        "definition_bytes_equal_bundle_source": definition_bytes == provider.read_bytes(),
        "bundle_manifest_sha256": sha_bytes(encode(manifest)),
        "validation_sha256": sha(CERT),
        "source_commit": stage.COMMIT,
        "preflight_count": len(cert["preflights"]),
        "max_preflight_seconds": cert["max_file_seconds"],
        "olean_sha256": cert["provider_olean_sha256"],
        "kernel_type_value_snapshots": cert["output_json_sha256"],
        "route": "/submit-definition",
        "expected_readback_status": "Definition",
        "at_most_once_policy": "durable publish_intent before POST; never repeat a recorded intent",
        "api_used": False,
        "proposal_status": "Draft",
        "submission_ready": False,
    }


def pending():
    provider, definition_bytes, metadata, payload, payload_bytes, manifest = static_artifacts()
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "publish-payload.json", payload_bytes)
    exact(DEST / "wire-definition-source.lean", definition_bytes)
    exact(DEST / "manifest.json", encode(manifest))
    return {"prepared": True, "validation_pending": not CERT.is_file(),
            "network_used": False, "proposal_status": "Draft",
            "payload_sha256": sha_bytes(payload_bytes)}


def prepare():
    provider, definition_bytes, metadata, payload, payload_bytes, manifest, cert = artifacts()
    frozen = pins(provider, definition_bytes, metadata, payload_bytes, manifest, cert)
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "publish-payload.json", payload_bytes)
    exact(DEST / "wire-definition-source.lean", definition_bytes)
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "prepare-record.json", encode(frozen))
    return {"prepared": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": frozen["payload_sha256"]}


def check():
    provider, definition_bytes, metadata, payload, payload_bytes, manifest, cert = artifacts()
    frozen = pins(provider, definition_bytes, metadata, payload_bytes, manifest, cert)
    need((DEST / "metadata.json").read_bytes() == encode(metadata)
         and (DEST / "publish-payload.json").read_bytes() == payload_bytes
         and (DEST / "wire-definition-source.lean").read_bytes() == definition_bytes
         and (DEST / "manifest.json").read_bytes() == encode(manifest)
         and (DEST / "validation.json").read_bytes() == CERT.read_bytes()
         and (DEST / "prepare-record.json").read_bytes() == encode(frozen),
         "Frozen collisionConstant Definition publication evidence differs")
    need(read(DEST / "publish-payload.json") == payload,
         "Saved Definition payload no longer decodes to the reviewed object")
    return {"checked": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": frozen["payload_sha256"]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-pending", action="store_true")
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = pending() if args.prepare_pending else prepare() if args.prepare_only else check()
    print(json.dumps(result, ensure_ascii=False, indent=2))
