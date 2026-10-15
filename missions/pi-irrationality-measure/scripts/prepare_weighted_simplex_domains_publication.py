"""Freeze either AP9 foundational Definition publication without networking."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_weighted_simplex_domains_existing as consumer
import publish_closed_definition_bundle as definition_driver
import stage_weighted_simplex_domains_providers as stage


TASK, ROOT = stage.TASK, stage.ROOT
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_weighted_simplex_domains_definitions.py"
ENV = definition_driver.ENV
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value): return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
def need(ok, message):
    if not ok: raise ValueError(message)


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen AP9 Definition publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def definition_name(c):
    prefix = "Definitions.Def_"
    need(c["platform_module"].startswith(prefix), "AP9 platform Definition module prefix differs")
    return c["platform_module"][len(prefix):]


def static_artifacts(key):
    stage.check_only(key)
    c = stage.config(key); root = c["stage"]; prep = read(root / "preparation.json")
    academic = read(root / "academic-metadata.json")
    need(set(academic) == {"definition_title", "natural_language_statement", "source",
                           "source_commit", "source_url", "tags"},
         "AP9 academic metadata schema differs")
    need(academic["source_commit"] == stage.COMMIT
         and academic["source_url"] in academic["source"]
         and prep["source_commit"] == stage.COMMIT
         and prep["source_module"] == c["source_module"]
         and prep["platform_module"] == c["platform_module"]
         and prep["provided_names"] == c["names"]
         and prep["provider_file"] == c["provider_file"],
         "AP9 academic/source/module identity differs")
    need(prep["order"] == [c["provider_file"], stage.SOURCE_SNAPSHOT, stage.GENERATED_SNAPSHOT]
         and [read(root / f"c{i}.json")["imports"] for i in range(1, 4)] ==
         [c["imports"], ["Lean", c["source_module"]], ["Lean", c["platform_module"]]],
         "AP9 ordered compiler/import contract differs")
    provider = root / c["provider_file"]
    raw = provider.read_bytes()
    need(sha(provider) == read(root / "c1.json")["output_sha256"]
         and b"sorry" not in raw and b"theorem " not in raw,
         "AP9 Definition provider differs, contains sorry, or contains a theorem")
    metadata = {
        "definition_title": academic["definition_title"],
        "natural_language_statement": academic["natural_language_statement"],
        "source": academic["source"],
        "tags": academic["tags"],
    }
    payload = {
        "definition_name": definition_name(c),
        "definition_title": metadata["definition_title"],
        "definition": raw.decode("utf-8"),
        "natural_language_statement": metadata["natural_language_statement"],
        "source": metadata["source"],
        "tags": metadata["tags"],
        "env": ENV,
        "private": False,
    }
    payload_bytes = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    need(payload["definition"].encode("utf-8") == raw,
         "AP9 JSON Definition body does not round-trip to exact provider bytes")
    cert_path = root / "actual-provider-validation.json"
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap9-foundational-definition-publication-manifest",
        "provider_key": key,
        "definition_name": payload["definition_name"],
        "definition_module": c["platform_module"],
        "provided_names": c["names"],
        "environment": ENV,
        "visibility": "public",
        "source_commit": stage.COMMIT,
        "source_module": c["source_module"],
        "source_url": academic["source_url"],
        "provider_source": stage.rel(provider),
        "provider_source_sha256": sha(provider),
        "stage_preparation_sha256": sha(root / "preparation.json"),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "payload_sha256": sha_bytes(payload_bytes),
        "uploaded_definition_sha256": sha_bytes(payload["definition"].encode("utf-8")),
        "definition_bytes_equal_provider_source": True,
        "route": "/submit-definition",
        "expected_readback_status": "Definition",
        "validated": cert_path.is_file(),
        "submission_ready": False,
        "proposal_status": "Draft",
    }
    return c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path


def replay_certificate(key, c, root, prep, cert):
    need(consumer.validate(key) == cert,
         "AP9 certificate differs from the strict saved-evidence consumer replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap9-foundational-actual-provider-validation"
         and cert["source_commit"] == stage.COMMIT
         and cert["source_module"] == c["source_module"]
         and cert["platform_module"] == c["platform_module"]
         and cert["provided_names"] == c["names"],
         "AP9 certificate identity/source domain differs")
    need(cert["validated"] is True and cert["Lean_started_by_consumer"] is False
         and cert["API_used"] is False and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft" and cert["Std3_only"] is True
         and cert["source_and_generated_types_equal"] is True
         and cert["definition_values_equal_and_exported"] is True
         and cert["contains_theorems"] is False,
         "AP9 certificate state/type/value/axiom gates differ")
    need(cert["provider_source_sha256"] == sha(root / c["provider_file"])
         and cert["preparation_sha256"] == sha(root / "preparation.json")
         and cert["compiler_manifest_sha256"] ==
         {f"c{i}.json": sha(root / f"c{i}.json") for i in range(1, 4)},
         "AP9 certificate stage pins differ")
    need(set(cert["preflights"]) == set(prep["order"])
         and 0 < cert["max_file_seconds"] <= 300,
         "AP9 exact three-preflight domain or budget differs")
    need(set(cert["actual_owners"]) == {"source", "generated"}
         and cert["actual_owners"]["source"] ==
         {name: c["source_module"] for name in c["names"]}
         and cert["actual_owners"]["generated"] ==
         {name: c["platform_module"] for name in c["names"]},
         "AP9 actual source/generated module owners differ")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP9 implementation changed: " + path)
    for path, expected in cert["output_json_sha256"].items():
        need(sha(TASK / path) == expected, "AP9 full-CI output changed: " + path)
    olean = TASK / cert["provider_olean"]
    need(olean.is_file() and sha(olean) == cert["provider_olean_sha256"],
         "AP9 provider OLean changed")


def artifacts(key):
    static = static_artifacts(key)
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path = static
    need(cert_path.is_file(), "Actual AP9 " + key + " validation certificate is pending")
    cert = read(cert_path); replay_certificate(key, c, root, prep, cert)
    return (*static, cert)


def api_review_pins():
    manifest = read(API_REVIEW / "manifest.json")
    docs = {x["name"]: x["sha256"] for x in manifest["documents"]}
    need(manifest["official_tag"] == "v0.12.4"
         and manifest["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and sha(API_REVIEW / "references/contribute.md") == docs["references/contribute.md"],
         "Reviewed official submit-definition API document differs")
    return {"official_tag": manifest["official_tag"],
            "official_commit": manifest["official_commit"],
            "manifest_sha256": sha(API_REVIEW / "manifest.json"),
            "contribute_sha256": docs["references/contribute.md"]}


def pins(key, c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert):
    return {
        "schema_version": 1,
        "artifact_kind": "ap9-foundational-definition-publication-preparation",
        "provider_key": key,
        "offline_prepare_only": True,
        "publisher_script_sha256": sha(Path(definition_driver.__file__)),
        "offline_wrapper_sha256": sha(SELF),
        "online_wrapper_sha256": sha(ONLINE),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "definition_name": definition_name(c),
        "definition_module": c["platform_module"],
        "environment": ENV,
        "visibility": "public",
        "metadata_sha256": sha_bytes(encode(metadata)),
        "payload_sha256": sha_bytes(payload_bytes),
        "payload_encoding": "Exact UTF-8 JSON bytes saved and sent unchanged",
        "wire_body_sha256": sha_bytes(payload_bytes),
        "bundle_source_sha256": sha(provider),
        "uploaded_definition_sha256": sha_bytes(raw),
        "uploaded_definition_bytes": len(raw),
        "definition_bytes_equal_bundle_source": True,
        "bundle_manifest_sha256": sha_bytes(encode(manifest)),
        "stage_preparation_sha256": sha(root / "preparation.json"),
        "validation_sha256": sha(cert_path),
        "source_commit": stage.COMMIT,
        "ordered_imports": {name: read(root / f"c{i}.json")["imports"]
                            for i, name in enumerate(prep["order"], 1)},
        "compiler_manifest_sha256": cert["compiler_manifest_sha256"],
        "stage_input_hashes": prep["input_hashes"],
        "preflight_count": len(cert["preflights"]),
        "max_preflight_seconds": cert["max_file_seconds"],
        "olean_sha256": cert["provider_olean_sha256"],
        "kernel_type_value_snapshots": cert["output_json_sha256"],
        "route": "/submit-definition",
        "expected_readback_status": "Definition",
        "official_api_review": api_review_pins(),
        "at_most_once_policy": "durable publish_intent before POST; never repeat a recorded intent",
        "API_used": False,
        "submission_ready": False,
        "proposal_status": "Draft",
    }


def pending(key):
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path = static_artifacts(key)
    dest = root / "publication"
    exact(dest / "metadata.json", encode(metadata))
    exact(dest / "publish-payload.json", payload_bytes)
    exact(dest / "wire-definition-source.lean", raw)
    record = {"schema_version": 1,
              "artifact_kind": "ap9-foundational-definition-pending-publication",
              "provider_key": key, "definition_name": payload["definition_name"],
              "publication_manifest_sha256": sha_bytes(encode(manifest)),
              "stage_preparation_sha256": sha(root / "preparation.json"),
              "metadata_sha256": sha_bytes(encode(metadata)),
              "payload_sha256": sha_bytes(payload_bytes),
              "provider_source_sha256": sha(provider),
              "strict_validation_pending": not cert_path.is_file(),
              "network_used": False, "API_used": False,
              "submission_ready": False, "proposal_status": "Draft"}
    exact(dest / "pending-preparation.json", encode(record))
    return {"prepared": True, "provider": key, "validation_pending": not cert_path.is_file(),
            "network_used": False, "payload_sha256": record["payload_sha256"]}


def prepare(key):
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path, cert = artifacts(key)
    dest = root / "publication"
    frozen = pins(key, c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert)
    exact(dest / "manifest.json", encode(manifest)); exact(dest / "validation.json", cert_path.read_bytes())
    exact(dest / "metadata.json", encode(metadata)); exact(dest / "publish-payload.json", payload_bytes)
    exact(dest / "wire-definition-source.lean", raw); exact(dest / "prepare-record.json", encode(frozen))
    return {"prepared": True, "provider": key, "network_used": False,
            "payload_sha256": frozen["payload_sha256"], "proposal_status": "Draft"}


def check(key):
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path, cert = artifacts(key)
    dest = root / "publication"
    frozen = pins(key, c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert)
    need((dest / "manifest.json").read_bytes() == encode(manifest)
         and (dest / "validation.json").read_bytes() == cert_path.read_bytes()
         and (dest / "metadata.json").read_bytes() == encode(metadata)
         and (dest / "publish-payload.json").read_bytes() == payload_bytes
         and (dest / "wire-definition-source.lean").read_bytes() == raw
         and (dest / "prepare-record.json").read_bytes() == encode(frozen),
         "Frozen AP9 Definition publication evidence differs")
    need(read(dest / "publish-payload.json") == payload,
         "Saved AP9 Definition payload no longer decodes to the reviewed object")
    return {"checked": True, "provider": key, "network_used": False,
            "payload_sha256": frozen["payload_sha256"], "proposal_status": "Draft"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider", choices=list(stage.CONFIGS), required=True)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-pending", action="store_true")
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = pending(args.provider) if args.prepare_pending else prepare(args.provider) if args.prepare_only else check(args.provider)
    print(json.dumps(result, ensure_ascii=False, indent=2))
