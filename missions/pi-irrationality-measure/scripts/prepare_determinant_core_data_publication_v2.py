"""Freeze the AP10 determinant Definition with its bounded proof-helper certificate."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import certify_determinant_core_data_helper_existing as consumer
import prepare_core_parent_data_publication as base
import publish_closed_definition_bundle as driver
import stage_determinant_data_helper_pair as helper


TASK, ROOT = base.TASK, base.ROOT
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_determinant_core_data_definitions_v2.py"
KEY = "determinant"
DEST_NAME = "publication-helper-v2"


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen determinant-v2 publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def static():
    values = base.static(KEY)
    c, root, prep, provider, raw, metadata, payload, payload_bytes, old_manifest, _ = values
    old = root / "publication"
    base.need((old / "metadata.json").read_bytes() == base.encode(metadata)
              and (old / "publish-payload.json").read_bytes() == payload_bytes
              and (old / "wire-definition-source.lean").read_bytes() == raw,
              "Frozen determinant pending publication bytes changed")
    pending = base.read(old / "pending-preparation.json")
    base.need(pending["provider_key"] == KEY
              and pending["payload_sha256"] == base.sha_bytes(payload_bytes)
              and pending["provider_source_sha256"] == base.sha(provider)
              and pending["strict_validation_pending"] is True,
              "Original determinant pending-publication identity differs")
    cert_path = consumer.CERT
    manifest = dict(old_manifest)
    manifest.update({
        "artifact_kind": "ap10-determinant-proof-helper-definition-publication-manifest",
        "validation_adapter": base.stage.rel(Path(consumer.__file__)),
        "validation_sha256": base.sha(cert_path) if cert_path.is_file() else None,
        "ordinary_pending_payload_sha256": pending["payload_sha256"],
        "provider_and_payload_bytes_preserved": True,
        "validated": cert_path.is_file(),
    })
    return c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path


def replay(c, root, prep, cert_path):
    cert = base.read(cert_path)
    base.need(consumer.validate() == cert,
              "Determinant-v2 certificate differs from strict saved-evidence replay")
    pair = cert["certified_actual_helper_pair"]
    expected_norm = {"constant_pairs": 1, "parent_values": 2,
                     "types_modified": False, "source_files_modified": False}
    base.need(cert["schema_version"] == 1
              and cert["artifact_kind"] == "ap10-determinant-certified-proof-helper-provider-validation"
              and cert["source_commit"] == base.stage.COMMIT
              and cert["source_module"] == c["source_module"]
              and cert["platform_module"] == c["platform_module"]
              and cert["provided_names"] == c["names"],
              "Determinant-v2 certificate identity differs")
    base.need(cert["validated"] is True
              and cert["Lean_started_by_consumer"] is False
              and cert["API_used"] is False
              and cert["submission_ready"] is False
              and cert["proposal_status"] == "Draft"
              and cert["Std3_only"] is True
              and cert["source_and_generated_types_equal"] is True
              and cert["contains_theorems"] is False,
              "Determinant-v2 actual type/axiom/state gates differ")
    base.need(cert["raw_definition_values_equal"] is False
              and cert["definition_values_equal_after_certified_proof_CI_substitution"] is True
              and cert["raw_equal_definition_count"] == 12
              and cert["changed_only_by_actual_proof_helper"] == helper.PARENTS
              and cert["original_source_and_generated_snapshot_bytes_preserved"] is True
              and cert["normalization_domain"] == expected_norm,
              "Determinant-v2 finite substitution domain differs")
    base.need(pair["source_name"] == helper.SOURCE_HELPER
              and pair["generated_name"] == helper.GENERATED_HELPER
              and pair["actual_closed_propositional_types_equal"] is True
              and pair["actual_full_proof_values_equal"] is True
              and set(pair["actual_witnesses"]) == {"source", "generated"},
              "Determinant-v2 actual helper pair differs")
    for side, expected_name in (("source", helper.SOURCE_HELPER),
                                ("generated", helper.GENERATED_HELPER)):
        witness = pair["actual_witnesses"][side]
        report = witness["actual_report"]
        base.need(report["helper"]["name"] == expected_name
                  and report["helper"]["closedType"] is True
                  and report["helper"]["closedValue"] is True
                  and report["helper"]["isProp"] is True
                  and [x["name"] for x in report["actualParentReferences"]] == helper.PARENTS
                  and base.sha(TASK / witness["output"]) == witness["output_sha256"]
                  and witness["preflight"]["data"]["success"] is True
                  and 0 < witness["preflight"]["data"]["seconds"] <= 300,
                  "Determinant-v2 helper witness differs: " + side)
    base.need(cert["provider_source_sha256"] == base.sha(root / c["provider_file"])
              and cert["preparation_sha256"] == base.sha(root / "preparation.json")
              and cert["compiler_manifest_sha256"] ==
                  {f"c{i}.json": base.sha(root / f"c{i}.json") for i in range(1, 4)}
              and set(cert["preflights"]) == set(prep["order"])
              and 0 < cert["max_file_seconds"] <= 300,
              "Determinant-v2 compiler evidence differs")
    base.need(cert["actual_owners"]["source"] ==
                  {n: c["source_module"] for n in c["names"]}
              and cert["actual_owners"]["generated"] ==
                  {n: c["platform_module"] for n in c["names"]},
              "Determinant-v2 actual owners differ")
    base.need(cert["ordinary_consumer_path"] == base.stage.rel(Path(base.consumer.__file__))
              and cert["ordinary_consumer_sha256"] == base.sha(Path(base.consumer.__file__))
              and base.sha(TASK / cert["difference_diagnosis"]) == cert["difference_diagnosis_sha256"],
              "Determinant-v2 ordinary-consumer or diagnosis evidence differs")
    for path, expected in cert["implementation_hashes"].items():
        base.need(base.sha(TASK / path) == expected,
                  "Determinant-v2 implementation changed: " + path)
    for path, expected in cert["output_json_sha256"].items():
        base.need(base.sha(TASK / path) == expected,
                  "Determinant-v2 full-CI output changed: " + path)
    base.need(base.sha(TASK / cert["provider_olean"]) == cert["provider_olean_sha256"],
              "Determinant-v2 provider OLean changed")
    if "preserved_strict_consumer_failure" in cert:
        failed = cert["preserved_strict_consumer_failure"]
        base.need(base.sha(TASK / failed["path"]) == failed["sha256"],
                  "Preserved strict-consumer failure evidence changed")
    return cert


def artifacts():
    values = static()
    cert_path = values[-1]
    base.need(cert_path.is_file(), "Actual determinant-v2 helper certificate is pending")
    cert = replay(values[0], values[1], values[2], cert_path)
    return (*values, cert)


def pins(c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert):
    old = root / "publication"
    return {
        "schema_version": 2,
        "artifact_kind": "ap10-determinant-proof-helper-definition-publication-preparation",
        "provider_key": KEY,
        "offline_prepare_only": True,
        "publisher_script_sha256": base.sha(Path(driver.__file__)),
        "ordinary_offline_wrapper_sha256": base.sha(Path(base.__file__)),
        "offline_wrapper_sha256": base.sha(SELF),
        "online_wrapper_sha256": base.sha(ONLINE),
        "api_client_sha256": base.sha(ROOT / "scripts/p2m_api.py"),
        "stage_producer_sha256": base.sha(Path(base.stage.__file__)),
        "ordinary_consumer_sha256": base.sha(Path(base.consumer.__file__)),
        "helper_stage_sha256": base.sha(Path(helper.__file__)),
        "strict_consumer_sha256": base.sha(Path(consumer.__file__)),
        "definition_name": base.name(c),
        "definition_module": c["platform_module"],
        "environment": base.ENV,
        "visibility": "public",
        "metadata_sha256": base.sha_bytes(base.encode(metadata)),
        "payload_sha256": base.sha_bytes(payload_bytes),
        "payload_encoding": "Exact UTF-8 JSON bytes saved and sent unchanged",
        "wire_body_sha256": base.sha_bytes(payload_bytes),
        "ordinary_pending_payload_sha256": base.sha(old / "publish-payload.json"),
        "bundle_source_sha256": base.sha(provider),
        "uploaded_definition_sha256": base.sha_bytes(raw),
        "uploaded_definition_bytes": len(raw),
        "definition_bytes_equal_bundle_source": True,
        "provider_and_payload_bytes_preserved": True,
        "bundle_manifest_sha256": base.sha_bytes(base.encode(manifest)),
        "stage_preparation_sha256": base.sha(root / "preparation.json"),
        "validation_sha256": base.sha(cert_path),
        "source_commit": base.stage.COMMIT,
        "ordered_imports": {n: base.read(root / f"c{i}.json")["imports"]
                            for i, n in enumerate(prep["order"], 1)},
        "compiler_manifest_sha256": cert["compiler_manifest_sha256"],
        "stage_input_hashes": prep["input_hashes"],
        "project_dependencies": prep["project_dependencies"],
        "actual_dependency_bindings": prep["actual_dependency_bindings"],
        "dependency_provider_evidence": prep["dependency_provider_evidence"],
        "preflight_count": len(cert["preflights"]) + 2,
        "max_preflight_seconds": cert["max_file_seconds"],
        "olean_sha256": cert["provider_olean_sha256"],
        "kernel_type_value_snapshots": cert["output_json_sha256"],
        "certified_actual_helper_pair": cert["certified_actual_helper_pair"],
        "normalization_domain": cert["normalization_domain"],
        "route": "/submit-definition",
        "expected_readback_status": "Definition",
        "official_api_review": base.api_review(),
        "at_most_once_policy": "durable publish_intent before POST; never repeat a recorded intent",
        "API_used": False,
        "submission_ready": False,
        "proposal_status": "Draft",
    }


def prepare():
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path, cert = artifacts()
    dest = root / DEST_NAME
    frozen = pins(c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert)
    exact(dest / "manifest.json", base.encode(manifest))
    exact(dest / "validation.json", cert_path.read_bytes())
    exact(dest / "metadata.json", base.encode(metadata))
    exact(dest / "publish-payload.json", payload_bytes)
    exact(dest / "wire-definition-source.lean", raw)
    exact(dest / "prepare-record.json", base.encode(frozen))
    return {"prepared": True, "provider": KEY, "network_used": False,
            "payload_sha256": frozen["payload_sha256"], "proposal_status": "Draft"}


def check():
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path, cert = artifacts()
    dest = root / DEST_NAME
    frozen = pins(c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert)
    base.need((dest / "manifest.json").read_bytes() == base.encode(manifest)
              and (dest / "validation.json").read_bytes() == cert_path.read_bytes()
              and (dest / "metadata.json").read_bytes() == base.encode(metadata)
              and (dest / "publish-payload.json").read_bytes() == payload_bytes
              and (dest / "wire-definition-source.lean").read_bytes() == raw
              and (dest / "prepare-record.json").read_bytes() == base.encode(frozen),
              "Frozen determinant-v2 publication evidence differs")
    base.need(base.read(dest / "publish-payload.json") == payload,
              "Saved determinant-v2 payload differs")
    return {"checked": True, "provider": KEY, "network_used": False,
            "payload_sha256": frozen["payload_sha256"], "proposal_status": "Draft"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare-only", action="store_true")
    group.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare_only else check(), ensure_ascii=False, indent=2))
