"""Prepare the AP19 four-Def package under its exact six-CI v5 contract."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_analytic_remainder_data_auto_ci_v5 as consumer
import prepare_analytic_remainder_data_publication as preimage


TASK, ROOT = preimage.TASK, preimage.ROOT
base, probe = consumer.probe.base, consumer.probe
STAGE = base.STAGE
CERT = consumer.CERT
DEST = STAGE / "publication-v4"
KEY = "remainder"
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_analytic_remainder_data_definition_auto_ci_v5.py"
FROZEN_OFFLINE_V4 = TASK / "scripts/prepare_analytic_remainder_data_publication_auto_ci_v4.py"
FROZEN_ONLINE_V4 = TASK / "scripts/publish_analytic_remainder_data_definition_auto_ci_v4.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("utf-8")


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen AP19 auto-CI publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def resolved(path):
    p = Path(path)
    return p if p.is_absolute() else TASK / p


def preflight_hashes(cert):
    found = {}
    rows = list(cert["original_preflights"].values()) + [cert["source_automatic_preflight"]]
    for row in rows:
        found[row["record"]] = row["record_sha256"]
        for key in ("source", "manifest", "log"):
            path = consumer.context.file(row["data"][key])
            found[str(path)] = sha(path)
    return dict(sorted(found.items()))


def dependency_oleans(cert):
    found = {}
    rows = list(cert["original_preflights"].values()) + [cert["source_automatic_preflight"]]
    for row in rows:
        for dep in row["data"]["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"],
                 "AP19 actual imported OLean changed during compilation")
            found[dep["path"]] = dep["sha256_before"]
    return dict(sorted(found.items()))


def api_review():
    review = read(API_REVIEW / "manifest.json")
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and all(sha(API_REVIEW / name) == expected for name, expected in docs.items()),
         "AP19 reviewed official API documents differ")
    return {"official_tag": review["official_tag"],
            "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW / "manifest.json"), "documents": docs}


def replay(cert):
    # Root already performed the single complete v5 replay that created this
    # immutable certificate.  Publication preparation checks the exact report
    # bytes and every certificate-bound artifact without repeating that replay.
    need(consumer.encode(cert) == CERT.read_bytes(),
         "AP19 v5 certificate encoding differs from the completed strict replay")
    auto_names = probe.actual_auto_names()
    pairs = cert["actual_source_generated_closed_Prop_autoCI_pairs"]
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] ==
             "ap19-analytic-remainder-four-Def-autoCI-derived-validation-v5"
         and cert["validated"] is True and cert["Std3_only"] is True
         and cert["provided_names"] == base.NAMES
         and cert["primary_Def_full_types_values_equal"] is True
         and cert["original_three_contexts_reused_unmodified"] is True
         and cert["actual_owned_CI_names"] == sorted(base.NAMES + auto_names)
         and [row["name"] for row in pairs] == auto_names
         and all(row["closed_Prop"] is True
                 and row["full_type_direct_refs_Std3_equal"] is True
                 and row["source_owner"] == probe.SOURCE_MODULE
                 and row["generated_owner"] == base.PLATFORM_MODULE
                 and set(row["axioms"]) <= preimage.STD3
                 for row in pairs)
         and cert["original_consumer_inventory_guard_rejected_two_observed_extra_CIs"] is True
         and cert["original_emitted_provider_olean_sha256"] ==
             sha(TASK / cert["original_emitted_provider_olean"])
         and cert["source_automatic_json_sha256"] == sha(probe.STAGE / probe.SOURCE_JSON)
         and cert["generated_owned_inventory_sha256"] ==
             sha(base.STAGE / base.INVENTORY_JSON)
         and 0 < cert["max_file_seconds"] <= 300
         and cert["submission_ready"] is False and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False,
         "AP19 exact four-Def/six-CI v5 contract differs")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP19 v5 implementation changed: " + path)


def static_artifacts(cert):
    config, prep, provider, raw, metadata, payload, payload_bytes, old_manifest = preimage.static()
    need(config["names"] == base.NAMES and provider == base.STAGE / base.PROVIDER_FILE
         and sha_bytes(raw) == "2de7c9206ef21c36fba00acb47fd2c3cc3319ea85d3e308aa98b22f1d383f319",
         "AP19 original four-Def payload source changed")
    manifest = dict(old_manifest)
    manifest.update({
        "artifact_kind": "ap19-analytic-remainder-four-Def-autoCI-v5-publication-manifest",
        "validated": True,
        "validation_contract": "four original full Def CIs plus two exact closed Prop auto CIs",
        "actual_owned_CI_names": cert["actual_owned_CI_names"],
        "actual_source_generated_closed_Prop_autoCI_pairs":
            cert["actual_source_generated_closed_Prop_autoCI_pairs"],
    })
    return config, prep, provider, raw, metadata, payload, payload_bytes, manifest


def prepare():
    need(CERT.is_file(), "AP19 genuine auto-CI v5 certificate is pending")
    cert = read(CERT)
    replay(cert)
    config, prep, provider, raw, metadata, payload, payload_bytes, manifest = static_artifacts(cert)
    probe_prep = read(probe.STAGE / "preparation.json")
    base_json = {base.rel(base.STAGE / name): sha(base.STAGE / name)
                 for name in [base.SOURCE_JSON, base.GENERATED_JSON, base.INVENTORY_JSON]}
    pins = {"schema_version": 1,
        "artifact_kind": "ap19-analytic-remainder-four-Def-autoCI-v5-publication-preparation",
        "provider_key": "remainder",
        "definition_name": preimage.definition_name(config),
        "definition_module": config["platform_module"],
        "environment": preimage.ENV, "visibility": "public",
        "offline_wrapper_sha256": sha(SELF), "online_wrapper_sha256": sha(ONLINE),
        "frozen_offline_v4_preimage_sha256": sha(FROZEN_OFFLINE_V4),
        "frozen_online_v4_preimage_sha256": sha(FROZEN_ONLINE_V4),
        "payload_builder_preimage_sha256": sha(preimage.SELF),
        "publisher_script_sha256": sha(Path(preimage.payload_driver.__file__)),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "base_stage_producer_sha256": sha(Path(base.__file__)),
        "auto_ci_probe_producer_sha256": sha(Path(probe.__file__)),
        "strict_v5_consumer_sha256": sha(Path(consumer.__file__)),
        "base_stage_preparation_sha256": sha(base.STAGE / "preparation.json"),
        "auto_ci_probe_preparation_sha256": sha(probe.STAGE / "preparation.json"),
        "validation_sha256": sha(CERT),
        "manifest_sha256": sha_bytes(encode(manifest)),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "payload_sha256": sha_bytes(payload_bytes),
        "provider_source_sha256": sha(provider),
        "uploaded_definition_sha256": sha_bytes(raw),
        "base_stage_input_hashes": prep["input_hashes"],
        "auto_ci_probe_input_hashes": probe_prep["input_hashes"],
        "base_compiler_manifest_sha256":
            {f"c{i}.json": sha(base.STAGE / f"c{i}.json") for i in range(1, 4)},
        "auto_ci_probe_manifest_sha256": sha(probe.STAGE / probe.MANIFEST),
        "preflight_artifact_sha256": preflight_hashes(cert),
        "dependency_olean_sha256": dependency_oleans(cert),
        "implementation_hashes": cert["implementation_hashes"],
        "base_kernel_json_sha256": base_json,
        "source_automatic_json_sha256": cert["source_automatic_json_sha256"],
        "generated_owned_inventory_sha256": cert["generated_owned_inventory_sha256"],
        "provider_olean": cert["original_emitted_provider_olean"],
        "provider_olean_sha256": cert["original_emitted_provider_olean_sha256"],
        "actual_owned_CI_names": cert["actual_owned_CI_names"],
        "actual_source_generated_closed_Prop_autoCI_pairs":
            cert["actual_source_generated_closed_Prop_autoCI_pairs"],
        "official_api_review": api_review(),
        "route": "/submit-definition", "expected_readback_status": "Definition",
        "one_complete_strict_replay_performed_before_publication_preparation": True,
        "strict_v5_certificate_reused_by_complete_hash_gate": True,
        "publication_preparation_repeats_strict_consumer": False,
        "subsequent_HTTP_guards_are_hash_only": True,
        "durable_policy": "write intent before POST; never repeat an uncertain POST; poll only a known id",
        "API_used": False, "submission_ready": False, "proposal_status": "Draft"}
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "publish-payload.json", payload_bytes)
    exact(DEST / "wire-definition-source.lean", raw)
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "provider": "remainder", "network_used": False,
            "strict_v5_certificate_reused_by_complete_hash_gate": True,
            "payload_sha256": pins["payload_sha256"], "proposal_status": "Draft"}


def hash_gate(pins):
    direct = {SELF: pins["offline_wrapper_sha256"], ONLINE: pins["online_wrapper_sha256"],
        FROZEN_OFFLINE_V4: pins["frozen_offline_v4_preimage_sha256"],
        FROZEN_ONLINE_V4: pins["frozen_online_v4_preimage_sha256"],
        preimage.SELF: pins["payload_builder_preimage_sha256"],
        Path(preimage.payload_driver.__file__): pins["publisher_script_sha256"],
        ROOT / "scripts/p2m_api.py": pins["api_client_sha256"],
        Path(base.__file__): pins["base_stage_producer_sha256"],
        Path(probe.__file__): pins["auto_ci_probe_producer_sha256"],
        Path(consumer.__file__): pins["strict_v5_consumer_sha256"],
        base.STAGE / "preparation.json": pins["base_stage_preparation_sha256"],
        probe.STAGE / "preparation.json": pins["auto_ci_probe_preparation_sha256"],
        CERT: pins["validation_sha256"],
        base.STAGE / base.PROVIDER_FILE: pins["provider_source_sha256"],
        probe.STAGE / probe.SOURCE_JSON: pins["source_automatic_json_sha256"],
        base.STAGE / base.INVENTORY_JSON: pins["generated_owned_inventory_sha256"]}
    for path, expected in direct.items():
        need(sha(path) == expected, "AP19 frozen v5 evidence changed: " + str(path))
    for collection in (pins["base_stage_input_hashes"], pins["auto_ci_probe_input_hashes"],
                       pins["implementation_hashes"], pins["base_kernel_json_sha256"],
                       pins["preflight_artifact_sha256"], pins["dependency_olean_sha256"]):
        for path, expected in collection.items():
            need(sha(resolved(path)) == expected, "AP19 frozen v5 input changed: " + path)
    for name, expected in pins["base_compiler_manifest_sha256"].items():
        need(sha(base.STAGE / name) == expected, "AP19 base manifest changed: " + name)
    need(sha(probe.STAGE / probe.MANIFEST) == pins["auto_ci_probe_manifest_sha256"]
         and sha(TASK / pins["provider_olean"]) == pins["provider_olean_sha256"],
         "AP19 c4 manifest/provider OLean changed")
    need((DEST / "preparation.json").read_bytes() == encode(pins)
         and sha(DEST / "manifest.json") == pins["manifest_sha256"]
         and sha(DEST / "validation.json") == pins["validation_sha256"]
         and sha(DEST / "metadata.json") == pins["metadata_sha256"]
         and sha(DEST / "publish-payload.json") == pins["payload_sha256"]
         and sha(DEST / "wire-definition-source.lean") == pins["uploaded_definition_sha256"],
         "AP19 frozen v5 publication artifacts changed")
    need(api_review() == pins["official_api_review"], "AP19 API review pins changed")


def frozen():
    pins = read(DEST / "preparation.json")
    hash_gate(pins)
    return pins, read(DEST / "metadata.json"), read(DEST / "publish-payload.json"), \
        (DEST / "publish-payload.json").read_bytes()


def check():
    result = prepare()
    frozen()
    return {"checked": True, **{k: v for k, v in result.items() if k != "prepared"}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider", choices=["remainder"], default="remainder")
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare_only else check(),
                     ensure_ascii=False, indent=2))
