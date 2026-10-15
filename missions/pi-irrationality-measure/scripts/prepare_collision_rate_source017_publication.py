"""Prepare a complete-footer _source017 Draft payload from certified AP11 evidence.

Pure offline preparation. The old AP11 publication artifacts remain unchanged.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_collision_rate_source017_binding as binding
import prepare_grouped_collision_rate_publication as prior
import publish_standalone_platform_node as driver
import stage_collision_rate_source017_comparator as bridge


TASK, ROOT, STAGE = bridge.TASK, bridge.ROOT, bridge.STAGE
DEST = STAGE / "publication"
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_collision_rate_source017_node.py"
CERT = binding.CERT
PREVIOUS = prior.DEST


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(value):
    return driver.encode(value)


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def root_rel(path):
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def exact(path, raw):
    path = Path(path)
    if path.exists():
        need(path.read_bytes() == raw, "Frozen source017 publication artifact differs: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def artifacts():
    cert = binding.validate(write=False)
    need(CERT.is_file() and CERT.read_bytes() == binding.encode(cert),
         "Saved finite source017 naming certificate differs from strict replay")
    old_manifest = read(PREVIOUS / "manifest.json")
    old_pins = read(PREVIOUS / "preparation.json")
    prior.hash_gate(old_manifest, old_pins)
    old_metadata = read(PREVIOUS / "metadata.json")
    prep = read(bridge.PREP)
    need(old_metadata == prior.academic_metadata(prep)
         and old_metadata["theorem_name"] == bridge.ap11.TARGET,
         "Old AP11 academic math/source metadata changed")
    old_payload = read(PREVIOUS / "publish-payload.json")
    need(old_payload["problems"][0]["theorem_name"] == bridge.ap11.TARGET
         and sha(PREVIOUS / "publish-payload.json") == cert["old_incomplete_publish_payload_sha256"],
         "Original incomplete namespace-footer payload changed")

    audit = read(STAGE / bridge.AUDIT)
    comparator = STAGE / bridge.OUTPUT
    comparator_raw = comparator.read_bytes()
    old_wire = bridge.ORIGINAL_WIRE.read_bytes()
    need(comparator_raw == old_wire.replace(bridge.OLD_TOKEN, bridge.NEW_TOKEN, 1)
         and sha(comparator) == cert["new_comparator_sha256"],
         "New comparator is not the one-token original transformation")
    preamble = old_manifest["preamble"]
    old_formal = old_manifest["formal_statement"]
    need(old_wire.startswith((preamble + old_formal).encode())
         and old_formal.count(bridge.OLD_TOKEN.decode()) == 1,
         "Original frozen platform statement is not the exact proof preimage")
    footer = old_wire[len((preamble + old_formal).encode()):]
    need(footer == b"\n" + bridge.ap11.GROUP_FOOTERS[bridge.ap11.TARGET_MODULE]
         and sha_bytes(footer) == audit["namespace_closure_sha256"],
         "Source namespace closure differs")
    formal = old_formal.replace(bridge.OLD_TOKEN.decode(), bridge.NEW_TOKEN.decode(), 1) + footer.decode()
    need((preamble + formal).encode() == comparator_raw
         and sha_bytes(comparator_raw) == cert["renamed_platform_wire_sha256"],
         "Publish payload must assemble the complete compiled comparator")

    manifest = dict(old_manifest)
    manifest.update({
        "artifact_kind": "ap11-collision-rate-source017-complete-footer-publication-manifest",
        "theorem_name": bridge.PUBLIC_NAME,
        "formal_statement": formal,
        "statement": root_rel(comparator),
        "statement_sha256": sha(comparator),
        "platform_statement_assembly_sha256": sha(comparator),
        "comparator_namespace_suffix_sha256": sha_bytes(footer),
        "validation": root_rel(DEST / "validation.json"),
        "validation_sha256": sha(CERT),
        "proposal_status": "Draft", "submission_ready": False,
    })
    metadata = dict(old_metadata)
    metadata["theorem_name"] = bridge.PUBLIC_NAME
    need({k: v for k, v in metadata.items() if k != "theorem_name"} ==
         {k: v for k, v in old_metadata.items() if k != "theorem_name"},
         "Source mathematics/provenance metadata differs beyond platform name")
    payloads = driver.payloads(DEST, manifest, metadata)
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    verification = json.loads(payloads["verification-payload.json"])
    need(problem["theorem_name"] == bridge.PUBLIC_NAME
         and (problem["preamble"] + problem["formal_statement"]).encode() == comparator_raw
         and problem["formal_statement"].endswith(footer.decode())
         and problem["source"] == prep["source_url"]
         and verification["target_theorem_name"] == bridge.PUBLIC_NAME
         and verification["theorem_id"] is None
         and verification["file"]["utf8"].encode() == (bridge.AP11 / bridge.ap11.SOLUTION_OUTPUT).read_bytes()
         and verification["file"]["sha256"] == old_manifest["solution_sha256"],
         "Exact source017 publish/verify payload differs from compiled/proved artifacts")
    pins = {
        "schema_version": 1,
        "artifact_kind": "ap11-collision-rate-source017-publication-preparation",
        "theorem_name": bridge.PUBLIC_NAME,
        "environment": driver.ENV,
        "proposal_status": "Draft",
        "manifest_sha256": sha_bytes(encode(manifest)),
        "validation_sha256": sha(CERT),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "publisher_sha256": sha(Path(driver.__file__)),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "offline_wrapper_sha256": sha(SELF),
        "online_wrapper_sha256": sha(ONLINE),
        "naming_binding_consumer_sha256": sha(Path(binding.__file__)),
        "comparator_producer_sha256": sha(Path(bridge.__file__)),
        "old_publication_manifest_sha256": sha(PREVIOUS / "manifest.json"),
        "old_publication_preparation_sha256": sha(PREVIOUS / "preparation.json"),
        "old_publication_payload_sha256": sha(PREVIOUS / "publish-payload.json"),
        "authoritative_old_target_GET_sha256": sha(binding.GET),
        "new_comparator_sha256": sha(comparator),
        "new_comparator_manifest_sha256": sha(STAGE / bridge.MANIFEST),
        "new_comparator_sidecar_sha256": cert["new_comparator_preflight"]["record_sha256"],
        "new_comparator_log_sha256": cert["new_comparator_preflight"]["data"]["log_sha256"],
        "new_comparator_dependency_oleans": [
            {"module": d["module"], "path": d["path"], "sha256": d["sha256_before"]}
            for d in cert["new_comparator_preflight"]["data"]["dependency_oleans"]],
        "platform_statement_assembly_sha256": sha(comparator),
        "original_AP11_certificate_sha256": sha(bridge.CERT),
        "original_AP11_solution_olean_sha256": cert["original_AP11_solution_olean_sha256"],
        "original_AP11_publication_hash_gate_reused": True,
        "full_namespace_closure_in_formal_statement": True,
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "local_node_validated": True, "submission_ready": False,
        "full_tree_ready": False, "API_used": False,
    }
    return manifest, metadata, payloads, comparator_raw, pins


def hash_gate(manifest, frozen):
    need(read(DEST / "manifest.json") == manifest
         and sha_bytes(encode(manifest)) == frozen["manifest_sha256"]
         and sha(DEST / "validation.json") == frozen["validation_sha256"]
         and sha(DEST / "metadata.json") == frozen["metadata_sha256"],
         "Frozen source017 publication manifest/certificate/metadata changed")
    old_manifest = read(PREVIOUS / "manifest.json")
    old_pins = read(PREVIOUS / "preparation.json")
    prior.hash_gate(old_manifest, old_pins)
    direct = {
        SELF: "offline_wrapper_sha256", ONLINE: "online_wrapper_sha256",
        Path(binding.__file__): "naming_binding_consumer_sha256",
        Path(bridge.__file__): "comparator_producer_sha256",
        Path(driver.__file__): "publisher_sha256",
        ROOT / "scripts/p2m_api.py": "api_client_sha256",
        PREVIOUS / "manifest.json": "old_publication_manifest_sha256",
        PREVIOUS / "preparation.json": "old_publication_preparation_sha256",
        PREVIOUS / "publish-payload.json": "old_publication_payload_sha256",
        binding.GET: "authoritative_old_target_GET_sha256",
        STAGE / bridge.OUTPUT: "new_comparator_sha256",
        STAGE / bridge.MANIFEST: "new_comparator_manifest_sha256",
        STAGE / bridge.OUTPUT.replace(".lean", ".lean.preflight.json"): "new_comparator_sidecar_sha256",
        bridge.CERT: "original_AP11_certificate_sha256",
        TASK / read(CERT)["original_AP11_solution_olean"]: "original_AP11_solution_olean_sha256",
    }
    for path, key in direct.items():
        need(sha(path) == frozen[key], "Frozen source017 input changed: " + str(path))
    log = binding.context.file(read(CERT)["new_comparator_preflight"]["data"]["log"])
    need(sha(log) == frozen["new_comparator_log_sha256"], "Source017 comparator log changed")
    for dep in frozen["new_comparator_dependency_oleans"]:
        need(sha(Path(dep["path"])) == dep["sha256"],
             "First-search source017 comparator imported OLean changed: " + dep["module"])
    for filename, expected in frozen["payload_sha256"].items():
        need(sha(DEST / filename) == expected, "Frozen source017 HTTP payload changed: " + filename)
    need(sha(DEST / "wire-theorem-source.lean") == frozen["platform_statement_assembly_sha256"],
         "Complete source017 platform wire changed")


def prepare():
    manifest, metadata, payloads, wire, pins = artifacts()
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "wire-theorem-source.lean", wire)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    exact(DEST / "preparation.json", encode(pins))
    hash_gate(manifest, pins)
    return pins


def check():
    manifest, metadata, payloads, wire, pins = artifacts()
    need((DEST / "manifest.json").read_bytes() == encode(manifest)
         and (DEST / "validation.json").read_bytes() == CERT.read_bytes()
         and (DEST / "metadata.json").read_bytes() == encode(metadata)
         and (DEST / "wire-theorem-source.lean").read_bytes() == wire
         and (DEST / "preparation.json").read_bytes() == encode(pins),
         "Frozen source017 publication preparation differs")
    for name, raw in payloads.items():
        need((DEST / name).read_bytes() == raw, "Frozen source017 payload differs: " + name)
    hash_gate(manifest, pins)
    return pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    pins = prepare() if args.prepare_only else check()
    print(json.dumps({"prepared": True, "theorem_name": pins["theorem_name"],
                      "exact_full_comparator_wire": True, "network_used": False,
                      "proposal_status": "Draft", "payload_sha256": pins["payload_sha256"]},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
