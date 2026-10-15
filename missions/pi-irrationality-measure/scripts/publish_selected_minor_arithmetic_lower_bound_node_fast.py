"""Durably advance the fully replayed AP16 arithmetic lower-bound publication by hash gates only."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from unittest.mock import patch

import prepare_selected_minor_arithmetic_lower_bound_publication as offline
import publish_standalone_platform_node as driver


SELF = Path(__file__).resolve()
BASE_ONLINE = offline.TASK / "scripts/publish_selected_minor_arithmetic_lower_bound_node.py"
PUB = offline.DEST
PREPARATION = PUB / "preparation.json"
ONLINE_PREPARATION = PUB / "online-preparation-driver.json"
FAST_PREPARATION = PUB / "fast-online-preparation.json"


def frozen():
    pins = offline.read(PREPARATION)
    manifest_path = PUB / "manifest.json"
    metadata_path = PUB / "metadata.json"
    validation_path = PUB / "validation.json"
    wire_path = PUB / "wire-theorem-source.lean"
    manifest = offline.read(manifest_path)
    metadata = offline.read(metadata_path)
    offline.hash_gate(manifest, pins)
    offline.need(offline.sha(PREPARATION) == offline.sha_bytes(offline.encode(pins))
                 and offline.sha(BASE_ONLINE) == pins["online_wrapper_sha256"]
                 and ONLINE_PREPARATION.is_file()
                 and ONLINE_PREPARATION.read_bytes() == offline.encode(pins),
                 "Reviewed AP16 final preparation differs")
    offline.need(validation_path.read_bytes() == offline.CERT.read_bytes()
                 and offline.sha(validation_path) == pins["validation_sha256"]
                 and offline.sha(metadata_path) == pins["metadata_sha256"]
                 and offline.sha(wire_path) == pins["wire_theorem_sha256"],
                 "Frozen AP16 publication evidence copy differs")
    payloads = {}
    for name, expected in pins["payload_sha256"].items():
        path = PUB / name
        offline.need(path.is_file() and offline.sha(path) == expected,
                     "Frozen AP16 payload differs: " + name)
        payloads[name] = path.read_bytes()
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    verify = json.loads(payloads["verification-payload.json"])
    offline.need(problem["theorem_name"] == pins["theorem_name"]
                 and problem["preamble"] == manifest["preamble"]
                 and problem["formal_statement"] == manifest["formal_statement"]
                 and verify["theorem_id"] is None
                 and verify["target_theorem_name"] == pins["theorem_name"]
                 and offline.sha_bytes(verify["file"]["utf8"].encode("utf-8")) ==
                     pins["solution_sha256"],
                 "Frozen AP16 payload semantics differ")
    return manifest, metadata, payloads, pins


def descriptor():
    manifest, metadata, payloads, pins = frozen()
    value = {"schema_version": 1,
        "artifact_kind": "ap16-selected-minor-arithmetic-lower-bound-fast-online-preparation",
        "full_strict_replay_preparation_sha256": offline.sha(PREPARATION),
        "full_strict_replay_validation_sha256": pins["validation_sha256"],
        "fast_wrapper_sha256": offline.sha(SELF),
        "base_online_wrapper_sha256": offline.sha(BASE_ONLINE),
        "online_preparation_driver_sha256": offline.sha(ONLINE_PREPARATION),
        "manifest_sha256": offline.sha(PUB / "manifest.json"),
        "metadata_sha256": offline.sha(PUB / "metadata.json"),
        "validation_copy_sha256": offline.sha(PUB / "validation.json"),
        "wire_theorem_sha256": offline.sha(PUB / "wire-theorem-source.lean"),
        "payload_sha256": pins["payload_sha256"],
        "hash_gate_rechecks_all_certificate_bound_inputs_before_each_HTTP": True,
        "network_used": False, "API_used": False,
        "proposal_status": "Draft"}
    return manifest, metadata, payloads, pins, value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    manifest, metadata, payloads, pins, value = descriptor()
    if args.prepare_only:
        offline.exact(FAST_PREPARATION, offline.encode(value))
        print(json.dumps({"prepared": True, "network_used": False,
                          "full_strict_replay_reused": True,
                          "payload_sha256": pins["payload_sha256"]},
                         ensure_ascii=False, indent=2))
        return
    offline.need(FAST_PREPARATION.is_file()
                 and FAST_PREPARATION.read_bytes() == offline.encode(value),
                 "Reviewed AP16 fast preparation differs")

    def hash_only_guard(current):
        current_manifest, _, current_payloads, current_pins, current_value = descriptor()
        offline.need(current == current_manifest and current_pins == pins
                     and current_payloads == payloads
                     and FAST_PREPARATION.read_bytes() == offline.encode(current_value),
                     "Frozen AP16 fast advancement inputs differ")

    with patch.object(driver.validator, "strict_inputs", hash_only_guard):
        driver.advance(PUB, manifest, metadata, pins, payloads)


if __name__ == "__main__":
    main()
