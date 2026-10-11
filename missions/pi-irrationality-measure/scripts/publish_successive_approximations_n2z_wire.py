"""Publish the exact compiled n2z statement after the preserved failed wire job."""
import argparse
import json
import sys
from pathlib import Path
from unittest.mock import patch
import prepare_successive_approximations_n2z_wire_retry as wire
import prepare_successive_approximations_n2z_publication as old
import publish_successive_approximations_n1 as bridge
import publish_standalone_platform_node as driver

sys.stdout.reconfigure(encoding="utf-8")
SELF = Path(__file__).resolve()
BRIDGE_SHA = "0d888c8840d6683dfab21af01f4fd687a64c99b1044270c3f583c1f4aaec29ff"
PUB = wire.DEST

def compiled_gate(wire_manifest):
    wire.check()
    original = wire.read(wire.STAGE / "manifest.json")
    differences = {key for key in original if original[key] != wire_manifest.get(key)}
    if set(original) != set(wire_manifest) or differences != {"preamble"}:
        raise ValueError("Wire repair differs beyond the exact statement preamble")
    assembled = (wire_manifest["preamble"] + wire_manifest["formal_statement"]).encode("utf-8")
    if assembled != wire.THEOREM_FILE.read_bytes():
        raise ValueError("Actual upload statement is not the exact successfully compiled source")
    if wire.sha(Path(bridge.__file__)) != BRIDGE_SHA:
        raise ValueError("Frozen current-runtime and first-search OLean gate changed")
    with patch.object(bridge, "offline", old):
        bridge.saved_gate(original)

def preparation():
    wire.check()
    _, metadata, payloads, wire_pins = wire.artifacts()
    manifest = wire.read(wire.STAGE / "manifest.json")
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    manifest = dict(manifest)
    manifest["preamble"] = problem["preamble"]
    compiled_gate(manifest)
    wire.exact(PUB / "manifest.json", wire.encode(manifest))
    return manifest, metadata, payloads, {
        "theorem_name": manifest["theorem_name"], "environment": driver.ENV,
        "proposal_status": "Draft", "manifest_sha256": wire.sha(PUB / "manifest.json"),
        "validation_sha256": wire.sha(PUB / "validation.json"),
        "metadata_sha256": wire.sha(PUB / "metadata.json"),
        "publisher_sha256": wire.sha(Path(driver.__file__)),
        "api_client_sha256": wire.sha(wire.ROOT / "scripts/p2m_api.py"),
        "online_wrapper_sha256": wire.sha(SELF), "online_bridge_sha256": BRIDGE_SHA,
        "wire_preparation_sha256": wire.sha(PUB / "online-preparation.json"),
        "assembly_certificate_sha256": wire.sha(PUB / "assembly-certificate.json"),
        "payload_sha256": wire_pins["payload_sha256"], "local_node_validated": True,
        "submission_ready": False, "full_tree_ready": False,
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    manifest, metadata, payloads, pins = preparation()
    path = PUB / "publisher-preparation.json"
    if args.prepare_only:
        wire.exact(path, wire.encode(pins))
        print(json.dumps({"prepared": True, "network_used": False,
                          "payload_sha256": pins["payload_sha256"], "proposal_status": "Draft"}))
        return
    if path.read_bytes() != wire.encode(pins):
        raise ValueError("Exact reviewed publisher preparation changed")
    def guard(current):
        compiled_gate(current)
        if (wire.sha(SELF) != pins["online_wrapper_sha256"]
                or wire.sha(PUB / "online-preparation.json") != pins["wire_preparation_sha256"]
                or wire.sha(PUB / "assembly-certificate.json") != pins["assembly_certificate_sha256"]):
            raise ValueError("Wire assembly or online implementation changed")
    with patch.object(driver.validator, "strict_inputs", guard):
        driver.advance(PUB, manifest, metadata, pins, payloads)

if __name__ == "__main__":
    main()
