"""Advance the frozen v2 collisionConstant Definition through the audited driver."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import prepare_collision_constant_publication_v2 as offline
import publish_closed_definition_bundle as definition_driver


SELF = Path(__file__).resolve()
PUB = offline.DEST


def preparation():
    offline.check()
    provider, definition_bytes, metadata, payload, payload_bytes, manifest, cert = offline.artifacts()
    pins = offline.pins(provider, definition_bytes, metadata, payload_bytes, manifest, cert)
    if offline.sha(Path(definition_driver.__file__)) != pins["publisher_script_sha256"]:
        raise ValueError("Audited Definition driver changed")
    if pins["route"] != "/submit-definition" or pins["expected_readback_status"] != "Definition":
        raise ValueError("Definition route/readback contract differs")
    if payload["definition"].encode("utf-8") != provider.read_bytes():
        raise ValueError("Definition payload body differs from the compiled provider source")
    return metadata, payload, pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    metadata, payload, pins = preparation()
    online = PUB / "online-preparation-definition-v1.json"
    online_pins = dict(pins)
    online_pins.update({
        "online_wrapper_sha256": offline.sha(SELF),
        "offline_prepare_record_sha256": offline.sha(PUB / "prepare-record.json"),
        "http_lookup_scope": "exact definition name and pinned environment only",
    })
    if args.prepare_only:
        offline.exact(online, offline.encode(online_pins))
        print(json.dumps({"prepared": True, "network_used": False,
                          "proposal_status": "Draft",
                          "payload_sha256": pins["payload_sha256"]}, ensure_ascii=False))
        return
    if online.read_bytes() != offline.encode(online_pins):
        raise ValueError("Reviewed online Definition preparation changed")
    if offline.sha(SELF) != online_pins["online_wrapper_sha256"]:
        raise ValueError("Frozen collisionConstant online wrapper changed")
    if offline.sha(PUB / "prepare-record.json") != online_pins["offline_prepare_record_sha256"]:
        raise ValueError("Frozen collisionConstant offline preparation changed")
    # The audited driver performs exact-name/environment lookup, writes a durable
    # publish_intent before its one POST, polls one job state per invocation, and
    # requires status=Definition plus byte-identical definition readback.
    record = definition_driver.advance(PUB, metadata, payload, pins)
    print(json.dumps({"advanced": True, "definition_name": payload["definition_name"],
                      "job_id": record.get("job_id"),
                      "definition_id": record.get("definition_id"),
                      "status": record.get("last_publish_verdict", {}).get("body", {}).get("status")},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
