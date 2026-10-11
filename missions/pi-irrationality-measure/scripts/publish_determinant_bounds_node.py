"""Prepare or advance the frozen determinant-bounds theorem publication."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from unittest.mock import patch

import prepare_determinant_bounds_publication as offline
import publish_standalone_platform_node as driver


SELF = Path(__file__).resolve()
TASK, ROOT, STAGE, PUB = offline.TASK, offline.ROOT, offline.STAGE, offline.DEST


def saved_gate(manifest):
    offline.check()
    _, staged, _, _, assembled, cert = offline.artifacts()
    if manifest != staged:
        raise ValueError("Publisher manifest differs from frozen determinant-bounds publication")
    statement = ROOT / staged["statement"]
    if statement.read_bytes() != assembled:
        raise ValueError("Publisher Thm differs from exact modechecked source")
    offline.replay_certificate(cert, offline.read(STAGE / "manifest.json"))


def preparation():
    offline.check()
    prep, manifest, metadata, payloads, _, _ = offline.artifacts()
    saved_gate(manifest)
    pins = dict(offline.pins(prep, manifest, metadata, payloads))
    pins.update({
        "online_wrapper_sha256": offline.sha(SELF),
        "offline_preparation_sha256": offline.sha(PUB / "preparation.json"),
        "http_lookup_scope": "exact theorem name and pinned environment only; no graph reconstruction",
        "durable_post_policy": "saved publish_intent before POST; never repeat a recorded intent",
    })
    return manifest, metadata, payloads, pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    manifest, metadata, payloads, pins = preparation()
    online = PUB / "online-preparation-driver.json"
    if args.prepare_only:
        offline.exact(online, offline.encode(pins))
        print(json.dumps({"prepared": True, "network_used": False,
                          "proposal_status": "Draft",
                          "payload_sha256": pins["payload_sha256"]},
                         ensure_ascii=False))
        return
    if online.read_bytes() != offline.encode(pins):
        raise ValueError("Reviewed determinant-bounds online preparation changed")

    def guard(current):
        saved_gate(current)
        if offline.sha(SELF) != pins["online_wrapper_sha256"]:
            raise ValueError("Frozen determinant-bounds online wrapper changed")
        if offline.sha(PUB / "preparation.json") != pins["offline_preparation_sha256"]:
            raise ValueError("Frozen determinant-bounds offline preparation changed")

    with patch.object(driver.validator, "strict_inputs", guard):
        driver.advance(PUB, manifest, metadata, pins, payloads)


if __name__ == "__main__":
    main()
