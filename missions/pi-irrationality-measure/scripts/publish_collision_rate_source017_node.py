"""Prepare or advance the exact _source017 Draft through the durable API driver.

Only --advance may contact the platform, and is reserved for the root agent.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from unittest.mock import patch

import prepare_collision_rate_source017_publication as offline
import publish_standalone_platform_node as driver


SELF = Path(__file__).resolve()
PUB = offline.DEST


def preparation():
    offline.check()
    manifest, metadata, payloads, _, pins = offline.artifacts()
    offline.need(offline.sha(SELF) == pins["online_wrapper_sha256"],
                 "Online source017 wrapper differs from frozen preparation")
    return manifest, metadata, payloads, pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    manifest, metadata, payloads, pins = preparation()
    online = PUB / "online-preparation-driver.json"
    if args.prepare_only:
        offline.exact(online, offline.encode(pins))
        print(json.dumps({"prepared": True, "theorem_name": manifest["theorem_name"],
                          "network_used": False, "proposal_status": "Draft",
                          "payload_sha256": pins["payload_sha256"]}, ensure_ascii=False))
        return
    offline.need(online.is_file() and online.read_bytes() == offline.encode(pins),
                 "Reviewed source017 online preparation changed")

    def hash_only_guard(current):
        offline.hash_gate(current, pins)
        offline.need(offline.sha(online) == offline.sha_bytes(offline.encode(pins)),
                     "Frozen source017 online preparation changed")

    # The reused driver exact-name lookup and every GET readback require the
    # full public name, pinned environment, and byte-exact preamble/formal text.
    with patch.object(driver.validator, "strict_inputs", hash_only_guard):
        driver.advance(PUB, manifest, metadata, pins, payloads)


if __name__ == "__main__":
    main()
