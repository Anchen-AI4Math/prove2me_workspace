"""Prepare or durably advance the frozen AP15 selected-minor clearing publication."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from unittest.mock import patch

import prepare_selected_minor_clearing_bound_publication as offline
import publish_standalone_platform_node as driver


SELF = Path(__file__).resolve()
PUB = offline.DEST


def preparation():
    offline.check()
    prep, manifest, metadata, payloads, _ = offline.static()
    pins = offline.read(PUB / "preparation.json")
    offline.need(offline.sha(SELF) == pins["online_wrapper_sha256"],
                 "AP15 online wrapper hash differs")
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
                         ensure_ascii=False, indent=2))
        return
    offline.need(online.is_file() and online.read_bytes() == offline.encode(pins),
                 "Reviewed AP15 online preparation changed")

    def hash_only_guard(current):
        offline.hash_gate(current, pins)
        offline.need(offline.sha(online) == offline.sha_bytes(offline.encode(pins)),
                     "Frozen AP15 online preparation changed")

    with patch.object(driver.validator, "strict_inputs", hash_only_guard):
        driver.advance(PUB, manifest, metadata, pins, payloads)


if __name__ == "__main__":
    main()
