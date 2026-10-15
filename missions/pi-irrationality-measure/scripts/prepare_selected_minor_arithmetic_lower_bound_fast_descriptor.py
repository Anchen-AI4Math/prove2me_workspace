"""Freeze AP16's reviewed online driver after the one full offline replay.

This helper performs hash gates only.  It does not call the strict consumer,
Lean, credentials, or the platform API.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import prepare_selected_minor_arithmetic_lower_bound_publication as offline


SELF = Path(__file__).resolve()
PUB = offline.DEST
PREPARATION = PUB / "preparation.json"
ONLINE_PREPARATION = PUB / "online-preparation-driver.json"


def prepare():
    pins = offline.read(PREPARATION)
    manifest = offline.read(PUB / "manifest.json")
    offline.hash_gate(manifest, pins)
    offline.need(offline.sha(SELF) == pins["fast_descriptor_helper_sha256"],
                 "AP16 fast descriptor helper changed")
    offline.need(offline.sha(PREPARATION) == offline.sha_bytes(offline.encode(pins))
                 and (PUB / "validation.json").read_bytes() == offline.CERT.read_bytes()
                 and offline.sha(PUB / "validation.json") == pins["validation_sha256"]
                 and offline.sha(PUB / "metadata.json") == pins["metadata_sha256"]
                 and offline.sha(PUB / "wire-theorem-source.lean") ==
                     pins["wire_theorem_sha256"],
                 "AP16 fully replayed publication artifacts differ")
    for name, expected in pins["payload_sha256"].items():
        path = PUB / name
        offline.need(path.is_file() and offline.sha(path) == expected,
                     "AP16 frozen payload differs: " + name)
    offline.exact(ONLINE_PREPARATION, offline.encode(pins))
    return {"prepared": True, "network_used": False, "API_used": False,
            "full_strict_replay_reused": True,
            "online_preparation_driver_sha256": offline.sha(ONLINE_PREPARATION),
            "payload_sha256": pins["payload_sha256"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(prepare(), ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
