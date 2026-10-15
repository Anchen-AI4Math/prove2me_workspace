"""Freeze AP17's hash-only online driver after its one full strict replay."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import prepare_actual_minor_arithmetic_lower_bound_source017_verification as offline


SELF = Path(__file__).resolve()
PREPARATION = offline.DEST / "preparation.json"
ONLINE = offline.DEST / "online-preparation-driver.json"


def prepare():
    pins = offline.read(PREPARATION)
    offline.hash_gate(pins)
    offline.need(offline.sha(SELF) == pins["fast_descriptor_helper_sha256"]
                 and offline.sha(PREPARATION) == offline.sha_bytes(offline.encode(pins)),
                 "AP17 reviewed replay pins/helper differ")
    offline.exact(ONLINE, offline.encode(pins))
    return {"prepared": True, "network_used": False, "API_used": False,
            "full_strict_replay_reused": True,
            "online_preparation_driver_sha256": offline.sha(ONLINE),
            "descriptor_sha256": pins["descriptor_sha256"],
            "multipart_sha256": pins["multipart_sha256"]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(prepare(), ensure_ascii=False, indent=2))
