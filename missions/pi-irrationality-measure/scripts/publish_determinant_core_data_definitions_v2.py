"""Advance the frozen AP10 determinant Definition through the audited driver."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import prepare_determinant_core_data_publication_v2 as offline
import publish_closed_definition_bundle as driver


SELF = Path(__file__).resolve()


def preparation():
    offline.check()
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path, cert = offline.artifacts()
    pins = offline.pins(c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert)
    offline.base.need(offline.base.sha(Path(driver.__file__)) == pins["publisher_script_sha256"]
                      and offline.base.sha(SELF) == pins["online_wrapper_sha256"],
                      "Frozen determinant-v2 publisher implementation changed")
    offline.base.need(pins["route"] == "/submit-definition"
                      and pins["expected_readback_status"] == "Definition",
                      "Determinant-v2 Definition route/readback contract differs")
    offline.base.need(payload["definition"].encode() == provider.read_bytes()
                      and offline.base.sha_bytes(payload_bytes) ==
                          pins["ordinary_pending_payload_sha256"],
                      "Determinant-v2 wire bytes differ from the frozen provider/pending payload")
    return root / offline.DEST_NAME, metadata, payload, pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare-only", action="store_true")
    group.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    pub, metadata, payload, pins = preparation()
    online = pub / "online-preparation-definition.json"
    online_pins = dict(pins)
    online_pins.update({
        "offline_prepare_record_sha256": offline.base.sha(pub / "prepare-record.json"),
        "http_lookup_scope": "exact definition name and pinned environment only",
    })
    if args.prepare_only:
        offline.exact(online, offline.base.encode(online_pins))
        print(json.dumps({"prepared": True, "provider": offline.KEY,
                          "network_used": False, "proposal_status": "Draft",
                          "payload_sha256": pins["payload_sha256"]},
                         ensure_ascii=False, indent=2))
        return
    offline.base.need(online.is_file()
                      and online.read_bytes() == offline.base.encode(online_pins)
                      and offline.base.sha(pub / "prepare-record.json") ==
                          online_pins["offline_prepare_record_sha256"],
                      "Reviewed determinant-v2 online/offline preparation changed")
    record = driver.advance(pub, metadata, payload, pins)
    print(json.dumps({"advanced": True, "provider": offline.KEY,
                      "definition_name": payload["definition_name"],
                      "job_id": record.get("job_id"),
                      "definition_id": record.get("definition_id"),
                      "status": record.get("last_publish_verdict", {}).get("body", {}).get("status")},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
