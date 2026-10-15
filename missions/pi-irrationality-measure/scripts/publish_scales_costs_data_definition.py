"""Advance the frozen AP15 scales/costs Definition with the audited driver."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import prepare_scales_costs_data_publication as offline
import publish_closed_definition_bundle as driver


SELF = Path(__file__).resolve()


def preparation():
    offline.check()
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path, cert = offline.artifacts()
    pins = offline.pins(c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert)
    offline.need(offline.sha(Path(driver.__file__)) == pins["publisher_script_sha256"]
                 and offline.sha(SELF) == pins["online_wrapper_sha256"],
                 "Frozen AP15 publisher implementation changed")
    offline.need(pins["route"] == "/submit-definition"
                 and pins["expected_readback_status"] == "Definition",
                 "AP15 Definition route/readback contract differs")
    offline.need(payload["definition"].encode("utf-8") == provider.read_bytes(),
                 "AP15 wire Definition differs from actual compiled provider")
    return root / "publication-v2", metadata, payload, pins


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--provider", choices=list(offline.stage.CONFIGS), default=offline.KEY)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--prepare-only", action="store_true")
    g.add_argument("--advance", action="store_true")
    a = p.parse_args()
    pub, metadata, payload, pins = preparation()
    online = pub / "online-preparation-definition.json"
    online_pins = dict(pins)
    online_pins.update({"offline_prepare_record_sha256": offline.sha(pub / "prepare-record.json"),
                        "http_lookup_scope": "exact definition name and pinned environment only"})
    if a.prepare_only:
        offline.exact(online, offline.encode(online_pins))
        print(json.dumps({"prepared": True, "provider": offline.KEY, "network_used": False,
                          "proposal_status": "Draft", "payload_sha256": pins["payload_sha256"]},
                         ensure_ascii=False, indent=2))
        return
    offline.need(online.is_file() and online.read_bytes() == offline.encode(online_pins)
                 and offline.sha(pub / "prepare-record.json") == online_pins["offline_prepare_record_sha256"],
                 "Reviewed AP15 online/offline preparation changed")
    record = driver.advance(pub, metadata, payload, pins)
    print(json.dumps({"advanced": True, "provider": offline.KEY,
                      "definition_name": payload["definition_name"],
                      "job_id": record.get("job_id"),
                      "definition_id": record.get("definition_id"),
                      "status": record.get("last_publish_verdict", {}).get("body", {}).get("status")},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
