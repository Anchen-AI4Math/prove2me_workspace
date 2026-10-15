"""Advance one frozen AP10 Definition through the audited Definition driver."""
from __future__ import annotations
import argparse, json
from pathlib import Path
import prepare_core_parent_data_publication as offline
import publish_closed_definition_bundle as driver

SELF = Path(__file__).resolve()


def preparation(key):
    offline.check(key)
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path, cert = offline.artifacts(key)
    pins = offline.pins(key, c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert)
    offline.need(offline.sha(Path(driver.__file__)) == pins["publisher_script_sha256"]
                 and offline.sha(SELF) == pins["online_wrapper_sha256"],
                 "Frozen AP10 publisher implementation changed")
    offline.need(pins["route"] == "/submit-definition" and pins["expected_readback_status"] == "Definition",
                 "AP10 Definition route/readback contract differs")
    offline.need(payload["definition"].encode() == provider.read_bytes(),
                 "AP10 wire Definition differs from actual compiled provider")
    return root / "publication", metadata, payload, pins


def main():
    p = argparse.ArgumentParser(description=__doc__); p.add_argument("--provider", choices=list(offline.stage.CONFIGS), required=True)
    g = p.add_mutually_exclusive_group(required=True); g.add_argument("--prepare-only", action="store_true"); g.add_argument("--advance", action="store_true"); a = p.parse_args()
    pub, metadata, payload, pins = preparation(a.provider)
    online = pub / "online-preparation-definition.json"; online_pins = dict(pins)
    online_pins.update({"offline_prepare_record_sha256": offline.sha(pub / "prepare-record.json"),
                        "http_lookup_scope": "exact definition name and pinned environment only"})
    if a.prepare_only:
        offline.exact(online, offline.encode(online_pins))
        print(json.dumps({"prepared": True, "provider": a.provider, "network_used": False,
                          "proposal_status": "Draft", "payload_sha256": pins["payload_sha256"]},
                         ensure_ascii=False, indent=2)); return
    offline.need(online.is_file() and online.read_bytes() == offline.encode(online_pins)
                 and offline.sha(pub / "prepare-record.json") == online_pins["offline_prepare_record_sha256"],
                 "Reviewed AP10 online/offline preparation changed")
    record = driver.advance(pub, metadata, payload, pins)
    print(json.dumps({"advanced": True, "provider": a.provider,
                      "definition_name": payload["definition_name"], "job_id": record.get("job_id"),
                      "definition_id": record.get("definition_id"),
                      "status": record.get("last_publish_verdict", {}).get("body", {}).get("status")},
                     ensure_ascii=False))


if __name__ == "__main__": main()
