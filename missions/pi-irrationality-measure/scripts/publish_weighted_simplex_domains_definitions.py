"""Advance one frozen AP9 Definition through the audited Definition driver."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import prepare_weighted_simplex_domains_publication as offline
import publish_closed_definition_bundle as definition_driver


SELF = Path(__file__).resolve()


def preparation(key):
    offline.check(key)
    values = offline.artifacts(key)
    c, root, prep, provider, raw, metadata, payload, payload_bytes, manifest, cert_path, cert = values
    pins = offline.pins(key, c, root, prep, provider, raw, metadata, payload_bytes, manifest, cert_path, cert)
    offline.need(offline.sha(Path(definition_driver.__file__)) == pins["publisher_script_sha256"],
                 "Audited Definition driver changed")
    offline.need(offline.sha(SELF) == pins["online_wrapper_sha256"],
                 "AP9 online wrapper changed")
    offline.need(pins["route"] == "/submit-definition"
                 and pins["expected_readback_status"] == "Definition",
                 "Definition route/readback contract differs")
    offline.need(payload["definition"].encode("utf-8") == provider.read_bytes(),
                 "Definition payload body differs from compiled provider source")
    return root / "publication", metadata, payload, pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider", choices=list(offline.stage.CONFIGS), required=True)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    pub, metadata, payload, pins = preparation(args.provider)
    online = pub / "online-preparation-definition.json"
    online_pins = dict(pins)
    online_pins.update({
        "offline_prepare_record_sha256": offline.sha(pub / "prepare-record.json"),
        "http_lookup_scope": "exact definition name and pinned environment only",
    })
    if args.prepare_only:
        offline.exact(online, offline.encode(online_pins))
        print(json.dumps({"prepared": True, "provider": args.provider,
                          "network_used": False, "proposal_status": "Draft",
                          "payload_sha256": pins["payload_sha256"]}, ensure_ascii=False, indent=2))
        return
    offline.need(online.is_file() and online.read_bytes() == offline.encode(online_pins),
                 "Reviewed online AP9 Definition preparation changed")
    offline.need(offline.sha(pub / "prepare-record.json") == online_pins["offline_prepare_record_sha256"],
                 "Frozen AP9 offline preparation changed")
    # Reuse the audited exact-name/environment lookup, exact public Definition
    # readback, durable pre-POST intent and one-job-per-invocation poller unchanged.
    record = definition_driver.advance(pub, metadata, payload, pins)
    print(json.dumps({"advanced": True, "provider": args.provider,
                      "definition_name": payload["definition_name"],
                      "job_id": record.get("job_id"),
                      "definition_id": record.get("definition_id"),
                      "status": record.get("last_publish_verdict", {}).get("body", {}).get("status")},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
