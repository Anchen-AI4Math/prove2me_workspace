"""Advance the frozen n1 payload through the existing at-most-once API driver."""
import argparse
import json
from pathlib import Path
from unittest.mock import patch
import prepare_successive_approximations_n1_publication as offline
import publish_standalone_platform_node as driver
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
TASK, ROOT, PUB = offline.TASK, offline.ROOT, offline.DEST

def saved_gate(manifest):
    offline.check()
    certificate = offline.read(offline.CERT)
    for filename, row in certificate["preflights"].items():
        data = row["data"]
        source = context.file(data["source"])
        mp = context.file(data["manifest"])
        current = context.record(source, mp, "modecheck", data["actual_module_identity"], offline.STAGE)
        if current != row:
            raise ValueError("Exact n1 sidecar, log, runtime or first-search OLean changed: " + filename)
    if manifest != offline.read(offline.STAGE / "manifest.json"):
        raise ValueError("n1 publishing manifest changed")

def preparation():
    offline.check()
    m, _, metadata, _, payloads, pins = offline.artifacts()
    saved_gate(m)
    pins = dict(pins)
    pins["api_client_sha256"] = offline.sha(ROOT / "scripts/p2m_api.py")
    pins["online_wrapper_sha256"] = offline.sha(SELF)
    pins["offline_preparation_sha256"] = offline.sha(PUB / "preparation.json")
    return m, metadata, payloads, pins

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    manifest, metadata, payloads, pins = preparation()
    online = PUB / "online-preparation.json"
    if args.prepare_only:
        offline.exact(online, offline.encode(pins))
        print(json.dumps({"prepared": True, "network_used": False, "proposal_status": "Draft",
                          "payload_sha256": pins["payload_sha256"]}))
        return
    if online.read_bytes() != offline.encode(pins):
        raise ValueError("Online preparation changed; no network action taken")
    def gate(current_manifest):
        saved_gate(current_manifest)
        if (offline.sha(SELF) != pins["online_wrapper_sha256"]
                or offline.sha(PUB / "preparation.json") != pins["offline_preparation_sha256"]
                or offline.sha(ROOT / "scripts/p2m_api.py") != pins["api_client_sha256"]):
            raise ValueError("Frozen n1 publisher implementation/preparation changed")
    with patch.object(driver.validator, "strict_inputs", gate):
        driver.advance(PUB, manifest, metadata, pins, payloads)

if __name__ == "__main__":
    main()
