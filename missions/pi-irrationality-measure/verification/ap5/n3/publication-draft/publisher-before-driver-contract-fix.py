"""Advance the frozen ap5/n3 payload with strict saved-evidence guards."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from unittest.mock import patch

import prepare_normalized_successive_approximations_n3_publication as offline
import publish_standalone_platform_node as driver
import validate_namespace_context_providers as context

SELF = Path(__file__).resolve()
TASK, ROOT, STAGE, PUB = offline.TASK, offline.ROOT, offline.STAGE, offline.DEST


def saved_gate(manifest: dict) -> None:
    offline.check()
    certificate = offline.read(offline.CERT)
    for name, row in certificate["preflights"].items():
        data = row["data"]
        source = context.file(data["source"])
        mp = context.file(data["manifest"])
        current = context.record(source, mp, "modecheck", data["actual_module_identity"], STAGE)
        # The node cert retains the three raw evidence fields. context.record
        # also returns a summary derived from the same checked sidecar.
        if (set(current) != {"summary", "record", "record_sha256", "data"}
                or set(row) != {"record", "record_sha256", "data"}
                or {key: current[key] for key in row} != row):
            raise ValueError("Exact n3 preflight/log/runtime/first-search evidence changed: " + name)
    staged = offline.read(STAGE / "manifest.json")
    if manifest.get("preamble") != staged["wire_preamble"]:
        raise ValueError("Publisher preamble differs from the exact compiled wire preamble")
    for key, value in staged.items():
        if manifest.get(key) != value:
            raise ValueError("Publisher manifest differs from stage at: " + key)
    statement = ROOT / staged["statement"]
    if ((manifest["preamble"] + manifest["formal_statement"]).encode("utf-8")
            != statement.read_bytes()):
        raise ValueError("Publisher statement bytes differ from the actual modechecked Thm source")


def preparation():
    offline.check()
    manifest, _, metadata, payloads, pins, _ = offline.artifacts()
    saved_gate(manifest)
    result = dict(pins)
    result.update({
        "api_client_sha256": offline.sha(ROOT / "scripts/p2m_api.py"),
        "online_wrapper_sha256": offline.sha(SELF),
        "offline_preparation_sha256": offline.sha(PUB / "preparation.json"),
        "assembly_certificate_sha256": offline.sha(PUB / "assembly-certificate.json"),
        "http_lookup_scope": "exact theorem name and pinned environment only; no 875-graph reconstruction",
    })
    return manifest, metadata, payloads, result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare-only", action="store_true")
    group.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    manifest, metadata, payloads, pins = preparation()
    online = PUB / "online-preparation.json"
    if args.prepare_only:
        offline.exact(online, offline.encode(pins))
        print(json.dumps({"prepared": True, "network_used": False,
                          "payload_sha256": pins["payload_sha256"],
                          "proposal_status": "Draft"}, ensure_ascii=False))
        return
    if online.read_bytes() != offline.encode(pins):
        raise ValueError("Reviewed online preparation changed; no network action taken")

    def guard(current_manifest):
        saved_gate(current_manifest)
        if (offline.sha(SELF) != pins["online_wrapper_sha256"]
                or offline.sha(PUB / "preparation.json") != pins["offline_preparation_sha256"]
                or offline.sha(PUB / "assembly-certificate.json") != pins["assembly_certificate_sha256"]
                or offline.sha(ROOT / "scripts/p2m_api.py") != pins["api_client_sha256"]):
            raise ValueError("Frozen n3 online implementation or evidence changed")

    with patch.object(driver.validator, "strict_inputs", guard):
        driver.advance(PUB, manifest, metadata, pins, payloads)


if __name__ == "__main__":
    main()
