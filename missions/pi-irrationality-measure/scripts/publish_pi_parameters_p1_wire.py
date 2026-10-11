"""At-most-once bridge for the exact certified Parameters p1 Draft payload."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from unittest.mock import patch

import prepare_pi_parameters_p1_publication as offline
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
            raise ValueError("Exact p1 preflight context.record, log, runtime or import OLean changed: " + filename)
    if manifest != offline.read(offline.STAGE / "manifest.json"):
        raise ValueError("p1 publishing manifest changed")
    statement = offline.STAGE / "Theorems/Thm_OAI_PiExponent_exists_parameters.lean"
    expected = (manifest["preamble"] + manifest["formal_statement"]).encode("utf-8")
    if statement.read_bytes() != expected:
        raise ValueError("Exact compiled Thm bytes differ from manifest.preamble + manifest.formal_statement")


def preparation():
    offline.check()
    manifest, _, metadata, payloads, pins = offline.artifacts()
    saved_gate(manifest)
    pins = dict(pins)
    pins["api_client_sha256"] = offline.sha(ROOT / "scripts/p2m_api.py")
    pins["online_wrapper_sha256"] = offline.sha(SELF)
    pins["offline_preparation_sha256"] = offline.sha(PUB / "preparation.json")
    return manifest, metadata, payloads, pins


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
                          "payload_sha256": pins["payload_sha256"]}, ensure_ascii=False, indent=2))
        return
    if not online.exists() or online.read_bytes() != offline.encode(pins):
        raise ValueError("Exact reviewed publisher preparation changed; no network action taken")

    def gate(current_manifest):
        saved_gate(current_manifest)
        if (offline.sha(SELF) != pins["online_wrapper_sha256"]
                or offline.sha(PUB / "preparation.json") != pins["offline_preparation_sha256"]
                or offline.sha(ROOT / "scripts/p2m_api.py") != pins["api_client_sha256"]):
            raise ValueError("Frozen p1 publisher implementation or offline preparation changed")

    with patch.object(driver.validator, "strict_inputs", gate):
        driver.advance(PUB, manifest, metadata, pins, payloads)


if __name__ == "__main__":
    main()
