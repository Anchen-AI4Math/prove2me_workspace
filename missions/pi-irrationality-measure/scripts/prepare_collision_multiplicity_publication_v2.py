"""Hash-only AP18 publication successor with the v0.12.4 job schema."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import prepare_collision_multiplicity_publication as prior


read, encode, sha, sha_bytes = prior.read, prior.encode, prior.sha, prior.sha_bytes
need, exact = prior.need, prior.exact
TASK, ROOT, KEY, stage = prior.TASK, prior.ROOT, prior.KEY, prior.stage
SELF = Path(__file__).resolve()
ONLINE = prior.TASK / "scripts/publish_collision_multiplicity_definition_v2.py"
PREVIOUS = prior.stage.STAGE / "publication"
DEST = prior.stage.STAGE / "publication-v2"
PREVIOUS_PREPARATION = PREVIOUS / "prepare-record.json"


def successor():
    old = prior.read(PREVIOUS_PREPARATION)
    prior.hash_gate(old)
    prior.need(prior.sha(prior.SELF) == old["offline_wrapper_sha256"]
               and prior.sha(prior.ONLINE) == old["online_wrapper_sha256"],
               "AP18 predecessor wrappers differ")
    frozen = dict(old)
    frozen.update({
        "artifact_kind": "ap18-collision-multiplicity-definition-publication-preparation-v2",
        "predecessor_prepare_record": prior.stage.rel(PREVIOUS_PREPARATION),
        "predecessor_prepare_record_sha256": prior.sha(PREVIOUS_PREPARATION),
        "predecessor_offline_wrapper_sha256": old["offline_wrapper_sha256"],
        "predecessor_online_wrapper_sha256": old["online_wrapper_sha256"],
        "offline_wrapper_sha256": prior.sha(SELF),
        "online_wrapper_sha256": prior.sha(ONLINE),
        "publish_job_response_contract": {
            "id": "exact durable job id", "kind": "definition",
            "theorem_name": old["definition_name"],
            "legacy_job_id_and_definition_name_if_present_must_also_match": True},
        "strict_certificate_replay_reused_by_hash": True,
        "new_deep_certificate_replay_performed": False})
    return frozen


def hash_gate(frozen):
    prior.need(frozen["predecessor_prepare_record_sha256"] == prior.sha(PREVIOUS_PREPARATION)
               and frozen["predecessor_prepare_record"] == prior.stage.rel(PREVIOUS_PREPARATION)
               and prior.sha(SELF) == frozen["offline_wrapper_sha256"]
               and prior.sha(ONLINE) == frozen["online_wrapper_sha256"],
               "AP18 successor/predecessor identity changed")
    old = prior.read(PREVIOUS_PREPARATION)
    prior.need(old["offline_wrapper_sha256"] == frozen["predecessor_offline_wrapper_sha256"]
               and old["online_wrapper_sha256"] == frozen["predecessor_online_wrapper_sha256"],
               "AP18 predecessor wrapper pins changed")
    prior.hash_gate(old)
    prior.need((DEST / "prepare-record.json").read_bytes() == prior.encode(frozen)
               and (DEST / "manifest.json").read_bytes() == (PREVIOUS / "manifest.json").read_bytes()
               and (DEST / "validation.json").read_bytes() == (PREVIOUS / "validation.json").read_bytes()
               and (DEST / "metadata.json").read_bytes() == (PREVIOUS / "metadata.json").read_bytes()
               and (DEST / "publish-payload.json").read_bytes() ==
                   (PREVIOUS / "publish-payload.json").read_bytes()
               and (DEST / "wire-definition-source.lean").read_bytes() ==
                   (PREVIOUS / "wire-definition-source.lean").read_bytes(),
               "AP18 successor artifacts differ from certified predecessor")


def prepare():
    frozen = successor()
    for name in ("manifest.json", "validation.json", "metadata.json",
                 "publish-payload.json", "wire-definition-source.lean"):
        prior.exact(DEST / name, (PREVIOUS / name).read_bytes())
    prior.exact(DEST / "prepare-record.json", prior.encode(frozen))
    hash_gate(frozen)
    return {"prepared": True, "provider": prior.KEY, "network_used": False,
            "strict_certificate_replay_reused_by_hash": True,
            "payload_sha256": frozen["payload_sha256"], "proposal_status": "Draft"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true", required=True)
    parser.parse_args()
    print(json.dumps(prepare(), ensure_ascii=False, indent=2))
