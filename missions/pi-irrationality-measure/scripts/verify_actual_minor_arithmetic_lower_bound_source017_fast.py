"""Durably verify AP17 on one existing theorem; never publish a theorem."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path

import prepare_actual_minor_arithmetic_lower_bound_source017_verification as offline


SELF = Path(__file__).resolve()
PUB = offline.DEST
PREPARATION = PUB / "preparation.json"
ONLINE = PUB / "online-preparation-driver.json"
FAST = PUB / "fast-online-preparation.json"
RECORD = PUB / "publication.json"
VERIFY_STATUSES = {"PENDING", "COMPILING", "SKETCH_ACCEPTED", "ACCEPTED",
                   "CE", "WA", "SORRY", "FAILED", "ERROR"}


def frozen():
    pins = offline.read(PREPARATION)
    offline.hash_gate(pins)
    offline.need(offline.sha(SELF) == pins["fast_wrapper_sha256"]
                 and offline.sha(PREPARATION) == offline.sha_bytes(offline.encode(pins))
                 and ONLINE.is_file() and ONLINE.read_bytes() == offline.encode(pins),
                 "AP17 reviewed online preparation differs")
    descriptor = offline.read(PUB / "verification-payload.json")
    multipart = (PUB / "verification-request.multipart").read_bytes()
    offline.need(descriptor["theorem_id"] == pins["target_theorem_id"]
                 and descriptor["target_theorem_name"] == pins["target_theorem_name"]
                 and descriptor["proof_type"] == "prove"
                 and descriptor["file"]["sha256"] == pins["solution_sha256"]
                 and offline.sha_bytes(multipart) == pins["multipart_sha256"],
                 "AP17 exact existing-target descriptor differs")
    return pins, descriptor, multipart


def fast_descriptor():
    pins, descriptor, multipart = frozen()
    value = {"schema_version": 1,
        "artifact_kind": "ap17-existing-open-proof-fast-online-preparation",
        "target_theorem_id": pins["target_theorem_id"],
        "target_theorem_name": pins["target_theorem_name"],
        "full_strict_replay_preparation_sha256": offline.sha(PREPARATION),
        "full_strict_replay_validation_sha256": pins["validation_sha256"],
        "online_preparation_driver_sha256": offline.sha(ONLINE),
        "fast_wrapper_sha256": offline.sha(SELF),
        "descriptor_sha256": offline.sha(PUB / "verification-payload.json"),
        "multipart_sha256": offline.sha_bytes(multipart),
        "exact_existing_target_only": True, "creates_theorem_or_proposal": False,
        "hash_gate_rechecks_all_certificate_bound_inputs_before_each_HTTP": True,
        "network_used": False, "API_used": False, "proposal_status": "Draft"}
    return pins, descriptor, multipart, value


def exact_server_target(body, pins, expected_status):
    frozen_body = offline.read(offline.FRESH)["parsed_body"]
    for key in ("theorem_id", "theorem_name", "preamble", "formal_statement",
                "mathlib_rev", "visibility", "deprecated_at", "deprecated_by"):
        offline.need(body.get(key) == frozen_body.get(key),
                     "AP17 public target changed: " + key)
    offline.need(body.get("status") == expected_status
                 and body.get("theorem_id") == pins["target_theorem_id"]
                 and (body["preamble"] + body["formal_statement"]).encode("utf-8") ==
                     (PUB / "wire-theorem-source.lean").read_bytes(),
                 "AP17 public target status/wire differs")


def write_record(record):
    record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
    RECORD.parent.mkdir(parents=True, exist_ok=True)
    RECORD.write_bytes(offline.encode(record))


def advance():
    pins, descriptor, multipart, value = fast_descriptor()
    offline.need(FAST.is_file() and FAST.read_bytes() == offline.encode(value),
                 "AP17 reviewed fast descriptor differs")
    record = offline.read(RECORD) if RECORD.exists() else {
        "target_theorem_id": pins["target_theorem_id"],
        "target_theorem_name": pins["target_theorem_name"],
        "environment": pins["environment"],
        "solution_sha256": pins["solution_sha256"],
        "descriptor_sha256": pins["descriptor_sha256"],
        "multipart_sha256": pins["multipart_sha256"],
        "creates_theorem_or_proposal": False}
    offline.need(record["target_theorem_id"] == pins["target_theorem_id"]
                 and record["target_theorem_name"] == pins["target_theorem_name"]
                 and record["environment"] == pins["environment"]
                 and record["solution_sha256"] == pins["solution_sha256"]
                 and record["descriptor_sha256"] == pins["descriptor_sha256"]
                 and record["multipart_sha256"] == pins["multipart_sha256"]
                 and record["creates_theorem_or_proposal"] is False,
                 "AP17 durable record identity/bytes differ")
    spec = importlib.util.spec_from_file_location("p2m_api_ap17", offline.API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = None

    def request(method, path, **kwargs):
        nonlocal token
        current_pins, current_descriptor, current_multipart, current_value = fast_descriptor()
        offline.need(current_pins == pins and current_descriptor == descriptor
                     and current_multipart == multipart
                     and FAST.read_bytes() == offline.encode(current_value),
                     "AP17 frozen request inputs changed")
        if token is None:
            token = api.get_token()
        status, raw = api._request(method, path, token=token, **kwargs)
        offline.hash_gate(pins)
        try:
            return status, json.loads(raw)
        except json.JSONDecodeError:
            return status, {"raw_body": raw}

    if not record.get("verify_intent"):
        status, target = request("GET", "/theorems/" + pins["target_theorem_id"])
        offline.need(status == 200 and isinstance(target, dict),
                     "AP17 pre-verify target GET failed")
        exact_server_target(target, pins, "Open")
        pre = PUB / "pre-verify-target.json"
        pre.write_bytes(offline.encode(target))
        record["pre_verify_target"] = {
            "path": offline.rel(pre), "sha256": offline.sha(pre)}
        record["verify_intent"] = {
            "at_utc": datetime.now(timezone.utc).isoformat(),
            "endpoint": "/verify", "theorem_id": pins["target_theorem_id"],
            "descriptor_sha256": pins["descriptor_sha256"],
            "multipart_sha256": pins["multipart_sha256"],
            "content_type": pins["multipart_content_type"],
            "solution_sha256": pins["solution_sha256"]}
        write_record(record)
        status, body = request("POST", "/verify", raw_body=multipart,
                               ctype=pins["multipart_content_type"])
        record["verify_response"] = {"http_status": status, "body": body}
        if status in (200, 202) and body.get("status") in VERIFY_STATUSES:
            submission_id = body.get("submission_id") or body.get("id")
            offline.need(isinstance(submission_id, str) and bool(submission_id),
                         "AP17 verify response lacks an exact nonempty submission ID")
            record["submission_id"] = submission_id
        write_record(record)
        offline.need(record.get("submission_id"),
                     "AP17 verify intent is durable but response is uncertain; never repeat POST")
        if body.get("status") != "ACCEPTED":
            return record
    else:
        offline.need(record.get("submission_id"),
                     "AP17 verify intent lacks a known submission; never repeat POST")
        status, body = request("GET", "/verify?submission_id=" + record["submission_id"])
        record["last_verify_verdict"] = {"http_status": status, "body": body}
        write_record(record)
        offline.need(status == 200 and body.get("theorem_id") == pins["target_theorem_id"]
                     and isinstance(body.get("id"), str)
                     and body["id"] == record["submission_id"]
                     and body.get("status") in VERIFY_STATUSES,
                     "AP17 verification poll has unknown status, submission, or target")
        if body.get("status") != "ACCEPTED":
            return record

    status, target = request("GET", "/theorems/" + pins["target_theorem_id"])
    offline.need(status == 200 and isinstance(target, dict),
                 "AP17 post-acceptance target GET failed")
    exact_server_target(target, pins, "Proved")
    post = PUB / "post-accepted-target.json"
    post.write_bytes(offline.encode(target))
    record["confirmed_ACCEPTED_and_Proved"] = True
    record["post_accepted_target"] = {"path": offline.rel(post),
                                       "sha256": offline.sha(post)}
    write_record(record)
    return record


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        pins, _, _, value = fast_descriptor()
        offline.exact(FAST, offline.encode(value))
        result = {"prepared": True, "network_used": False,
                  "full_strict_replay_reused": True,
                  "target_theorem_id": pins["target_theorem_id"],
                  "descriptor_sha256": pins["descriptor_sha256"],
                  "multipart_sha256": pins["multipart_sha256"]}
    else:
        result = advance()
    print(json.dumps(result, ensure_ascii=False, indent=2))
