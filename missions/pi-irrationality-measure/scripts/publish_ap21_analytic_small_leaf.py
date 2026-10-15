"""Durably verify one frozen AP21 proof on its existing public target."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path

import prepare_ap21_analytic_small_leaf_publication as offline


SELF = Path(__file__).resolve()
VERIFY_STATUSES = {"PENDING", "COMPILING", "SKETCH_ACCEPTED", "ACCEPTED",
                   "CE", "WA", "SORRY", "FAILED", "ERROR"}


def paths(node):
    cfg = offline.config(node)
    dest = cfg["stage_dir"] / "publication"
    return cfg, dest, dest / "preparation.json", dest / "online-preparation.json", dest / "publication.json"


def descriptor(node):
    cfg, dest, preparation, online, record = paths(node)
    pins = offline.hash_gate(node)
    payload = offline.read(dest / "verification-payload.json")
    multipart = (dest / "verification-request.multipart").read_bytes()
    offline.need(payload["theorem_id"] == cfg["theorem_id"]
                 and payload["target_theorem_name"] == cfg["target"]
                 and payload["proof_type"] == "prove"
                 and payload["env"] == offline.ENV
                 and payload["file"]["sha256"] == pins["solution_source_sha256"]
                 and offline.sha(dest / "wire-theorem-source.lean") ==
                     pins["wire_source_sha256"]
                 and offline.digest(multipart) ==
                     pins["artifact_sha256"]["verification-request.multipart"],
                 "Frozen AP21 verify descriptor differs")
    value = {
        "schema_version": 1,
        "artifact_kind": "ap21-analytic-small-leaf-hash-only-online-preparation",
        "node": node, "theorem_id": cfg["theorem_id"],
        "theorem_name": cfg["target"], "proof_type": "prove",
        "full_strict_replay_preparation_sha256": offline.sha(preparation),
        "validation_sha256": pins["validation_sha256"],
        "offline_wrapper_sha256": offline.sha(offline.SELF),
        "online_wrapper_sha256": offline.sha(SELF),
        "descriptor_sha256": offline.sha(dest / "verification-payload.json"),
        "multipart_sha256": offline.digest(multipart),
        "exact_existing_target_only": True,
        "creates_theorem_or_proposal": False,
        "every_HTTP_guard_hash_only": True,
        "network_used": False, "API_used": False, "proposal_status": "Draft"}
    return cfg, dest, preparation, online, record, pins, payload, multipart, value


def exact_target(body, cfg, allowed_statuses):
    _, historical = offline.publication_record(cfg)
    for key in ("theorem_id", "theorem_name", "preamble", "formal_statement",
                "mathlib_rev", "visibility", "deprecated_at", "deprecated_by"):
        offline.need(body.get(key) == historical.get(key),
                     "AP21 public target changed: " + key)
    offline.need(body.get("status") in allowed_statuses
                 and (body["preamble"] + body["formal_statement"]).encode() ==
                     (cfg["stage_dir"] / "publication/wire-theorem-source.lean").read_bytes(),
                 "AP21 public target status or exact wire differs")


def write_record(path, record):
    record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
    path.write_bytes(offline.encode(record))


def advance(node):
    cfg, dest, preparation, online, record_path, pins, payload, multipart, value = descriptor(node)
    offline.need(online.is_file() and online.read_bytes() == offline.encode(value),
                 "Reviewed AP21 online preparation differs")
    record = offline.read(record_path) if record_path.exists() else {
        "node": node, "target_theorem_id": cfg["theorem_id"],
        "target_theorem_name": cfg["target"], "environment": offline.ENV,
        "descriptor_sha256": value["descriptor_sha256"],
        "multipart_sha256": value["multipart_sha256"],
        "creates_theorem_or_proposal": False}
    offline.need(record["node"] == node
                 and record["target_theorem_id"] == cfg["theorem_id"]
                 and record["target_theorem_name"] == cfg["target"]
                 and record["environment"] == offline.ENV
                 and record["descriptor_sha256"] == value["descriptor_sha256"]
                 and record["multipart_sha256"] == value["multipart_sha256"]
                 and record["creates_theorem_or_proposal"] is False,
                 "Durable AP21 proof record identity differs")
    spec = importlib.util.spec_from_file_location("p2m_api_ap21_leaf", offline.API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = None

    def request(method, path, **kwargs):
        nonlocal token
        c2, d2, p2, o2, r2, pins2, payload2, multipart2, value2 = descriptor(node)
        offline.need(c2["theorem_id"] == cfg["theorem_id"] and pins2 == pins
                     and payload2 == payload and multipart2 == multipart
                     and o2.read_bytes() == offline.encode(value2),
                     "Frozen AP21 request inputs changed")
        if token is None:
            token = api.get_token()
        status, raw = api._request(method, path, token=token, **kwargs)
        offline.hash_gate(node, pins)
        try:
            return status, json.loads(raw)
        except json.JSONDecodeError:
            return status, {"raw_body": raw}

    if not record.get("verify_intent") and not record.get("reused_existing_Proved"):
        status, target = request("GET", "/theorems/" + cfg["theorem_id"])
        offline.need(status == 200 and isinstance(target, dict),
                     "AP21 pre-verify target GET failed")
        exact_target(target, cfg, {"Open", "Proved"})
        pre = dest / "pre-verify-target.json"
        pre.write_bytes(offline.encode(target))
        record["pre_verify_target"] = {"path": offline.pin_key(pre), "sha256": offline.sha(pre)}
        if target["status"] == "Proved":
            record["reused_existing_Proved"] = True
            record["own_ACCEPTED_counted"] = False
            record["reuse_reason"] = (
                "Target was already Proved before this wrapper created an own verification submission")
            write_record(record_path, record)
            return record
        record["verify_intent"] = {
            "at_utc": datetime.now(timezone.utc).isoformat(),
            "endpoint": "/verify", "theorem_id": cfg["theorem_id"],
            "proof_type": "prove", "descriptor_sha256": value["descriptor_sha256"],
            "multipart_sha256": value["multipart_sha256"],
            "content_type": pins["multipart_content_type"]}
        write_record(record_path, record)
        status, body = request("POST", "/verify", raw_body=multipart,
                               ctype=pins["multipart_content_type"])
        record["verify_response"] = {"http_status": status, "body": body}
        if (status in (200, 202) and body.get("status") in VERIFY_STATUSES
                and body.get("theorem_id") == cfg["theorem_id"]):
            submission_id = body.get("submission_id") or body.get("id")
            offline.need(isinstance(submission_id, str) and bool(submission_id),
                         "AP21 verify response lacks a nonempty submission ID")
            offline.need(body.get("submission_id") in (None, submission_id)
                         and body.get("id") in (None, submission_id),
                         "AP21 verify response has conflicting submission IDs")
            record["submission_id"] = submission_id
        write_record(record_path, record)
        offline.need(record.get("submission_id"),
                     "AP21 verify intent is durable but response is uncertain; never repeat POST")
        if body.get("status") != "ACCEPTED":
            return record
    elif record.get("verify_intent"):
        offline.need(record.get("submission_id"),
                     "AP21 verify intent has no known submission; never repeat POST")
        status, body = request("GET", "/verify?submission_id=" + record["submission_id"])
        record["last_verify_verdict"] = {"http_status": status, "body": body}
        write_record(record_path, record)
        offline.need(status == 200 and isinstance(body.get("id"), str)
                     and body["id"] == record["submission_id"]
                     and body.get("submission_id") in (None, record["submission_id"])
                     and body.get("theorem_id") == cfg["theorem_id"]
                     and body.get("status") in VERIFY_STATUSES,
                     "AP21 poll has unknown submission, target, or status")
        if body["status"] != "ACCEPTED":
            return record
    else:
        offline.need(record.get("reused_existing_Proved") is True
                     and record.get("own_ACCEPTED_counted") is False,
                     "AP21 terminal reuse evidence differs")
        return record

    status, target = request("GET", "/theorems/" + cfg["theorem_id"])
    offline.need(status == 200 and isinstance(target, dict),
                 "AP21 post-acceptance target GET failed")
    exact_target(target, cfg, {"Proved"})
    post = dest / "post-accepted-target.json"
    post.write_bytes(offline.encode(target))
    record["confirmed_ACCEPTED_and_Proved"] = True
    record["own_ACCEPTED_counted"] = True
    record["post_accepted_target"] = {"path": offline.pin_key(post), "sha256": offline.sha(post)}
    write_record(record_path, record)
    return record


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--node", choices=("index", "row"), required=True)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        cfg, dest, preparation, online, record, pins, payload, multipart, value = descriptor(args.node)
        offline.exact(online, offline.encode(value))
        result = {"prepared": True, "node": args.node, "network_used": False,
                  "full_strict_replay_reused": True,
                  "theorem_id": cfg["theorem_id"],
                  "descriptor_sha256": value["descriptor_sha256"],
                  "multipart_sha256": value["multipart_sha256"]}
    else:
        result = advance(args.node)
    print(json.dumps(result, ensure_ascii=False, indent=2))
