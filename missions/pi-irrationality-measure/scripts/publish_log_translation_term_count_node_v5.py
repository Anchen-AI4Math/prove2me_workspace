"""Hash-guard and durably publish/verify the original AP20 translation-count logarithm theorem.

``--prepare-only`` is pure and creates the fast descriptor after the offline
wrapper has completed its one strict replay.  ``--advance`` performs at most
one durable state transition: exact lookup, theorem publication/poll, or proof
verification/poll.  Every HTTP call is surrounded by the full frozen hash gate.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import prepare_log_translation_term_count_publication_v5 as offline


SELF = Path(__file__).resolve()
PUB = offline.DEST
PREPARATION = PUB / "preparation.json"
ONLINE = PUB / "online-preparation-driver.json"
RECORD = PUB / "publication.json"
ENV = offline.ENV
TOOLCHAIN = "leanprover/lean4:v4.33.1"
PUBLISH_STATES = {"PENDING", "COMPILING", "PUBLISHED", "FAILED", "ERROR"}
VERIFY_STATES = {"PENDING", "COMPILING", "ACCEPTED", "SKETCH_ACCEPTED",
                 "CE", "WA", "SORRY", "FAILED", "ERROR"}


def descriptor():
    manifest, metadata, payloads, pins = offline.frozen()
    offline.need(offline.sha(SELF) == pins["online_wrapper_sha256"],
                 "AP20 translation-count corrected online wrapper hash differs")
    value = {
        "schema_version": 1,
        "artifact_kind": "ap20-log-translation-count-fast-online-preparation",
        "theorem_name": pins["theorem_name"],
        "environment": pins["environment"],
        "full_strict_replay_preparation_sha256": offline.sha(PREPARATION),
        "full_strict_replay_validation_sha256": pins["validation_sha256"],
        "online_wrapper_sha256": offline.sha(SELF),
        "manifest_sha256": offline.sha(PUB / "manifest.json"),
        "metadata_sha256": offline.sha(PUB / "metadata.json"),
        "validation_copy_sha256": offline.sha(PUB / "validation.json"),
        "wire_theorem_sha256": offline.sha(PUB / "wire-theorem-source.lean"),
        "payload_sha256": pins["payload_sha256"],
        "authoritative_prior_exact_match_count": 0,
        "new_theorem_POST_requires_fresh_zero_exact_name_environment_matches": True,
        "known_publish_job_is_polled_without_reposting": True,
        "known_verify_submission_is_polled_without_reposting": True,
        "hash_gate_before_and_after_every_HTTP": True,
        "network_used": False,
        "API_used": False,
        "submission_ready": False,
        "proposal_status": "Draft",
    }
    return manifest, metadata, payloads, pins, value


def save(record):
    record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
    RECORD.write_bytes(offline.encode(record))


def advance():
    manifest, metadata, payloads, pins, expected = descriptor()
    offline.need(ONLINE.is_file() and ONLINE.read_bytes() == offline.encode(expected),
                 "Reviewed AP20 translation-count online descriptor differs")
    publish = json.loads(payloads["publish-payload.json"])
    problem = publish["problems"][0]
    verify = json.loads(payloads["verification-payload.json"])
    record = offline.read(RECORD) if RECORD.exists() else {
        "theorem_name": pins["theorem_name"],
        "environment": ENV,
        "visibility": "public",
        "proposal_status": "Draft",
        "preparation_sha256": offline.sha(PREPARATION),
    }
    offline.need(record.get("theorem_name") == pins["theorem_name"]
                 and record.get("environment") == ENV
                 and record.get("visibility") == "public"
                 and record.get("preparation_sha256") == offline.sha(PREPARATION),
                 "AP20 translation-count durable publication identity differs")
    if record.get("verify_intent"):
        multipart = PUB / "verification-request.multipart"
        offline.need(multipart.is_file()
                     and offline.sha(multipart) == record["verify_intent"]["multipart_sha256"],
                     "Durable proof POST multipart evidence changed")

    spec = importlib.util.spec_from_file_location(
        "p2m_ap20_log_translation_count_v5", offline.ROOT / "scripts/p2m_api.py")
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = None

    def request(method, path, **kwargs):
        nonlocal token
        if record.get("verify_intent"):
            offline.need(offline.sha(PUB / "verification-request.multipart") ==
                         record["verify_intent"]["multipart_sha256"],
                         "Durable proof multipart changed before HTTP")
        current = descriptor()
        offline.need(current[0] == manifest and current[1] == metadata
                     and current[2] == payloads and current[3] == pins
                     and ONLINE.read_bytes() == offline.encode(current[4]),
                     "AP20 translation-count frozen request inputs changed before HTTP")
        if token is None:
            token = api.get_token()
        status, raw = api._request(method, path, token=token, **kwargs)
        current_after = descriptor()
        if record.get("verify_intent"):
            offline.need(offline.sha(PUB / "verification-request.multipart") ==
                         record["verify_intent"]["multipart_sha256"],
                         "Durable proof multipart changed after HTTP")
        offline.need(current_after[0] == manifest and current_after[1] == metadata
                     and current_after[2] == payloads and current_after[3] == pins
                     and ONLINE.read_bytes() == offline.encode(current_after[4]),
                     "AP20 translation-count frozen request inputs changed after HTTP")
        try:
            body = json.loads(raw)
        except json.JSONDecodeError:
            body = {"raw_body": raw}
        return status, raw, body

    def evidence(status, raw, body):
        return {"http_status": status, "raw_body_utf8": raw,
                "raw_body_sha256": offline.digest(raw.encode("utf-8")),
                "body": body}

    def readback(theorem_id, label):
        status, raw, body = request("GET", "/theorems/" + quote(theorem_id, safe=""))
        record[label] = evidence(status, raw, body)
        save(record)
        offline.need(status == 200 and body.get("theorem_id") == theorem_id
                     and body.get("theorem_name") == manifest["theorem_name"]
                     and body.get("mathlib_rev") == ENV
                     and body.get("visibility") == "public"
                     and body.get("deprecated_at") is None
                     and body.get("preamble") == manifest["preamble"]
                     and body.get("formal_statement") == manifest["formal_statement"],
                     "AP20 translation-count public target identity/text/environment differs")
        return body

    save(record)

    # Resolve or create the theorem.  A durable intent always prevents replaying
    # an uncertain theorem-publication POST.
    if not record.get("theorem_id") and not record.get("publish_intent"):
        pages, matches, offset = [], [], 0
        while True:
            route = ("/theorems?theorem_name=" + quote(manifest["theorem_name"])
                     + "&env=" + ENV + "&limit=100&offset=" + str(offset))
            status, raw, body = request("GET", route)
            offline.need(status == 200 and isinstance(body.get("theorems"), list)
                         and type(body.get("total")) is int and body["total"] >= 0,
                         "AP20 translation-count fresh exact-name query failed; no POST sent")
            page = body["theorems"]
            pages.append({"route": route, **evidence(status, raw, body)})
            matches.extend(row for row in page
                           if row.get("theorem_name") == manifest["theorem_name"]
                           and row.get("mathlib_rev") == ENV)
            offset += len(page)
            if offset >= body["total"]:
                break
            offline.need(bool(page), "AP20 translation-count exact-name pagination ended early")
        record["fresh_exact_name_lookup"] = {"pages": pages, "matches": matches}
        save(record)
        offline.need(len(matches) <= 1, "AP20 translation-count exact theorem name is ambiguous")
        if matches:
            theorem_id = matches[0].get("theorem_id")
            offline.need(isinstance(theorem_id, str) and theorem_id,
                         "AP20 translation-count exact-name match lacks theorem ID")
            readback(theorem_id, "pre_verify_target_readback")
            record["theorem_id"] = theorem_id
            record["reused_exact_existing_theorem"] = True
            save(record)
        else:
            status, raw, environments = request("GET", "/environments")
            record["environment_readback"] = evidence(status, raw, environments)
            save(record)
            offline.need(status == 200 and any(
                row.get("mathlib_rev") == ENV and row.get("toolchain") == TOOLCHAIN
                for row in environments.get("environments", [])),
                "AP20 translation-count pinned environment unavailable; no POST sent")
            record["publish_intent"] = {
                "at_utc": datetime.now(timezone.utc).isoformat(),
                "endpoint": "/submit-problem",
                "theorem_name": manifest["theorem_name"],
                "environment": ENV,
                "visibility": "public",
                "payload_sha256": pins["payload_sha256"]["publish-payload.json"],
                "payload": publish,
            }
            save(record)
            status, raw, body = request("POST", "/submit-problem",
                                        raw_body=payloads["publish-payload.json"],
                                        ctype="application/json")
            record["publish_response"] = evidence(status, raw, body)
            jobs = body.get("jobs", [])
            if status == 202 and not body.get("errors") and len(jobs) == 1:
                job = jobs[0]
                job_id = job.get("job_id")
                offline.need(job.get("name") == manifest["theorem_name"]
                             and isinstance(job_id, str) and job_id,
                             "AP20 translation-count theorem POST response job identity differs")
                record["job_id"] = job_id
            save(record)
            offline.need(record.get("job_id"),
                         "AP20 translation-count theorem POST is uncertain; intent is durable and POST must not repeat")
            return record

    if not record.get("theorem_id"):
        offline.need(record.get("publish_intent") and record.get("job_id"),
                     "AP20 translation-count durable theorem POST intent has no known job; do not repeat POST")
        status, raw, body = request("GET", "/publish-jobs/" +
                                    quote(record["job_id"], safe=""))
        record["last_publish_verdict"] = evidence(status, raw, body)
        save(record)
        offline.need(status == 200
                     and body.get("id") == record["job_id"]
                     and body.get("kind") == "problem"
                     and body.get("theorem_name") == manifest["theorem_name"]
                     and body.get("status") in PUBLISH_STATES
                     and ("job_id" not in body or body["job_id"] == record["job_id"]),
                     "AP20 translation-count publish job id/kind/name/state differs")
        if body["status"] == "PUBLISHED":
            theorem_id = body.get("theorem_id")
            offline.need(isinstance(theorem_id, str) and theorem_id,
                         "AP20 translation-count Published job lacks theorem ID")
            record["theorem_id"] = theorem_id
            save(record)
            readback(theorem_id, "post_publish_target_readback")
        return record

    theorem_id = record["theorem_id"]
    offline.need(isinstance(theorem_id, str) and theorem_id,
                 "AP20 translation-count durable target theorem ID differs")

    # Resolve or submit the proof.  Existing Proved targets are reused without a
    # proof POST; otherwise the exact frozen solution is submitted once.
    if not record.get("submission_id"):
        current = readback(theorem_id, "pre_verify_target_readback")
        if current.get("status") == "Proved":
            record["confirmed_proved"] = True
            record["existing_proved_reused"] = True
            save(record)
            return record
        offline.need(current.get("status") == "Open",
                     "AP20 translation-count target is neither Open nor Proved")
        offline.need(not record.get("verify_intent"),
                     "AP20 translation-count uncertain proof POST intent recorded; do not repeat POST")
        payload, ctype = api._multipart(
            {"theorem_id": theorem_id, "proof_type": verify["proof_type"],
             "explanation": verify["explanation"]},
            {"file": (verify["file"]["filename"],
                      verify["file"]["utf8"].encode("utf-8"))})
        multipart = PUB / "verification-request.multipart"
        multipart.write_bytes(payload)
        record["verify_intent"] = {
            "at_utc": datetime.now(timezone.utc).isoformat(),
            "endpoint": "/verify", "theorem_id": theorem_id,
            "content_type": ctype,
            "multipart_sha256": offline.digest(payload),
            "solution_sha256": manifest["solution_sha256"],
            "descriptor_sha256": pins["payload_sha256"]["verification-payload.json"],
        }
        save(record)
        status, raw, body = request("POST", "/verify", raw_body=payload, ctype=ctype)
        record["verify_response"] = evidence(status, raw, body)
        submission_id = body.get("submission_id")
        if status in (200, 202) and body.get("status") in {"PENDING", "COMPILING"}:
            offline.need(isinstance(submission_id, str) and submission_id
                         and ("id" not in body or body["id"] == submission_id),
                         "AP20 translation-count proof POST response lacks exact submission ID")
            record["submission_id"] = submission_id
        save(record)
        offline.need(record.get("submission_id"),
                     "AP20 translation-count proof POST is uncertain; intent is durable and POST must not repeat")
        return record

    submission_id = record["submission_id"]
    status, raw, body = request("GET", "/verify?submission_id=" +
                                quote(submission_id, safe=""))
    record["last_verify_verdict"] = evidence(status, raw, body)
    save(record)
    offline.need(status == 200 and body.get("id") == submission_id
                 and body.get("theorem_id") == theorem_id
                 and body.get("status") in VERIFY_STATES
                 and ("submission_id" not in body or body["submission_id"] == submission_id),
                 "AP20 translation-count verification submission id/theorem/state differs")
    if body["status"] == "ACCEPTED":
        post = readback(theorem_id, "post_accepted_target_readback")
        offline.need(post.get("status") == "Proved",
                     "AP20 translation-count ACCEPTED proof did not produce an exact Proved readback")
        record["confirmed_ACCEPTED_and_Proved"] = True
        save(record)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        _, _, _, pins, value = descriptor()
        offline.exact(ONLINE, offline.encode(value))
        result = {"prepared": True, "network_used": False,
                  "strict_replay_reused_by_hash": True,
                  "payload_sha256": pins["payload_sha256"],
                  "proposal_status": "Draft"}
    else:
        record = advance()
        result = {"advanced": True,
                  "theorem_name": record.get("theorem_name"),
                  "job_id": record.get("job_id"),
                  "theorem_id": record.get("theorem_id"),
                  "submission_id": record.get("submission_id"),
                  "publish_status": record.get("last_publish_verdict", {}).get("body", {}).get("status"),
                  "verify_status": record.get("last_verify_verdict", {}).get("body", {}).get("status"),
                  "confirmed_ACCEPTED_and_Proved":
                      record.get("confirmed_ACCEPTED_and_Proved", False)}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()



