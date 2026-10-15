"""Hash-guard and durably publish the AP19 four-definition provider."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import prepare_analytic_remainder_data_publication as offline


SELF = Path(__file__).resolve()
PUB = offline.DEST
PREPARATION = PUB / "preparation.json"
ONLINE = PUB / "online-preparation-definition.json"
RECORD = PUB / "publication.json"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
JOB_STATES = {"PENDING", "COMPILING", "PUBLISHED", "FAILED", "ERROR"}


def descriptor():
    pins, metadata, payload, raw = offline.frozen()
    offline.need(offline.sha(SELF) == pins["online_wrapper_sha256"],
                 "AP19 reviewed online wrapper hash differs")
    value = {"schema_version": 1,
        "artifact_kind": "ap19-analytic-remainder-four-Def-fast-online-preparation",
        "provider_key": offline.KEY,
        "definition_name": pins["definition_name"],
        "environment": pins["environment"],
        "offline_preparation_sha256": offline.sha(PREPARATION),
        "validation_sha256": pins["validation_sha256"],
        "online_wrapper_sha256": offline.sha(SELF),
        "payload_sha256": offline.sha_bytes(raw),
        "new_POST_requires_fresh_zero_exact_name_environment_matches": True,
        "known_job_is_polled_without_reposting": True,
        "official_job_contract": {"id": "exact durable job id",
                                  "kind": "definition",
                                  "theorem_name": pins["definition_name"]},
        "hash_gate_before_and_after_every_HTTP": True,
        "network_used": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft"}
    return pins, metadata, payload, raw, value


def save(record):
    record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
    RECORD.write_bytes(offline.encode(record))


def advance():
    pins, metadata, payload, raw, expected = descriptor()
    offline.need(ONLINE.is_file() and ONLINE.read_bytes() == offline.encode(expected),
                 "Reviewed AP19 online descriptor differs")
    record = offline.read(RECORD) if RECORD.exists() else {
        "provider_key": offline.KEY,
        "definition_name": payload["definition_name"],
        "environment": pins["environment"], "visibility": "public",
        "preparation_sha256": offline.sha(PREPARATION)}
    offline.need(record.get("provider_key") == offline.KEY
                 and record.get("definition_name") == payload["definition_name"]
                 and record.get("environment") == pins["environment"]
                 and record.get("visibility") == "public"
                 and record.get("preparation_sha256") == offline.sha(PREPARATION),
                 "AP19 durable publication identity differs")
    if "job_id" in record:
        offline.need(isinstance(record["job_id"], str) and bool(record["job_id"]),
                     "AP19 durable publish job ID is not a nonempty string")
    if "definition_id" in record:
        offline.need(isinstance(record["definition_id"], str)
                     and bool(record["definition_id"]),
                     "AP19 durable Definition ID is not a nonempty string")

    spec = importlib.util.spec_from_file_location(
        "p2m_ap19_remainder", offline.ROOT / "scripts/p2m_api.py")
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = None

    def request(method, path, **kwargs):
        nonlocal token
        current = descriptor()
        offline.need(current[:4] == (pins, metadata, payload, raw)
                     and ONLINE.read_bytes() == offline.encode(current[4]),
                     "AP19 frozen request inputs changed before HTTP")
        if token is None:
            token = api.get_token()
        status, body_raw = api._request(method, path, token=token, **kwargs)
        after = descriptor()
        offline.need(after[:4] == (pins, metadata, payload, raw)
                     and ONLINE.read_bytes() == offline.encode(after[4]),
                     "AP19 frozen request inputs changed after HTTP")
        try:
            body = json.loads(body_raw)
        except json.JSONDecodeError:
            body = {"raw_body": body_raw}
        return status, body_raw, body

    def evidence(status, body_raw, body):
        return {"http_status": status, "raw_body_utf8": body_raw,
                "raw_body_sha256": offline.sha_bytes(body_raw.encode("utf-8")),
                "body": body}

    def readback(definition_id):
        status, body_raw, body = request(
            "GET", "/theorems/" + quote(definition_id, safe=""))
        record["target_readback"] = evidence(status, body_raw, body)
        save(record)
        offline.need(status == 200 and body.get("theorem_id") == definition_id
                     and body.get("theorem_name") == payload["definition_name"]
                     and body.get("status") == "Definition"
                     and body.get("mathlib_rev") == pins["environment"]
                     and body.get("visibility") == "public"
                     and body.get("deprecated_at") is None
                     and body.get("definition") == payload["definition"],
                     "AP19 exact Definition readback differs")
        return body

    save(record)
    if record.get("publish_intent"):
        if record.get("definition_id"):
            readback(record["definition_id"])
            return record
        offline.need(record.get("job_id"),
                     "AP19 durable POST intent has no known job; never repeat POST")
    elif record.get("definition_id"):
        readback(record["definition_id"])
        return record
    else:
        pages, matches, offset = [], [], 0
        while True:
            route = ("/theorems?theorem_name=" + quote(payload["definition_name"])
                     + "&env=" + pins["environment"]
                     + "&limit=100&offset=" + str(offset))
            status, body_raw, body = request("GET", route)
            offline.need(status == 200 and isinstance(body.get("theorems"), list)
                         and type(body.get("total")) is int and body["total"] >= 0,
                         "AP19 exact Definition-name query failed")
            page = body["theorems"]
            pages.append({"route": route, **evidence(status, body_raw, body)})
            matches.extend(row for row in page
                           if row.get("theorem_name") == payload["definition_name"]
                           and row.get("mathlib_rev") == pins["environment"])
            offset += len(page)
            if offset >= body["total"]:
                break
            offline.need(bool(page), "AP19 exact-name pagination ended early")
        record["fresh_exact_name_lookup"] = {"pages": pages, "matches": matches}
        save(record)
        offline.need(len(matches) <= 1, "AP19 duplicate exact Definition name exists")
        if matches:
            definition_id = matches[0].get("theorem_id")
            offline.need(isinstance(definition_id, str) and definition_id,
                         "AP19 exact match lacks Definition ID")
            readback(definition_id)
            record["definition_id"] = definition_id
            record["reused_exact_existing_definition"] = True
            save(record)
            return record
        status, body_raw, environments = request("GET", "/environments")
        record["environment_readback"] = evidence(status, body_raw, environments)
        save(record)
        offline.need(status == 200 and any(
            row.get("mathlib_rev") == pins["environment"]
            and row.get("toolchain") == TOOLCHAIN
            for row in environments.get("environments", [])),
            "AP19 pinned environment unavailable; no POST sent")
        record["publish_intent"] = {
            "at_utc": datetime.now(timezone.utc).isoformat(),
            "endpoint": "/submit-definition",
            "definition_name": payload["definition_name"],
            "environment": pins["environment"], "visibility": "public",
            "payload": payload, "payload_sha256": pins["payload_sha256"],
            "provider_source_sha256": pins["provider_source_sha256"],
            "validation_sha256": pins["validation_sha256"]}
        save(record)
        status, body_raw, body = request("POST", "/submit-definition",
                                         raw_body=raw, ctype="application/json")
        record["publish_response"] = evidence(status, body_raw, body)
        job_id = body.get("job_id")
        if status == 202 and body.get("definition_name") == payload["definition_name"]:
            offline.need(isinstance(job_id, str) and job_id,
                         "AP19 Definition POST response lacks job ID")
            record["job_id"] = job_id
        save(record)
        offline.need(record.get("job_id"),
                     "AP19 POST is uncertain; intent is durable and POST must not repeat")
        return record

    status, body_raw, body = request(
        "GET", "/publish-jobs/" + quote(record["job_id"], safe=""))
    record["last_publish_verdict"] = evidence(status, body_raw, body)
    save(record)
    offline.need(status == 200
                 and isinstance(body.get("id"), str)
                 and body["id"] == record["job_id"]
                 and body.get("kind") == "definition"
                 and body.get("theorem_name") == payload["definition_name"]
                 and body.get("status") in JOB_STATES
                 and ("job_id" not in body or body["job_id"] == record["job_id"])
                 and ("definition_name" not in body or
                      body["definition_name"] == payload["definition_name"]),
                 "AP19 publish job id/kind/name/state differs")
    if body["status"] == "PUBLISHED":
        definition_id = body.get("definition_id") or body.get("theorem_id")
        offline.need(isinstance(definition_id, str) and definition_id,
                     "AP19 Published job lacks Definition ID")
        record["definition_id"] = definition_id
        save(record)
        readback(definition_id)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider", choices=[offline.KEY], default=offline.KEY)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        pins, _, _, _, value = descriptor()
        offline.exact(ONLINE, offline.encode(value))
        result = {"prepared": True, "provider": offline.KEY,
                  "network_used": False, "strict_replay_reused_by_hash": True,
                  "payload_sha256": pins["payload_sha256"],
                  "proposal_status": "Draft"}
    else:
        record = advance()
        result = {"advanced": True, "provider": offline.KEY,
                  "definition_name": record.get("definition_name"),
                  "job_id": record.get("job_id"),
                  "definition_id": record.get("definition_id"),
                  "status": record.get("last_publish_verdict", {}).get("body", {}).get("status")}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
