"""Durably publish AP18 multiplicity with the exact v0.12.4 job schema."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import prepare_collision_multiplicity_publication_v2 as offline


SELF = Path(__file__).resolve()
PUB = offline.DEST
PREPARATION = PUB / "prepare-record.json"
ONLINE = PUB / "online-preparation-definition.json"
RECORD = PUB / "publication.json"


def frozen():
    pins = offline.read(PREPARATION)
    offline.hash_gate(pins)
    offline.need(offline.sha(SELF) == pins["online_wrapper_sha256"]
                 and pins["route"] == "/submit-definition"
                 and pins["expected_readback_status"] == "Definition",
                 "AP18 reviewed v2 online wrapper/route differs")
    metadata = offline.read(PUB / "metadata.json")
    payload = offline.read(PUB / "publish-payload.json")
    raw = (PUB / "publish-payload.json").read_bytes()
    provider = offline.stage.STAGE / offline.stage.PROVIDER_FILE
    offline.need(offline.sha_bytes(raw) == pins["payload_sha256"]
                 and payload["definition"].encode("utf-8") == provider.read_bytes()
                 and payload["definition_name"] == pins["definition_name"]
                 and payload["env"] == pins["environment"]
                 and payload["private"] is False,
                 "AP18 exact Definition payload differs")
    return pins, metadata, payload, raw


def descriptor():
    pins, metadata, payload, raw = frozen()
    value = {"schema_version": 1,
        "artifact_kind": "ap18-collision-multiplicity-fast-online-preparation-v2",
        "definition_name": pins["definition_name"],
        "environment": pins["environment"],
        "offline_prepare_record_sha256": offline.sha(PREPARATION),
        "online_wrapper_sha256": offline.sha(SELF),
        "payload_sha256": offline.sha_bytes(raw),
        "http_lookup_scope": "exact definition name and pinned environment only",
        "publish_job_response_contract": pins["publish_job_response_contract"],
        "hash_gate_before_and_after_every_HTTP": True,
        "durable_intent_before_POST": True,
        "network_used": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft"}
    return pins, metadata, payload, raw, value


def write_record(record):
    record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
    RECORD.write_bytes(offline.encode(record))


def advance():
    pins, metadata, payload, raw, expected_descriptor = descriptor()
    offline.need(ONLINE.is_file() and ONLINE.read_bytes() == offline.encode(expected_descriptor),
                 "AP18 reviewed v2 online descriptor differs")
    record = offline.read(RECORD) if RECORD.exists() else {
        "definition_name": payload["definition_name"],
        "environment": pins["environment"], "visibility": "public"}
    offline.need(record.get("definition_name") == payload["definition_name"]
                 and record.get("environment") == pins["environment"]
                 and record.get("visibility") == "public"
                 and record.get("publish_payload_sha256", pins["payload_sha256"]) ==
                     pins["payload_sha256"],
                 "AP18 durable publication identity differs")
    spec = importlib.util.spec_from_file_location("p2m_api_ap18_multiplicity_v2",
                                                   offline.ROOT / "scripts/p2m_api.py")
    api = importlib.util.module_from_spec(spec); spec.loader.exec_module(api)
    token = None

    def request(method, path, **kwargs):
        nonlocal token
        current = descriptor()
        offline.need(current[0] == pins and current[1] == metadata
                     and current[2] == payload and current[3] == raw
                     and ONLINE.read_bytes() == offline.encode(current[4]),
                     "AP18 frozen v2 request inputs changed")
        if token is None: token = api.get_token()
        status, body_raw = api._request(method, path, token=token, **kwargs)
        offline.hash_gate(pins)
        try: return status, json.loads(body_raw)
        except json.JSONDecodeError: return status, {"raw_body": body_raw}

    def exact_readback(definition_id):
        status, body = request("GET", "/theorems/" + quote(definition_id, safe=""))
        record["target_readback"] = {"http_status": status, "body": body}
        write_record(record)
        offline.need(status == 200 and body.get("theorem_id") == definition_id
                     and body.get("theorem_name") == payload["definition_name"]
                     and body.get("status") == "Definition"
                     and body.get("mathlib_rev") == pins["environment"]
                     and body.get("visibility") == "public"
                     and body.get("definition") == payload["definition"],
                     "AP18 Definition readback differs")
        return body

    if record.get("publish_intent"):
        if record.get("definition_id"):
            exact_readback(record["definition_id"]); return record
        offline.need(record.get("job_id"),
                     "AP18 durable POST intent has no known job; never repeat POST")
    elif record.get("definition_id"):
        exact_readback(record["definition_id"]); return record
    else:
        matches, offset = [], 0
        while True:
            status, body = request("GET", "/theorems?theorem_name=" +
                quote(payload["definition_name"]) + "&env=" + pins["environment"] +
                f"&limit=100&offset={offset}")
            offline.need(status == 200 and isinstance(body.get("theorems"), list)
                         and isinstance(body.get("total"), int) and body["total"] >= 0,
                         "AP18 exact Definition-name query failed")
            page = body["theorems"]
            matches.extend(row for row in page
                           if row.get("theorem_name") == payload["definition_name"])
            offset += len(page)
            if offset >= body["total"]: break
            offline.need(bool(page), "AP18 pagination ended before its total")
        if matches:
            offline.need(len(matches) == 1 and isinstance(matches[0].get("theorem_id"), str)
                         and bool(matches[0]["theorem_id"]),
                         "AP18 duplicate exact Definition name exists")
            result = exact_readback(matches[0]["theorem_id"])
            record.update({"definition_id": result["theorem_id"],
                           "publish_payload_sha256": pins["payload_sha256"],
                           "reused_exact_existing_definition": True})
            write_record(record); return record
        status, environments = request("GET", "/environments")
        offline.need(status == 200 and any(
            row.get("mathlib_rev") == pins["environment"]
            and row.get("toolchain") == "leanprover/lean4:v4.33.1"
            for row in environments.get("environments", [])),
            "AP18 pinned environment unavailable; no POST sent")
        record["publish_payload_sha256"] = pins["payload_sha256"]
        record["publish_intent"] = {"at_utc": datetime.now(timezone.utc).isoformat(),
            "endpoint": "/submit-definition", "definition_name": payload["definition_name"],
            "environment": pins["environment"], "visibility": "public",
            "payload": payload, "payload_sha256": pins["payload_sha256"],
            "bundle_source_sha256": pins["bundle_source_sha256"],
            "bundle_manifest_sha256": pins["bundle_manifest_sha256"],
            "validation_sha256": pins["validation_sha256"]}
        write_record(record)
        status, body = request("POST", "/submit-definition", raw_body=raw,
                               ctype="application/json")
        record["publish_response"] = {"http_status": status, "body": body}
        job_id = body.get("job_id")
        if status == 202 and body.get("definition_name") == payload["definition_name"]:
            offline.need(isinstance(job_id, str) and bool(job_id),
                         "AP18 submit response lacks a nonempty job ID")
            record["job_id"] = job_id
        write_record(record)
        offline.need(record.get("job_id"),
                     "AP18 POST outcome is uncertain; intent is durable and POST must not repeat")
        return record

    status, body = request("GET", "/publish-jobs/" + quote(record["job_id"], safe=""))
    record["last_publish_verdict"] = {"http_status": status, "body": body}
    write_record(record)
    offline.need(status == 200
                 and isinstance(body.get("id"), str) and body["id"] == record["job_id"]
                 and body.get("kind") == "definition"
                 and body.get("theorem_name") == payload["definition_name"]
                 and body.get("status") in {"PUBLISHED", "FAILED", "ERROR", "PENDING", "COMPILING"}
                 and ("job_id" not in body or body["job_id"] == record["job_id"])
                 and ("definition_name" not in body or
                      body["definition_name"] == payload["definition_name"]),
                 "AP18 publish job identity, kind, name, or state differs")
    if body["status"] == "PUBLISHED":
        definition_id = body.get("definition_id") or body.get("theorem_id")
        offline.need(isinstance(definition_id, str) and bool(definition_id),
                     "AP18 Published job lacks a Definition ID")
        record["definition_id"] = definition_id; write_record(record)
        exact_readback(definition_id)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider", choices=list(offline.stage.CONFIGS), default=offline.KEY)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        pins, _, _, _, value = descriptor()
        offline.exact(ONLINE, offline.encode(value))
        result = {"prepared": True, "provider": offline.KEY, "network_used": False,
                  "payload_sha256": pins["payload_sha256"], "proposal_status": "Draft"}
    else:
        record = advance()
        result = {"advanced": True, "provider": offline.KEY,
                  "definition_name": record.get("definition_name"),
                  "job_id": record.get("job_id"), "definition_id": record.get("definition_id"),
                  "status": record.get("last_publish_verdict", {}).get("body", {}).get("status")}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__": main()
