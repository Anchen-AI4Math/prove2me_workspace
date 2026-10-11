"""Resume the exact saved f1 submission by polling it, never resubmitting.

Default/--check-only performs the frozen publisher's full read-only preparation
and pin replay, then reports the saved target/submission IDs without importing
the API client. --advance is the only mode that loads credentials and performs
GET requests. It accepts only the exact saved submission's ACCEPTED response
plus a fresh exact-target Proved readback, then archives the prior record and
stores that receipt. No Lean or POST request is used by this helper.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from urllib.parse import quote

import publish_formal_log_proof_node as publisher
import formal_log_node_security_pins as securitypins


EXPECTED_THEOREM_ID = "6a63ca41-070c-4b8a-86e1-dc41228ab921"
EXPECTED_SUBMISSION_ID = "fdd3e549-4921-432a-80a9-53b1e4fb46c1"
EXPECTED_THEOREM_NAME = "OAI.PiExponent.FormalLogTruncation.liftSeries_eq_toMvPowerSeries"
ENV = publisher.ENV
TOOLCHAIN = publisher.TOOLCHAIN


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def confined_publication_files(publication_dir: Path):
    stage = publication_dir.parent.resolve()
    if stage != publisher.DEFAULT_STAGE.resolve() or publication_dir.resolve().parent != stage:
        raise ValueError("Expected the fixed f1 publication directory")
    if publication_dir.is_symlink():
        raise ValueError("Publication directory must not be a symlink")
    record_path = publication_dir / "publication.json"
    prep_path = publication_dir / "preparation.json"
    if record_path.is_symlink() or prep_path.is_symlink():
        raise ValueError("Publication state files must not be symlinks")
    return record_path, prep_path


def check_record_binding(publication_dir: Path, manifest: dict, pins: dict) -> tuple[dict, bytes]:
    record_path, prep_path = confined_publication_files(publication_dir)
    if not record_path.is_file() or not prep_path.is_file():
        raise ValueError("The exact f1 publication record and offline preparation are required")
    record_bytes = record_path.read_bytes()
    record = publisher.read(record_path)
    expected_binding = publisher.target_binding(manifest, pins)
    if (record.get("schema_version") != 1
            or record.get("artifact_kind") != "formal-log-proof-node-publication-record"
            or record.get("theorem_name") != EXPECTED_THEOREM_NAME
            or record.get("environment") != ENV
            or record.get("target_binding") != expected_binding
            or record.get("preparation") != pins
            or manifest.get("theorem_name") != EXPECTED_THEOREM_NAME):
        raise ValueError("Publication record does not bind the exact certified f1 target")
    if record.get("theorem_id") != EXPECTED_THEOREM_ID:
        raise ValueError("Saved theorem ID differs from the pinned f1 theorem")
    if record.get("submission_id") != EXPECTED_SUBMISSION_ID:
        raise ValueError("Saved submission ID differs from the pinned f1 submission")
    pub_intent = record.get("publication_intent")
    if (not isinstance(pub_intent, dict)
            or pub_intent.get("endpoint") != "/submit-problem"
            or pub_intent.get("theorem_name") != EXPECTED_THEOREM_NAME
            or pub_intent.get("environment") != ENV
            or pub_intent.get("payload_sha256") != pins["payload_sha256"]["publish-payload.json"]):
        raise ValueError("Publication intent is not bound to the exact f1 payload")
    intent = record.get("verification_intent")
    if (not isinstance(intent, dict) or intent.get("endpoint") != "/verify"
            or intent.get("theorem_id") != EXPECTED_THEOREM_ID
            or intent.get("descriptor_sha256") != pins["payload_sha256"]["verification-payload.json"]):
        raise ValueError("Verification intent is not bound to the exact f1 theorem and payload")
    response = record.get("verification_response")
    if (not isinstance(response, dict) or response.get("http_status") != 200
            or response.get("body", {}).get("submission_id") != EXPECTED_SUBMISSION_ID):
        raise ValueError("Saved verification response does not establish this exact submission ID")
    job_id = record.get("job_id")
    publication_response = record.get("publication_response", {})
    # The durable job ID and target binding are retained even when the original
    # queue response omits details in its historical body.
    if not isinstance(job_id, str) or not job_id:
        raise ValueError("Publication record has no durable job ID")
    if record.get("existing_proved_reused") is True and record.get("own_submission_receipt"):
        receipt = record["own_submission_receipt"]
        if (receipt.get("submission_id") != EXPECTED_SUBMISSION_ID
                or receipt.get("theorem_id") != EXPECTED_THEOREM_ID
                or receipt.get("status") != "ACCEPTED"
                or record.get("accepted") is not True
                or record.get("confirmed_proved") is not True):
            raise ValueError("Existing own-submission receipt is malformed")
    return record, record_bytes


def offline_review(stage_value, metadata_value):
    stage = publisher.stage_path(stage_value)
    metadata_file = publisher.confined_file(metadata_value, base=publisher.TASK)
    result = publisher.prepare(stage, metadata_file, write=False)
    _, publication_dir, evidence, manifest, metadata, pins, payloads = result
    record, record_bytes = check_record_binding(publication_dir, manifest, pins)
    return stage, publication_dir, evidence, manifest, metadata, pins, payloads, record, record_bytes


def request_guard(stage: Path, publication_dir: Path, manifest: dict, pins: dict,
                  record_path: Path, expected_record_bytes: bytes) -> None:
    metadata_path = publisher.confined_file(pins["metadata_file"], base=publisher.TASK)
    securitypins.assert_security_pins(pins["security_pins"])
    if (publication_dir.is_symlink()
            or record_path.is_symlink()
            or (publication_dir / "preparation.json").is_symlink()
            or (publication_dir / "preparation.json").read_bytes() != publisher.encode(pins)
            or record_path.read_bytes() != expected_record_bytes
            or publisher.sha(stage / "manifest.json") != pins["manifest_sha256"]
            or publisher.sha(stage / "formal-node-validation.json") != pins["certificate_sha256"]
            or publisher.sha(Path(publisher.__file__).resolve()) != pins["publisher_sha256"]
            or publisher.sha(Path(publisher.checker.__file__).resolve()) != pins["checker_sha256"]
            or pins["security_helper_sha256"] != publisher.SECURITY_HELPER_SHA256
            or publisher.sha(Path(securitypins.__file__).resolve()) != publisher.SECURITY_HELPER_SHA256
            or publisher.sha(publisher.ROOT / "scripts/p2m_api.py") != pins["api_client_sha256"]
            or publisher.sha(metadata_path) != pins["metadata_sha256"]):
        raise ValueError("Reviewed f1 source, certificate, metadata, or durable record changed")
    for filename, expected in pins["payload_sha256"].items():
        payload_path = publication_dir / filename
        if payload_path.is_symlink() or publisher.sha(payload_path) != expected:
            raise ValueError("Reviewed f1 payload changed: " + filename)
    if manifest.get("theorem_name") != EXPECTED_THEOREM_NAME or manifest.get("mathlib_rev", ENV) != ENV:
        raise ValueError("Pinned target name/environment changed")


def import_api_after_explicit_advance():
    api_path = publisher.ROOT / "scripts/p2m_api.py"
    spec = importlib.util.spec_from_file_location("formal_log_poll_p2m_api", api_path)
    if spec is None or spec.loader is None:
        raise ValueError("Could not load the configured Prove2Me API client")
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    return api


def parse_response(status: int, raw: str) -> dict:
    try:
        body = json.loads(raw)
    except (TypeError, json.JSONDecodeError) as exc:
        raise ValueError("API returned a non-JSON response") from exc
    if not isinstance(body, dict):
        raise ValueError("API response must be a JSON object")
    return {"http_status": status, "body": body}


def check_target_readback(readback: dict, manifest: dict) -> None:
    if (readback.get("http_status") != 200
            or readback["body"].get("theorem_id") != EXPECTED_THEOREM_ID
            or readback["body"].get("theorem_name") != EXPECTED_THEOREM_NAME
            or readback["body"].get("mathlib_rev") != ENV
            or readback["body"].get("visibility") != "public"
            or readback["body"].get("deprecated_at") is not None
            or readback["body"].get("formal_statement") != manifest.get("formal_statement")
            or readback["body"].get("preamble") != manifest.get("preamble")
            or readback["body"].get("status") != "Proved"):
        raise ValueError("Fresh target readback is not the exact public Proved f1 theorem")


def archive_and_store_receipt(publication_dir: Path, record_path: Path, original_bytes: bytes,
                              record: dict, verify_result: dict, target_result: dict) -> dict:
    before_sha = sha_bytes(original_bytes)
    archive_dir = publication_dir / "poll-history"
    if archive_dir.is_symlink():
        raise ValueError("Poll history directory must not be a symlink")
    archive_dir.mkdir(exist_ok=True)
    if archive_dir.resolve().parent != publication_dir.resolve():
        raise ValueError("Poll history directory escaped publication")
    archive_path = archive_dir / f"original-publication-{before_sha}.json"
    if archive_path.is_symlink():
        raise ValueError("Original publication archive must not be a symlink")
    if archive_path.exists() and archive_path.read_bytes() != original_bytes:
        raise ValueError("Existing original-record archive has different bytes")
    if not archive_path.exists():
        archive_path.write_bytes(original_bytes)
    record["last_verify_verdict"] = verify_result
    record["accepted"] = True
    record["confirmed_proved"] = True
    record["existing_proved_reused"] = False
    record["target_readback"] = target_result
    record["own_submission_receipt"] = {
        "submission_id": EXPECTED_SUBMISSION_ID,
        "theorem_id": EXPECTED_THEOREM_ID,
        "theorem_name": EXPECTED_THEOREM_NAME,
        "environment": ENV,
        "status": "ACCEPTED",
        "accepted_at_utc": datetime.now(timezone.utc).isoformat(),
        "verification_response": verify_result,
        "proved_target_readback": target_result,
    }
    record["prior_publication_record_archive"] = {
        "path": archive_path.relative_to(publisher.TASK).as_posix(),
        "sha256": before_sha,
    }
    record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
    encoded = publisher.encode(record)
    temp_path = record_path.with_name(record_path.name + ".poll-new")
    if temp_path.is_symlink():
        raise ValueError("Temporary publication record must not be a symlink")
    if temp_path.exists() and temp_path.read_bytes() != encoded:
        raise ValueError("Existing temporary receipt file has different bytes")
    if record_path.read_bytes() != original_bytes:
        raise ValueError("Publication record changed before receipt persistence")
    temp_path.write_bytes(encoded)
    temp_path.replace(record_path)
    return {"record_sha256": sha_bytes(encoded), "archive_path": str(archive_path),
            "archive_sha256": before_sha}


def advance(stage: Path, publication_dir: Path, evidence: dict, manifest: dict, pins: dict,
            record: dict, original_bytes: bytes) -> dict:
    record_path, _ = confined_publication_files(publication_dir)
    if record.get("own_submission_receipt"):
        receipt = record["own_submission_receipt"]
        if (receipt.get("submission_id") == EXPECTED_SUBMISSION_ID
                and receipt.get("theorem_id") == EXPECTED_THEOREM_ID
                and receipt.get("status") == "ACCEPTED"
                and record.get("confirmed_proved") is True
                and record.get("existing_proved_reused") is False):
            return {"result": "exact own Accepted/Proved receipt already recorded", "api_requests": 0}
        raise ValueError("Existing own-submission receipt does not match the exact expected final state")
    api = import_api_after_explicit_advance()
    verify_path = "/verify?submission_id=" + quote(EXPECTED_SUBMISSION_ID, safe="")
    theorem_path = "/theorems/" + quote(EXPECTED_THEOREM_ID, safe="")

    def get(path: str) -> dict:
        if path not in (verify_path, theorem_path):
            raise ValueError("Poll helper permits only the pinned verification and theorem GET paths")
        request_guard(stage, publication_dir, manifest, pins, record_path, original_bytes)
        token = api.get_token()
        request_guard(stage, publication_dir, manifest, pins, record_path, original_bytes)
        status, raw = api._request("GET", path, token=token)
        request_guard(stage, publication_dir, manifest, pins, record_path, original_bytes)
        return parse_response(status, raw)

    verify_result = get(verify_path)
    body = verify_result["body"]
    if (verify_result["http_status"] != 200
            or body.get("id") != EXPECTED_SUBMISSION_ID
            or body.get("theorem_id") != EXPECTED_THEOREM_ID
            or body.get("status") != "ACCEPTED"
            or body.get("error_message") not in (None, "")):
        return {"result": "own submission has not returned exact HTTP 200 ACCEPTED; record unchanged",
                "last_verify_verdict": verify_result, "api_requests": 1}

    target_result = get(theorem_path)
    check_target_readback(target_result, manifest)
    # Ensure the original record is still byte-identical after the two GETs.
    if record_path.read_bytes() != original_bytes:
        raise ValueError("Publication record changed while the poll was in flight")
    storage = archive_and_store_receipt(publication_dir, record_path, original_bytes,
                                        record, verify_result, target_result)
    return {"result": "exact own Accepted submission and fresh Proved target recorded",
            "api_requests": 2, "accepted": True, "confirmed_proved": True,
            "existing_proved_reused": False, "submission_id": EXPECTED_SUBMISSION_ID,
            "theorem_id": EXPECTED_THEOREM_ID, **storage}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", default=str(publisher.DEFAULT_STAGE.relative_to(publisher.TASK)))
    parser.add_argument("--metadata-file", default=str(publisher.DEFAULT_METADATA.relative_to(publisher.TASK)))
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check-only", action="store_true", help="Default: full read-only certificate and pin replay")
    mode.add_argument("--advance", action="store_true", help="Explicitly GET the saved submission and target")
    args = parser.parse_args()
    reviewed = offline_review(args.stage, args.metadata_file)
    stage, publication_dir, evidence, manifest, metadata, pins, payloads, record, record_bytes = reviewed
    if args.advance:
        result = advance(stage, publication_dir, evidence, manifest, pins, record, record_bytes)
    else:
        result = {
            "result": "offline review passed; no API client loaded and no request made",
            "theorem_name": EXPECTED_THEOREM_NAME,
            "environment": ENV,
            "theorem_id": record.get("theorem_id"),
            "submission_id": record.get("submission_id"),
            "saved_last_verify_status": record.get("last_verify_verdict", {}).get("body", {}).get("status"),
            "saved_existing_proved_reused": record.get("existing_proved_reused"),
            "own_accepted_receipt_present": bool(record.get("own_submission_receipt")),
            "typed_security_pin_count": len(pins["security_pins"]),
            "api_client_imported": False,
            "credentials_read": False,
            "network_used": False,
            "lean_started": False,
        }
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        print(json.dumps({"error_type": type(exc).__name__, "error": str(exc),
                          "api_client_imported": False if "--advance" not in sys.argv else None,
                          "credentials_read": False if "--advance" not in sys.argv else None,
                          "network_used": False if "--advance" not in sys.argv else None,
                          "lean_started": False}, ensure_ascii=False, sort_keys=True, indent=2))
        sys.exit(2)
