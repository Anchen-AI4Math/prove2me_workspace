"""GET-only fast polling for the two already-submitted FormalLog successors.

Default mode checks the saved, previously certified evidence offline.  The
explicit --advance mode performs only GETs for the two hard-coded submission
and theorem IDs; it never submits or retries a proof.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import time
from urllib.parse import quote

sys.dont_write_bytecode = True

import publish_formal_log_successor_node as publisher
import formal_log_successor_security_pins as securitypins

TASK, ROOT = publisher.TASK, publisher.ROOT
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
PUBLISHER_SHA = "b084ca262fbbfdceb687c8b41afd42ba32aedcd10d7e0f8e78c557cadf99dc89"
HELPER_SHA = "198dc1620322fd0ec87db635f4dd761f0aedc8f77b3947ceb8b107679b32ff57"
API_SHA = "8c7c90d59692d914ed0bf62d05d88204a970d0eb827cde37b862c64e299e00ed"
BASE_CHECKER_SHA = "20f761f0d169c7af296faea379bb7547909abd56f79d0bdba03a207d7617bfb4"
F3_CHECKER_SHA = "e59db91b0c19026106294683e737c4f1060439d9aaccb9addd5502aa9e158a7a"
FROZEN_PUBLISHER_SHA = "dee52d38432a461d5520e7df2103640b72ea1ffe6bf2288a75891b7a45217913"
KNOWN = {
    "f2": {
        "theorem_id": "bc74060f-2602-42a2-ab0a-7435517bae27",
        "submission_id": "4f54c75a-6ac6-409a-8da5-3f016779cd13",
        "theorem_name": "OAI.PiExponent.FormalLogTruncation.logTail_mem_rationalWeightedIdeal",
        "metadata": "platform/formal-log-node-metadata/logTail_mem_rationalWeightedIdeal.json",
        "certificate": "verification/flp3/f2/successor-node-validation.json",
        "pin_count": 688,
    },
    "f3": {
        "theorem_id": "9e8a05d9-eb6a-4e92-92d2-640defa3421c",
        "submission_id": "d1bf8788-830c-4f74-92c6-3dbbf427fa1b",
        "theorem_name": "OAI.PiExponent.FormalLogTruncation.shiftMap_truncatedFormalJet",
        "metadata": "platform/formal-log-node-metadata/shiftMap_truncatedFormalJet.json",
        "certificate": "verification/flp3/f3/complete-node-validation.json",
        "pin_count": 717,
    },
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load(path: Path):
    return json.loads(path.read_bytes().decode("utf-8"))


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def review(stage_name: str):
    require(stage_name in KNOWN, "Only known stages f2/f3 are allowed")
    k = KNOWN[stage_name]
    stage = (TASK / "verification/flp3" / stage_name).resolve()
    pubdir = stage / "publication"
    record_path, prep_path = pubdir / "publication.json", pubdir / "preparation.json"
    for p in (stage, pubdir, record_path, prep_path):
        require(not p.is_symlink() and p.exists(), "Missing or symlinked fixed publication input: " + str(p))
    record_raw, prep_raw = record_path.read_bytes(), prep_path.read_bytes()
    record, pins = load(record_path), load(prep_path)
    require(prep_raw == publisher.encode(pins), "Preparation is not its canonical frozen JSON")
    require(record.get("preparation") == pins, "Publication record embeds a different preparation")
    require(record.get("schema_version") == 1 and record.get("artifact_kind") == "formal-log-proof-node-publication-record",
            "Unexpected publication record schema or artifact kind")
    require(pins.get("stage") == "verification/flp3/" + stage_name and pins.get("environment") == ENV,
            "Preparation stage/environment differs")
    require(pins.get("definition_name") == k["theorem_name"],
            "Preparation definition name differs from the fixed theorem")
    require(pins.get("proposal_status") == "Draft" and pins.get("submission_ready") is False,
            "Preparation is not the expected Draft/non-submission-ready artifact")
    require(record.get("environment") == ENV and record.get("proposal_status") == "Draft",
            "Record environment or proposal state differs")
    require(record.get("theorem_id") == k["theorem_id"] and record.get("submission_id") == k["submission_id"],
            "Record does not contain the exact known theorem and own submission IDs")
    require(record.get("theorem_name") == k["theorem_name"], "Record theorem name differs")

    paths = {
        "publisher": TASK / "scripts/publish_formal_log_successor_node.py",
        "helper": TASK / "scripts/formal_log_successor_security_pins.py",
        "api": ROOT / "scripts/p2m_api.py",
        "base_checker": TASK / "scripts/validate_formal_log_successor_node.py",
        "frozen_publisher": TASK / "scripts/publish_formal_log_proof_node.py",
        "metadata": TASK / k["metadata"],
        "certificate": TASK / k["certificate"],
        "manifest": stage / "manifest.json",
        "publish_payload": pubdir / "publish-payload.json",
        "verify_payload": pubdir / "verification-payload.json",
    }
    expected = {
        "publisher": PUBLISHER_SHA, "helper": HELPER_SHA, "api": API_SHA,
        "base_checker": BASE_CHECKER_SHA, "frozen_publisher": FROZEN_PUBLISHER_SHA,
        "metadata": pins["metadata_sha256"], "certificate": pins["certificate_sha256"],
        "manifest": pins["manifest_sha256"],
        "publish_payload": pins["payload_sha256"]["publish-payload.json"],
        "verify_payload": pins["payload_sha256"]["verification-payload.json"],
    }
    if stage_name == "f3":
        paths["f3_checker"] = TASK / "scripts/validate_formal_log_f3_complete_node_repaired.py"
        expected["f3_checker"] = F3_CHECKER_SHA
    for key, path in paths.items():
        require(not path.is_symlink() and path.is_file(), "Missing or symlinked bound file: " + str(path))
        require(digest(path.read_bytes()) == expected[key], "Bound file hash differs: " + key)
    require(pins.get("publisher_sha256") == PUBLISHER_SHA and pins.get("security_helper_sha256") == HELPER_SHA
            and pins.get("api_client_sha256") == API_SHA and pins.get("checker_sha256") == BASE_CHECKER_SHA
            and pins.get("frozen_publisher_sha256") == FROZEN_PUBLISHER_SHA,
            "Preparation implementation pins differ")
    require(pins.get("certificate_file") == k["certificate"], "Certificate path differs from known stage")
    if stage_name == "f3":
        require(pins.get("complete_checker_sha256") == F3_CHECKER_SHA, "f3 checker pin differs")
    manifest = load(paths["manifest"])
    require(manifest.get("theorem_name") == k["theorem_name"], "Manifest theorem differs")
    binding = publisher.target_binding(manifest, pins)
    require(record.get("target_binding") == binding, "Saved target binding does not replay from current manifest/pins")
    require(record.get("publication_intent", {}).get("endpoint") == "/submit-problem"
            and record["publication_intent"].get("environment") == ENV
            and record["publication_intent"].get("theorem_name") == k["theorem_name"]
            and record["publication_intent"].get("payload_sha256") == expected["publish_payload"],
            "Publication intent is not bound to the exact public Draft payload")
    desc = load(paths["verify_payload"])
    verify_intent = record.get("verification_intent", {})
    require(verify_intent.get("endpoint") == "/verify" and verify_intent.get("theorem_id") == k["theorem_id"]
            and verify_intent.get("descriptor_sha256") == expected["verify_payload"]
            and verify_intent.get("solution_sha256") == desc.get("file", {}).get("sha256"),
            "Verification intent does not bind the exact known target and solution")
    require(desc.get("target_theorem_name") == k["theorem_name"] and desc.get("env") == ENV
            and desc.get("theorem_id") is None
            and desc.get("theorem_id_binding") == "exact public theorem name/environment/preamble/formal_statement readback"
            and desc.get("proof_type") == "prove",
            "Prepared verification descriptor has a different theorem, environment, or type")
    for name in ("verification_response", "last_verify_verdict"):
        response = record.get(name, {})
        body = response.get("body", {})
        require(response.get("http_status") in (200, 202)
                and (body.get("submission_id") or body.get("id")) == k["submission_id"]
                and body.get("status") in ("PENDING", "COMPILING", "ACCEPTED"),
                "Saved " + name + " is not a known own-submission response")
    require(len(pins.get("security_pins", [])) == k["pin_count"], "Frozen security pin count differs")
    securitypins.assert_security_pins(pins["security_pins"])
    return stage, pubdir, record_path, record_raw, record, pins, manifest, desc


def validate_mock_binding(stage, theorem_id, submission_id):
    known = KNOWN[stage]
    require(theorem_id == known["theorem_id"] and submission_id == known["submission_id"],
            "Mock/response identity does not match the fixed known IDs")


def atomic_write(path: Path, data: bytes):
    fd, name = tempfile.mkstemp(prefix="." + path.name + ".", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as out:
            out.write(data); out.flush(); os.fsync(out.fileno())
        os.replace(name, path)
    finally:
        if os.path.exists(name): os.unlink(name)


def safe_child_directory(parent: Path, name: str) -> Path:
    child = parent / name
    require(not child.is_symlink(), "Refusing symlinked publication subdirectory: " + str(child))
    child.mkdir(exist_ok=True)
    resolved_parent, resolved_child = parent.resolve(), child.resolve()
    require(resolved_child != resolved_parent and resolved_child.is_relative_to(resolved_parent),
            "Publication subdirectory escapes its fixed parent")
    return resolved_child


def advance(stage_name: str):
    reviewed = review(stage_name)
    stage, pubdir, record_path, original, record, pins, manifest, _ = reviewed
    k = KNOWN[stage_name]
    # Import the frozen API client only here, and deliberately use its GET
    # transport directly so an expired token cannot trigger its refresh POST.
    api_path = ROOT / "scripts/p2m_api.py"
    spec = importlib.util.spec_from_file_location("formal_log_poll_api", api_path)
    api = importlib.util.module_from_spec(spec); spec.loader.exec_module(api)
    require(api.BASE == "https://prove2.me/api/v1", "API base URL is not the pinned production endpoint")
    creds = api._load()
    require(creds.get("access_token") and creds.get("expires_at", 0) > int(time.time()) + 120,
            "A currently valid access token is required; poller will not refresh credentials")
    token = creds["access_token"]
    def get(path):
        status, raw = api._request("GET", path, token=token)
        try: body = json.loads(raw)
        except Exception: body = {"raw": raw}
        return status, body

    # Recheck the complete cheap local inventory immediately before and after
    # the network reads. No Lean process, checker replay, or POST is involved.
    require(review(stage_name)[3] == original, "Publication record changed before polling")
    status, body = get("/verify?submission_id=" + quote(k["submission_id"], safe=""))
    require(status in (200, 202) and (body.get("submission_id") or body.get("id")) == k["submission_id"]
            and body.get("theorem_id") == k["theorem_id"], "Fresh verify response is not for the exact own submission")
    verify_result = {"http_status": status, "body": body}
    if body.get("status") != "ACCEPTED":
        require(review(stage_name)[3] == original and record_path.read_bytes() == original,
                "Certified inputs or publication record changed before saving pending poll receipt")
        receipt = {"schema_version": 1, "artifact_kind": "formal-log-successor-poll-receipt",
                   "stage": "verification/flp3/" + stage_name, "theorem_id": k["theorem_id"],
                   "submission_id": k["submission_id"], "verify": verify_result,
                   "accepted": False, "checked_at_utc": datetime.now(timezone.utc).isoformat()}
        receipt_dir = safe_child_directory(pubdir, "poll-receipts")
        receipt_path = receipt_dir / (datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ") + ".json")
        require(not receipt_path.exists(), "Poll receipt path collision")
        atomic_write(receipt_path, publisher.encode(receipt))
        return {"stage": stage_name, "status": body.get("status"), "accepted": False, "receipt": str(receipt_path)}

    require(status == 200, "A fresh Accepted verification receipt must use HTTP 200")
    status2, target = get("/theorems/" + quote(k["theorem_id"], safe=""))
    require(status2 == 200 and target.get("theorem_id") == k["theorem_id"]
            and target.get("theorem_name") == k["theorem_name"] and target.get("status") == "Proved"
            and target.get("mathlib_rev") == ENV and target.get("visibility") == "public"
            and target.get("deprecated_at") is None and target.get("formal_statement") == manifest.get("formal_statement")
            and target.get("preamble") == manifest.get("preamble"),
            "Fresh target readback is not the exact public Proved theorem")
    require(review(stage_name)[3] == original and record_path.read_bytes() == original,
            "Local publication record or certified inputs changed during polling")

    history = safe_child_directory(pubdir, "poll-history")
    archive = history / ("publication-" + digest(original) + ".json")
    if archive.exists():
        require(archive.read_bytes() == original, "Existing archive has different bytes")
    else:
        atomic_write(archive, original)
    updated = dict(record)
    updated["accepted"] = True
    updated["confirmed_proved"] = True
    updated["existing_proved_reused"] = False
    updated["last_verify_verdict"] = verify_result
    updated["target_readback"] = {"http_status": status2, "body": target}
    updated["poll_acceptance"] = {"theorem_id": k["theorem_id"], "submission_id": k["submission_id"],
                                  "verify": verify_result, "target_readback": {"http_status": status2, "body": target},
                                  "prior_publication_sha256": digest(original),
                                  "prior_publication_archive": archive.relative_to(TASK).as_posix(),
                                  "checked_at_utc": datetime.now(timezone.utc).isoformat()}
    require(not record_path.is_symlink() and record_path.read_bytes() == original,
            "Publication record changed or became symlinked before atomic update")
    atomic_write(record_path, publisher.encode(updated))
    return {"stage": stage_name, "status": "ACCEPTED", "accepted": True,
            "theorem_id": k["theorem_id"], "submission_id": k["submission_id"],
            "archive": str(archive)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=KNOWN, required=True)
    parser.add_argument("--check-only", action="store_true", help="offline-only review (the default)")
    parser.add_argument("--advance", action="store_true", help="perform only exact known-ID GET requests")
    parser.add_argument("--self-test", action="store_true", help="test fixed-ID rejection without filesystem/API access")
    args = parser.parse_args()
    if args.self_test:
        validate_mock_binding(args.stage, KNOWN[args.stage]["theorem_id"], KNOWN[args.stage]["submission_id"])
        for bad_t, bad_s in (("wrong-theorem", KNOWN[args.stage]["submission_id"]),
                             (KNOWN[args.stage]["theorem_id"], "wrong-submission")):
            try: validate_mock_binding(args.stage, bad_t, bad_s)
            except ValueError: pass
            else: raise AssertionError("Bad mocked identity was accepted")
        print("mock identity checks passed; no files, credentials, API, or Lean accessed")
        return 0
    if args.advance:
        result = advance(args.stage)
    else:
        stage, _, record_path, raw, record, pins, _, _ = review(args.stage)
        result = {"stage": args.stage, "offline_review": True,
                  "saved_status": record["last_verify_verdict"]["body"]["status"],
                  "known_submission_id": KNOWN[args.stage]["submission_id"],
                  "security_pin_count": len(pins["security_pins"]),
                  "publication_sha256": digest(raw), "path": str(stage)}
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
