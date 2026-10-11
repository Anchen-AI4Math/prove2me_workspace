"""GET-only f4 receipt polling; reuse sealed typed evidence without replaying it."""
import argparse
import importlib.util
import json
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import quote
import publish_formal_log_final_node as p

PUBLISHER_SHA = "dc962dccf0e8b0aad8704f53ceb067ef26b7e1419ab8000b5756ba10fe954318"


def guard(stage, directory, pins, record):
    manifest = p.read(stage / "manifest.json")
    certificate = p.read(p.TASK / pins["certificate_file"])
    # Reconstruct only the frozen typed inventory, including ordered-first OLean
    # resolution. The complete proof checker is never invoked by this helper.
    inventory = p.securitypins.reviewed_security_pins({
        "validated": certificate.get("validated"), "stage": stage,
        "manifest_data": manifest,
        "certificate": {"path": pins["certificate_file"], "sha256": pins["certificate_sha256"], "data": certificate},
    })
    if inventory != pins["security_pins"]:
        raise ValueError("Sealed typed inventory or ordered-first OLean resolution changed")
    fixed = {
        directory / "preparation.json": p.sha_bytes(p.encode(pins)),
        stage / "manifest.json": pins["manifest_sha256"],
        p.TASK / pins["certificate_file"]: pins["certificate_sha256"],
        p.confined_file(pins["metadata_file"], base=p.TASK): pins["metadata_sha256"],
        Path(p.__file__): PUBLISHER_SHA,
        Path(p.checker.__file__): p.FINAL_CHECKER_SHA256,
        Path(p.securitypins.__file__): p.SECURITY_HELPER_SHA256,
        Path(p.retained_successor.__file__): p.RETAINED_SUCCESSOR_SHA256,
        p.ROOT / "scripts/p2m_api.py": pins["api_client_sha256"],
    }
    fixed.update({directory / name: digest for name, digest in pins["payload_sha256"].items()})
    for path, digest in fixed.items():
        if path.is_symlink() or p.sha(path) != digest:
            raise ValueError("Sealed typed input changed: " + str(path))
    if directory.is_symlink() or (directory / "publication.json").is_symlink():
        raise ValueError("Publication state cannot use symlinks")
    if (record.get("preparation") != pins or record.get("target_binding") != p.target_binding(manifest, pins)
            or record.get("environment") != p.ENV or record.get("theorem_name") != manifest["theorem_name"]
            or record.get("artifact_kind") != "formal-log-proof-node-publication-record"
            or record.get("proposal_status") != "Draft"):
        raise ValueError("Known publication is not bound to sealed f4 inputs")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--poll", action="store_true")
    parser.add_argument("--theorem-id")
    parser.add_argument("--submission-id")
    args = parser.parse_args()
    stage = p.DEFAULT_STAGE
    directory = stage / "publication"
    state_path = directory / "publication.json"
    state_before = state_path.read_bytes()
    record = json.loads(state_before)
    pins = p.read(directory / "preparation.json")
    manifest = guard(stage, directory, pins, record)
    if not args.poll:
        print(json.dumps({"typed_guard_passed": True, "network_used": False, "pins": len(pins["security_pins"])}))
        return
    tid, sid = args.theorem_id, args.submission_id
    if not tid or not sid or record.get("theorem_id") != tid or record.get("submission_id") != sid:
        raise ValueError("Explicit known theorem and own submission IDs must match durable state")
    spec = importlib.util.spec_from_file_location("f4_known_receipt_api", p.ROOT / "scripts/p2m_api.py")
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = api.get_token()
    status, raw = api._request("GET", "/verify?submission_id=" + quote(sid, safe=""), token=token)
    verdict = json.loads(raw)
    if status != 200 or verdict.get("theorem_id") != tid or (verdict.get("submission_id") or verdict.get("id")) != sid:
        raise ValueError("Own-submission GET receipt identity mismatch")
    target_status, raw = api._request("GET", "/theorems/" + quote(tid, safe=""), token=token)
    target = json.loads(raw)
    if (target_status != 200 or target.get("theorem_id") != tid or target.get("theorem_name") != manifest["theorem_name"]
            or target.get("mathlib_rev") != p.ENV or target.get("visibility") != "public"
            or target.get("deprecated_at") is not None or target.get("formal_statement") != manifest["formal_statement"]
            or target.get("preamble") != manifest["preamble"]):
        raise ValueError("Exact public theorem GET readback mismatch")
    guard(stage, directory, pins, record)
    if state_path.read_bytes() != state_before:
        raise ValueError("Concurrent publication state change; receipts were not saved")
    record["last_verify_verdict"] = {"http_status": status, "body": verdict}
    record["target_readback"] = {"http_status": target_status, "body": target}
    record["accepted"] = verdict.get("status") == "ACCEPTED"
    record["confirmed_proved"] = target.get("status") == "Proved"
    record["existing_proved_reused"] = False
    record["known_receipt_poll"] = {"helper_sha256": p.sha(Path(__file__)), "GET_only": True,
        "typed_inputs_stable": True, "checked_at_utc": datetime.now(timezone.utc).isoformat()}
    record["updated_at_utc"] = record["known_receipt_poll"]["checked_at_utc"]
    state_path.write_bytes(p.encode(record))
    print(json.dumps({key: record.get(key) for key in ["theorem_id", "submission_id", "accepted", "confirmed_proved"]}))


if __name__ == "__main__":
    main()
