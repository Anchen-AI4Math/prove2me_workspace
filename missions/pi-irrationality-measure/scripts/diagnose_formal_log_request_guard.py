"""Offline-only preview and dry run for the frozen f1 request-guard repair.

This script never imports the publisher or its API client, reads credentials,
opens a network connection, runs Lean, or writes files. It creates the proposed
publisher source in memory by removing only the obsolete security_file_hashes
loop; then it syntax-checks and statically inspects that candidate and replays
the currently prepared non-API request guards read-only.
"""
from __future__ import annotations

import ast
import difflib
import hashlib
import json
from pathlib import Path
import re
import sys

import formal_log_node_security_pins as securitypins


TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parent.parent
STAGE = TASK / "verification/flp3/f1"
PUBLICATION = STAGE / "publication"
PUBLISHER = TASK / "scripts/publish_formal_log_proof_node.py"
CHECKER = TASK / "scripts/validate_formal_log_node.py"
METADATA = TASK / "platform/formal-log-node-metadata/liftSeries_eq_toMvPowerSeries.json"
MANIFEST = STAGE / "manifest.json"
CERTIFICATE = STAGE / "formal-node-validation.json"
EXPECTED_PUBLISHER_SHA256 = "bfe1d7333ba1b263577a7ade8ac777651877f1471ac173d56aa821eee20b95e2"
EXPECTED_HELPER_SHA256 = "8adf3e87f2dc8f7b219cfd55364e3cca391307ffacd46fc6e8d3b12773da7a4f"
EXPECTED_PAYLOADS = {
    "publish-payload.json": "6b15abe647f35f1dec5e59511e225a328ca60e6eb8e2424088e037def13e54b0",
    "verification-payload.json": "e1412316174177d594342ecb143373cfc616935db2bc03a12ab16ef83da4e205",
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_digest(path: Path) -> str:
    return digest(path.read_bytes())


def json_file(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def candidate_bytes(original: bytes) -> bytes:
    start_marker = b'        for file_value, expected in pins["security_file_hashes"].items():'
    end_marker = b'        for filename, expected in pins["payload_sha256"].items():'
    if original.count(start_marker) != 1 or original.count(end_marker) != 1:
        raise ValueError("Expected exactly one obsolete security_file_hashes loop and one following payload loop")
    start = original.index(start_marker)
    end = original.index(end_marker, start)
    if end <= start:
        raise ValueError("Obsolete guard loop boundaries are reversed")
    # Keep the next guard at its original indentation and preserve all other bytes.
    return original[:start] + original[end:]


def verify_candidate_static(candidate: bytes) -> None:
    source = candidate.decode("utf-8")
    ast.parse(source, filename="publish_formal_log_proof_node.py (repair candidate)")
    if "security_file_hashes" in source:
        raise ValueError("Repair candidate still references the removed security_file_hashes field")
    module = ast.parse(source)
    advance = next((node for node in module.body if isinstance(node, ast.FunctionDef) and node.name == "advance"), None)
    if advance is None:
        raise ValueError("Repair candidate has no advance function")
    guard = next((node for node in advance.body if isinstance(node, ast.FunctionDef) and node.name == "guard"), None)
    if guard is None:
        raise ValueError("Repair candidate has no nested request guard")
    guard_source = ast.get_source_segment(source, guard) or ""
    required = (
        'securitypins.assert_security_pins(pins["security_pins"])',
        'pins["payload_sha256"]',
        'pins["metadata_sha256"]',
        'pins["certificate_sha256"]',
        'pins["manifest_sha256"]',
    )
    if any(item not in guard_source for item in required):
        raise ValueError("Repair candidate is missing a required current request-guard check")


def dry_run_existing_pins() -> dict:
    prep_path = PUBLICATION / "preparation.json"
    record_path = PUBLICATION / "publication.json"
    prep = json_file(prep_path)
    record = json_file(record_path)
    if prep.get("publisher_sha256") != EXPECTED_PUBLISHER_SHA256:
        raise ValueError("Saved offline preparation is not bound to the expected frozen publisher")
    if prep.get("security_helper_sha256") != EXPECTED_HELPER_SHA256:
        raise ValueError("Saved offline preparation is not bound to the expected security helper")
    if file_digest(PUBLISHER) != EXPECTED_PUBLISHER_SHA256:
        raise ValueError("Publisher source differs from the frozen pre-repair source")
    if file_digest(securitypins.__file__ and Path(securitypins.__file__)) != EXPECTED_HELPER_SHA256:
        raise ValueError("Security helper differs from the frozen source")
    if record.get("preparation") != prep:
        raise ValueError("Current publication record does not carry the exact saved preparation")
    forbidden_activity = (
        "publication_intent", "verification_intent", "publication_response",
        "verification_response", "job_id", "theorem_id", "submission_id", "status",
    )
    activity = {key: record.get(key) for key in forbidden_activity if record.get(key) not in (None, False, "")}
    if activity:
        raise ValueError("Publication record has nonempty API activity fields; refusing dry run")

    # This validates the exact typed 611-file security inventory without replaying Lean.
    securitypins.assert_security_pins(prep["security_pins"])
    checks = {
        "manifest_sha256": file_digest(MANIFEST) == prep["manifest_sha256"],
        "certificate_sha256": file_digest(CERTIFICATE) == prep["certificate_sha256"],
        "checker_sha256": file_digest(CHECKER) == prep["checker_sha256"],
        "metadata_sha256": file_digest(METADATA) == prep["metadata_sha256"],
    }
    payloads = prep["payload_sha256"]
    for filename, expected in EXPECTED_PAYLOADS.items():
        actual = file_digest(PUBLICATION / filename)
        checks[filename] = actual == expected == payloads.get(filename)
    if not all(checks.values()):
        raise ValueError("One or more offline preparation guards failed: " + repr(checks))
    return {
        "saved_preparation_sha256": file_digest(prep_path),
        "publication_record_sha256": file_digest(record_path),
        "typed_security_pin_count": len(prep["security_pins"]),
        "read_only_guard_checks": checks,
        "payload_hashes_unchanged": True,
        "api_activity_fields_empty": True,
        "publication_record_preparation_matches": True,
        "api_client_imported_or_read": False,
        "credentials_read": False,
        "network_used": False,
        "lean_started": False,
    }


def main() -> int:
    original = PUBLISHER.read_bytes()
    if digest(original) != EXPECTED_PUBLISHER_SHA256:
        raise ValueError("Frozen publisher preimage SHA does not match")
    candidate = candidate_bytes(original)
    verify_candidate_static(candidate)
    diff = "".join(difflib.unified_diff(
        original.decode("utf-8").splitlines(keepends=True),
        candidate.decode("utf-8").splitlines(keepends=True),
        fromfile="frozen publisher (read only)",
        tofile="proposed candidate (in memory only)",
    ))
    report = {
        "schema_version": 1,
        "artifact_kind": "formal-log-f1-offline-request-guard-repair-preview",
        "publisher_preimage_sha256": digest(original),
        "publisher_candidate_sha256": digest(candidate),
        "removed_block": "the obsolete pins['security_file_hashes'] iteration only",
        "candidate_ast_valid": True,
        "candidate_keeps_typed_security_pin_guard": True,
        "diff": diff,
        "dry_run": dry_run_existing_pins(),
    }
    print(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        print(json.dumps({"error_type": type(exc).__name__, "error": str(exc), "network_used": False,
                          "api_client_imported_or_read": False, "credentials_read": False}, indent=2))
        sys.exit(2)
