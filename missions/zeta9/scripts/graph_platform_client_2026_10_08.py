"""Current, guarded Prove2Me transport for the new public mission only.

Offline imports never open credentials. Business requests are issued once, with
an exact wire snapshot and a write-ahead record. Unknown outcomes stop the batch.
"""
from __future__ import annotations

import hashlib
import json
import msvcrt
import sys
import urllib.request
import uuid
from datetime import datetime, timezone
from pathlib import Path

import audit_new_mission_2026_10_07 as documents
import publish_mission_2026_10_02 as official

TASK = Path(__file__).resolve().parents[1]
MISSION = "5eb457c6-bc3b-4f51-852a-c5d29fb77c53"
PROPOSAL = "19653cff-d481-498a-a717-10630d1ca1b7"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
OLD = {"8195d8fe-059f-4515-92b4-57b585e2bac6", "06faf23f-00c2-4edf-92ab-1212cdb7d7d6"}
DOCS = TASK / "formalization/platform/readback-2026-10-08/api-docs-v0.12.2"
OUT = TASK / "formalization/platform/graph-integration-2026-10-08"
PINS = dict(documents.PINS, **{"SKILL.md": "7fab478b044493296d78bfcbb40883e1fdfffe4568f9dd23670fac2b7a65bd04"})


def sha(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1048576), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load(path: Path):
    return json.loads(path.read_bytes())


def save(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def check_documents():
    for relative, expected in PINS.items():
        assert sha(DOCS / relative) == expected, relative


def check_source_gate():
    pin = load(OUT / "Root-reviewed-publication-pin.json")
    source_plan = load(OUT / "Root-reviewed-source-plan.json")
    assert pin["all_required_native_and_platform_independent_checks_passed"]
    assert source_plan["all_required_native_and_platform_independent_checks_passed"]
    assert pin["new_mission_id"] == MISSION and pin["env"] == ENV
    assert source_plan["reviewed_labels"] == list(source_plan["sources"])
    assert source_plan["sources"] and set(source_plan["sources"]) <= {"A", "two", "one"}
    for binding in pin["bindings"]:
        relative = Path(binding["task_relative"])
        assert not relative.is_absolute() and ".." not in relative.parts
        target = TASK / relative
        assert target.stat().st_size == binding["bytes"] and sha(target) == binding["sha256"]
    for roles in source_plan["sources"].values():
        for binding in roles.values():
            relative = Path(binding["task_relative"])
            assert not relative.is_absolute() and ".." not in relative.parts
            target = TASK / relative
            assert target.stat().st_size == binding["bytes"] and sha(target) == binding["sha256"]
    return pin


def validate_receipt(path, request_body, value):
    assert isinstance(value, dict)
    def valid_uuid(identifier):
        assert isinstance(identifier, str) and str(uuid.UUID(identifier)) == identifier
    if path == "/submit-definition":
        requested = json.loads(request_body)
        valid_uuid(value.get("job_id"))
        assert value.get("definition_name") == requested["definition_name"]
        assert value.get("status") == "PENDING"
    elif path == "/submit-problem":
        requested = json.loads(request_body)
        assert value.get("errors") == [] and len(value["jobs"]) == len(requested["problems"])
        for job, problem in zip(value["jobs"], requested["problems"]):
            valid_uuid(job.get("job_id"))
            assert job.get("name") == problem["theorem_name"]
    elif path == "/verify":
        valid_uuid(value.get("submission_id"))
        assert value.get("status") in {"PENDING", "ACCEPTED", "SKETCH_ACCEPTED"}
    elif path == f"/missions/{MISSION}/milestones":
        requested = json.loads(request_body)
        valid_uuid(value.get("id"))
        assert value["title"] == requested["title"]
        assert value["milestone_description"] == requested["milestone_description"]
        assert value["theorem"]["id"] == requested["theorem_id"]
    elif path.startswith("/theorems/"):
        valid_uuid(value.get("theorem_id"))
        assert value["theorem_id"] == path.rsplit("/", 1)[1]
        requested = json.loads(request_body)
        for key in requested:
            if key != "reason":
                assert value[key] == requested[key]
    else:
        raise AssertionError("Unreviewed receipt endpoint")


class Client(official.Client):
    def __init__(self):
        check_documents()
        check_source_gate()  # Entire offline source/pin validation before health or credentials.
        compatibility = load(OUT / "Root-reviewed-api-compatibility.json")
        assert compatibility["latest_official_document_pins"] == PINS
        assert compatibility["latest_main_skill_sha256"] == PINS["SKILL.md"]
        assert compatibility["used_endpoint_contracts_personally_reviewed"]
        official.VERSION = compatibility["observed_platform_version"]
        super().__init__()  # Health check precedes credential access; refresh checks version.

    def call(self, method, path, data=None, authenticated=True):
        assert not any(identity in path for identity in OLD)
        assert method == "GET" or (method == "POST" and path == "/agent/refresh" and not authenticated)
        return super().call(method, path, data, authenticated)

    def business(self, operation: str, method: str, path: str, body: bytes, content_type: str):
        assert method in {"POST", "PATCH"}
        assert not any(identity in path for identity in OLD)
        assert path in {"/submit-definition", "/submit-problem", "/verify", f"/missions/{MISSION}/milestones"} or path.startswith("/theorems/")
        assert "/mission-proposals/" not in path
        pin = check_source_gate()
        expected = pin["operations"][operation]
        assert expected == {"method": method, "path": path, "body_sha256": hashlib.sha256(body).hexdigest(), "body_bytes": len(body), "content_type": content_type}
        reconciliation = load(TASK / "verification/graph-integration-root-2026-10-08/phase-registration-recovery/Root-complete-readonly-reconciliation.json")
        assert reconciliation["history_complete_total"] == 236 and reconciliation["exact_current_name_search_total"] == 0
        OUT.mkdir(parents=True, exist_ok=True)
        with (OUT / "writer.lock").open("a+b") as lock:
            lock.seek(0)
            if not lock.read(1):
                lock.write(b"0")
                lock.flush()
            lock.seek(0)
            msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
            try:
                journal_path = OUT / "business-post-journal.json"
                journal = load(journal_path) if journal_path.exists() else {"new_mission_id": MISSION, "attempts": []}
                assert journal["new_mission_id"] == MISSION
                assert all(row.get("receipt_saved") for row in journal["attempts"]), "Resolve the recorded unknown result before any business request"
                for recorded in journal["attempts"]:
                    assert recorded["operation"] in pin["operations"]
                    checked = pin["operations"][recorded["operation"]]
                    assert all(recorded[key] == checked[key] for key in checked)
                    stored_wire = OUT / recorded["wire"]
                    stored_receipt = OUT / recorded["receipt"]
                    assert stored_wire.stat().st_size == checked["body_bytes"] and sha(stored_wire) == checked["body_sha256"]
                    assert sha(stored_receipt) == recorded["receipt_sha256"]
                    validate_receipt(recorded["path"], stored_wire.read_bytes(), load(stored_receipt))
                previous = [row for row in journal["attempts"] if row["operation"] == operation]
                if previous:
                    assert len(previous) == 1 and previous[0]["body_sha256"] == expected["body_sha256"]
                    receipt = OUT / previous[0]["receipt"]
                    assert sha(receipt) == previous[0]["receipt_sha256"]
                    return load(receipt)
                key = uuid.uuid4().hex
                wire = OUT / "wire" / (key + ".body")
                wire.parent.mkdir(parents=True, exist_ok=True)
                wire.write_bytes(body)
                row = dict(expected, operation=operation, intended_at_utc=datetime.now(timezone.utc).isoformat(), receipt_saved=False, wire=wire.relative_to(OUT).as_posix(), receipt="receipts/" + key + ".json")
                journal["attempts"].append(row)
                save(journal_path, journal)
                request = urllib.request.Request(official.BASE + path, data=wire.read_bytes(), headers={"Authorization": "Bearer " + self.token, "Content-Type": content_type}, method=method)
                try:
                    with self.opener.open(request, timeout=45) as response:
                        value = json.load(response)
                    validate_receipt(path, wire.read_bytes(), value)
                except Exception:
                    raise RuntimeError("Business result unknown; inspect documented history before any further write") from None
                receipt = OUT / row["receipt"]
                save(receipt, value)
                row["receipt_saved"] = True
                row["receipt_sha256"] = sha(receipt)
                save(journal_path, journal)
                return value
            finally:
                lock.seek(0)
                msvcrt.locking(lock.fileno(), msvcrt.LK_UNLCK, 1)


def json_wire(value) -> bytes:
    return json.dumps(value, ensure_ascii=False).encode("utf-8")


def multipart_wire(theorem_id: str, source: bytes, explanation: str, boundary: str):
    assert str(uuid.UUID(theorem_id)) == theorem_id
    assert boundary.isascii() and all(character.isalnum() for character in boundary)
    assert ("--" + boundary).encode() not in source
    parts = []
    for name, value in [("theorem_id", theorem_id), ("proof_type", "prove"), ("explanation", explanation)]:
        assert "\r" not in name and "\n" not in name
        parts.append((f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n').encode() + value.encode("utf-8") + b"\r\n")
    parts.append((f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode() + source + b"\r\n")
    body = b"".join(parts) + (f"--{boundary}--\r\n").encode()
    assert source in body
    return body, "multipart/form-data; boundary=" + boundary


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    check_documents()
    print("Offline transport syntax and official document bindings checked; no credentials or API calls")
