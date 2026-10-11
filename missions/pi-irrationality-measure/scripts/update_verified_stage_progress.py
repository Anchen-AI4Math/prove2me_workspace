"""Summarize only exact successful public Definition readbacks for this task."""
import hashlib
import json
import argparse
from datetime import datetime, timezone
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
V = TASK / "verification"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--preflight-session-id", type=int)
parser.add_argument("--publisher-session-id", type=int)
parser.add_argument("--queue-note")
parser.add_argument("--root-status-record")
args = parser.parse_args()
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
roots = [V / "definition-validation", V / "providers-preview/all-shared-safe-leaves/validation",
         V / "providers-complete-preview/all-shared-safe-leaves/validation",
         V / "providers-context-preview/namespace-context/validation",
         V / "providers-formal-log-preview/formal-log/validation",
         V / "ap2/publication", V / "ap3/publication", V / "ap7/publication",
         V / "ap7/collision-constant"]
published = {}
pending = []
for root in roots:
    for path in sorted(root.glob("*/publication.json")):
        record = json.loads(path.read_bytes())
        readback = record.get("target_readback", {})
        body = readback.get("body", {})
        payload = (record.get("publish_intent") or {}).get("payload")
        identifier = record.get("definition_id")
        if identifier and readback.get("http_status") == 200 and payload:
            assert (body.get("theorem_id") == identifier
                    and body.get("theorem_name") == record["definition_name"]
                    and body.get("status") == "Definition"
                    and body.get("mathlib_rev") == ENV
                    and body.get("visibility") == "public"
                    and body.get("definition") == payload["definition"])
            published[identifier] = {
                "definition_id": identifier, "definition_name": record["definition_name"],
                "job_id": record.get("job_id"), "status": "PUBLISHED_EXACT_READBACK",
                "source_bytes": len(payload["definition"].encode("utf-8")),
                "source_sha256": hashlib.sha256(payload["definition"].encode("utf-8")).hexdigest(),
                "publication_record": path.relative_to(TASK).as_posix(),
                "publication_record_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            }
        elif record.get("job_id"):
            pending.append({"definition_name": record["definition_name"], "job_id": record["job_id"],
                            "publication_record": path.relative_to(TASK).as_posix()})
report = {"updated_at_utc": datetime.now(timezone.utc).isoformat(),
          "definition_count": len(published), "definitions": list(published.values()),
          "pending_known_jobs": pending, "source_main_and_campaign_bridge_locally_verified": True,
          "final_platform_dependency_closure_complete": False, "proposal_status": "Draft"}
proofs = []
matrix_path = TASK / "platform/current-det-row-sum.json"
matrix_submission = TASK / "platform/det-row-sum-submission.json"
matrix, submission = json.loads(matrix_path.read_bytes()), json.loads(matrix_submission.read_bytes())
verdict = submission["last_verdict"]
assert (matrix["status"] == "Proved" and verdict["status"] == "ACCEPTED"
        and matrix["theorem_id"] == submission["theorem_id"] == verdict["theorem_id"])
proofs.append({"theorem_id": matrix["theorem_id"], "theorem_name": matrix["theorem_name"],
               "submission_id": verdict["id"], "status": "ACCEPTED_AND_PROVED",
               "verification_record": matrix_submission.relative_to(TASK).as_posix(),
               "verification_record_sha256": hashlib.sha256(matrix_submission.read_bytes()).hexdigest()})
proof_paths = []
for root in [V / "independent", V / "nodes-preview"]:
    proof_paths.extend(root.glob("*/publication.json"))
proof_paths.extend((V / "flp3").glob("*/publication/publication.json"))
proof_paths.extend((V / "provider-nodes-preview").glob("*/dimension-margin-publication*/publication.json"))
proof_paths.extend((V / "ap4").glob("*/publication/publication.json"))
proof_paths.extend((V / "ap4").glob("*/publication-draft/publication.json"))
proof_paths.extend((V / "ap4").glob("*/publication-wire-*/publication.json"))
proof_paths.extend((V / "ap5").glob("*/publication*/publication.json"))
proof_paths.extend((V / "ap6/a1").glob("*/publication*/publication.json"))
proof_paths.extend((V / "ap7").glob("*/publication*/publication.json"))
for path in sorted(proof_paths):
        record = json.loads(path.read_bytes())
        if record.get("confirmed_proved") is not True:
            continue
        verify = record.get("last_verify_verdict", {})
        body = verify.get("body", verify)  # Historical independent uploader stored the API body directly.
        target = record.get("target_readback", {}).get("body", {})
        if record.get("existing_proved_reused") and body.get("status") != "ACCEPTED":
            continue
        assert (body.get("status") == "ACCEPTED" and target.get("status") == "Proved"
                and body.get("theorem_id") == target.get("theorem_id") == record["theorem_id"]
                and body.get("id") == record["submission_id"])
        proofs.append({"theorem_id": record["theorem_id"], "theorem_name": record["theorem_name"],
                       "submission_id": record["submission_id"], "status": "ACCEPTED_AND_PROVED",
                       "verification_record": path.relative_to(TASK).as_posix(),
                       "verification_record_sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
report.update(proof_count=len(proofs), proofs=proofs)
(V / "verified-stage-progress.json").write_bytes((json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode())
state_path = V / "run-state.json"
state = json.loads(state_path.read_bytes())
state["preflight_session_id"] = args.preflight_session_id
state["publisher_session_id"] = args.publisher_session_id
state["published_definition_count"] = len(published)
state["accepted_proof_count"] = len(proofs)
state["note"] = (f"{len(published)} Definitions PUBLISHED with exact public readback; "
                 f"{len(proofs)} theorem proofs Accepted/Proved. Source Main and platform bridge verified locally; "
                 "final platform dependency closure remains incomplete, proposal Draft, goal active.")
if args.queue_note:
    state["current_queue_note"] = args.queue_note
if args.root_status_record:
    status_path = (TASK / args.root_status_record).resolve()
    assert status_path.is_relative_to(V.resolve()) and status_path.is_file()
    status_record = json.loads(status_path.read_bytes())
    expected_targets = {"e717eef2-11b1-4b14-9789-65f52c0502e1", "406736ed-98ce-4177-b97f-24de96ba4188"}
    assert status_record["read_only"] is True and len(status_record["records"]) == 2
    assert {r["body"]["theorem_id"] for r in status_record["records"]} == expected_targets
    assert all(r["http_status"] == 200 for r in status_record["records"])
    state["latest_live_root_status"] = status_path.relative_to(TASK).as_posix()
    state["latest_live_root_status_sha256"] = hashlib.sha256(status_path.read_bytes()).hexdigest()
state["verified_stage_progress"] = "verification/verified-stage-progress.json"
state_path.write_bytes((json.dumps(state, ensure_ascii=False, indent=2) + "\n").encode())
print(json.dumps({"definition_count": len(published), "proof_count": len(proofs),
                  "pending_known_jobs": pending}))
