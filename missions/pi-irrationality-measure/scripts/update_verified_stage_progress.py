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
         V / "ap7/collision-constant", V / "ap9/simplex", V / "ap9/domains",
         V / "ap10/interpolation", V / "ap10/arithmetic", V / "ap10/determinant",
         V / "ap14/row-data", V / "ap15/scales-costs", V / "ap18/multiplicity",
         V / "ap19/analytic-remainder-data", V / "ap20/literal-interface-data"]
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
proof_paths.extend((V / "ap8").glob("*/publication*/publication.json"))
proof_paths.extend((V / "ap11").glob("*/publication*/publication.json"))
proof_paths.extend((V / "ap12").glob("*/publication*/publication.json"))
proof_paths.extend((V / "ap13").glob("*/publication*/publication.json"))
proof_paths.extend((V / "ap14/entry-gaussian").glob("publication*/publication.json"))
proof_paths.extend((V / "ap15/selected-minor-clearing-bound").glob("publication*/publication.json"))
proof_paths.extend((V / "ap16/selected-minor-arithmetic-lower-bound").glob("publication*/publication.json"))
proof_paths.extend((V / "ap17/actual-minor-arithmetic-lower-bound").glob("publication*/publication.json"))
for path in sorted(proof_paths):
        record = json.loads(path.read_bytes())
        if record.get("confirmed_proved") is not True:
            verification = record.get("last_verify_verdict", record.get("verify_response", {}))
            verification_body = verification.get("body", verification)
            if (record.get("submission_id") and verification.get("http_status") == 200
                    and verification_body.get("status") in {"PENDING", "COMPILING"}):
                pending.append({"kind": "proof-verification",
                                "theorem_name": record["theorem_name"],
                                "theorem_id": record["theorem_id"],
                                "submission_id": record["submission_id"],
                                "status_at_last_readback": verification_body["status"],
                                "publication_record": path.relative_to(TASK).as_posix()})
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
# The existing-target AP17 uploader has a distinct durable record schema.
# Count it only after its exact ACCEPTED submission and hashed Proved readback.
for path in sorted((V / "ap17/actual-minor-arithmetic-lower-bound").glob("verification-publication*/publication.json")):
    record = json.loads(path.read_bytes())
    theorem_id = record["target_theorem_id"]
    theorem_name = record["target_theorem_name"]
    assert theorem_id == "15c55202-44da-420f-bf88-f910c0e7060c"
    assert theorem_name == "OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_bound_source017"
    verdict = record.get("last_verify_verdict", record.get("verify_response", {}))
    body = verdict.get("body", {})
    if record.get("confirmed_ACCEPTED_and_Proved") is not True:
        if (record.get("submission_id") and verdict.get("http_status") in {200, 202}
                and body.get("status") in {"PENDING", "COMPILING"}):
            pending.append({"kind": "proof-verification", "theorem_name": theorem_name,
                            "theorem_id": theorem_id, "submission_id": record["submission_id"],
                            "status_at_last_readback": body["status"],
                            "publication_record": path.relative_to(TASK).as_posix()})
        continue
    readback = record["post_accepted_target"]
    target_path = (TASK / readback["path"]).resolve()
    assert target_path.is_relative_to(V.resolve())
    assert hashlib.sha256(target_path.read_bytes()).hexdigest() == readback["sha256"]
    target = json.loads(target_path.read_bytes())
    assert (verdict["http_status"] in {200, 202} and body.get("status") == "ACCEPTED"
            and body.get("theorem_id") == target.get("theorem_id") == theorem_id
            and body.get("id", body.get("submission_id")) == record["submission_id"]
            and target.get("theorem_name") == theorem_name and target.get("status") == "Proved")
    proofs.append({"theorem_id": theorem_id, "theorem_name": theorem_name,
                   "submission_id": record["submission_id"], "status": "ACCEPTED_AND_PROVED",
                   "verification_record": path.relative_to(TASK).as_posix(),
                   "verification_record_sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
# These standalone publishers preserve exact HTTP bytes inline.
# Its accepted flag is distinct from legacy publishers, so audit the actual
# submission and public readback rather than counting the prepared certificate.
inline_publications = [
    (V / "ap18/translated-summand-bound-v2",
     "OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound"),
    (V / "ap20/collision-remainder-limit-v2",
     "OAI.PiExponent.tendsto_collisionRemainder_of_normalized_pow"),
    (V / "ap20/log-translation-term-count-node-v2",
     "OAI.PiExponent.tendsto_log_translationTermCount_div"),
]
for path, theorem_name in [
    (path, name) for base, name in inline_publications
    for path in sorted(base.glob("publication*/publication.json"))
]:
    record = json.loads(path.read_bytes())
    assert record["theorem_name"] == theorem_name and record["environment"] == ENV
    verdict = record.get("last_verify_verdict", record.get("verify_response", {}))
    body = verdict.get("body", {})
    if record.get("confirmed_ACCEPTED_and_Proved") is not True:
        if (record.get("submission_id") and verdict.get("http_status") in {200, 202}
                and body.get("status") in {"PENDING", "COMPILING"}):
            pending.append({"kind": "proof-verification", "theorem_name": theorem_name,
                            "theorem_id": record["theorem_id"],
                            "submission_id": record["submission_id"],
                            "status_at_last_readback": body["status"],
                            "publication_record": path.relative_to(TASK).as_posix()})
        continue
    readback = record["post_accepted_target_readback"]
    raw = readback["raw_body_utf8"].encode("utf-8")
    assert hashlib.sha256(raw).hexdigest() == readback["raw_body_sha256"]
    target = json.loads(raw)
    manifest = json.loads((path.parent / "manifest.json").read_bytes())
    assert (readback["http_status"] == 200 and target == readback["body"]
            and verdict["http_status"] == 200 and body["status"] == "ACCEPTED"
            and body["id"] == record["submission_id"]
            and body["theorem_id"] == target["theorem_id"] == record["theorem_id"]
            and target["theorem_name"] == theorem_name and target["status"] == "Proved"
            and target["mathlib_rev"] == ENV and target["visibility"] == "public"
            and target["deprecated_at"] is None
            and target["preamble"] == manifest["preamble"]
            and target["formal_statement"] == manifest["formal_statement"])
    proofs.append({"theorem_id": record["theorem_id"], "theorem_name": theorem_name,
                   "submission_id": record["submission_id"], "status": "ACCEPTED_AND_PROVED",
                   "verification_record": path.relative_to(TASK).as_posix(),
                   "verification_record_sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
# AP21 verifies two already-published targets and stores hashed public readbacks.
for folder, theorem_id, theorem_name in [
    ("index-weight-nonneg-node", "0aeabe86-ff79-46b4-b8e3-eacc0125c4e4",
     "OAI.PiExponent.LiteralAnalytic.indexWeight_nonneg"),
    ("actual-row-count-pos-node", "df6176c8-39cf-473c-b5f0-447ca52023f2",
     "OAI.PiExponent.LiteralAnalytic.actualRowCount_pos"),
]:
    path = V / "ap21" / folder / "publication/publication.json"
    if not path.exists():
        continue
    record = json.loads(path.read_bytes())
    assert (record["target_theorem_id"] == theorem_id
            and record["target_theorem_name"] == theorem_name and record["environment"] == ENV)
    verdict = record.get("last_verify_verdict", record.get("verify_response", {}))
    body = verdict.get("body", {})
    if record.get("confirmed_ACCEPTED_and_Proved") is not True:
        if record.get("submission_id") and body.get("status") in {"PENDING", "COMPILING"}:
            pending.append({"kind": "proof-verification", "theorem_name": theorem_name,
                            "theorem_id": theorem_id, "submission_id": record["submission_id"],
                            "status_at_last_readback": body["status"],
                            "publication_record": path.relative_to(TASK).as_posix()})
        continue
    witness = record["post_accepted_target"]
    target_path = (TASK / witness["path"]).resolve()
    assert target_path.is_relative_to(V.resolve())
    assert hashlib.sha256(target_path.read_bytes()).hexdigest() == witness["sha256"]
    target = json.loads(target_path.read_bytes())
    manifest = json.loads((path.parent / "manifest.json").read_bytes())
    assert (record["own_ACCEPTED_counted"] is True
            and verdict["http_status"] in {200, 202} and body["status"] == "ACCEPTED"
            and body.get("id", body.get("submission_id")) == record["submission_id"]
            and body["theorem_id"] == target["theorem_id"] == theorem_id
            and target["theorem_name"] == theorem_name and target["status"] == "Proved"
            and target["mathlib_rev"] == ENV and target["visibility"] == "public"
            and target["deprecated_at"] is None
            and target["preamble"] == manifest["preamble"]
            and target["formal_statement"] == manifest["formal_statement"])
    proofs.append({"theorem_id": theorem_id, "theorem_name": theorem_name,
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
