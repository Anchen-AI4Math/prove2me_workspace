"""Advance one verified independent stage, recording every request before/after it."""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from urllib.parse import quote
from generate_independent_node import check_stage_inputs

sys.stdout.reconfigure(encoding="utf-8")
TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
STAGES = TASK / "verification/independent"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    stage = (STAGES / sys.argv[1]).resolve()
    if not stage.is_relative_to(STAGES.resolve()):
        raise SystemExit("Stage path escapes the task")
    manifest = read(stage / "manifest.json")
    if not manifest["validated"] or digest(ROOT / manifest["validation"]) != manifest["validation_sha256"]:
        raise SystemExit("Exact upload bytes must pass the kernel type and strict preflight gates")
    validation = read(ROOT / manifest["validation"])
    if not validation["validated"] or not validation["kernel_types_equal"] or not validation["standard_axioms_only"]:
        raise SystemExit("Independent stage has no clean type/axiom certificate")
    check_stage_inputs(stage, manifest)
    for field in ("runtime_sha256", "statement_sha256", "solution_sha256", "snapshot_sha256",
                  "source_graph_sha256", "facts_sha256"):
        if validation[field] != manifest[field]:
            raise SystemExit("Validation certificate describes a different stage: " + field)
    for filename, field in (("original-type.json", "original_type_sha256"),
                            ("generated-type.json", "generated_type_sha256")):
        if digest(stage / filename) != validation[field]:
            raise SystemExit("A certified kernel type snapshot changed")
    expected_files = {Path(manifest["statement"]).name, Path(manifest["solution"]).name,
                      "SnapshotOriginal.lean", "SnapshotGenerated.lean"}
    if set(validation["preflights"]) != expected_files:
        raise SystemExit("The certificate must contain all four staged compilation checks")
    for filename, record in validation["preflights"].items():
        if (record["exit_code"] or record["timed_out"] or not record["source_unchanged"]
                or not 0 < record["timeout_seconds"] <= 300
                or not 0 < record["seconds"] <= 300
                or record["runtime_sha256"] != manifest["runtime_sha256"]
                or ROOT / record["source"] != stage / filename
                or digest(ROOT / record["source"]) != record["source_sha256"]
                or digest(ROOT / record["log"]) != record["log_sha256"]):
            raise SystemExit("A strict compilation certificate is stale or failed")
    metadata = read(stage / "metadata.json")
    spec = importlib.util.spec_from_file_location("p2m", ROOT / "scripts/p2m_api.py")
    p2m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p2m)
    record_path = stage / "publication.json"
    record = read(record_path) if record_path.exists() else {"theorem_name": manifest["theorem_name"]}
    metadata_sha256 = digest(stage / "metadata.json")
    if record.get("metadata_sha256", metadata_sha256) != metadata_sha256:
        raise SystemExit("Metadata changed after the recorded publication request")
    record["metadata_sha256"] = metadata_sha256
    problem = {"theorem_name": manifest["theorem_name"], "preamble": manifest["preamble"],
               "formal_statement": manifest["formal_statement"], "source": manifest["source_url"],
               **{field: metadata[field] for field in
                  ("theorem_title", "natural_language_statement", "tags")}}
    publication_payload = {"problems": [problem], "env": ENV, "private": False}
    payload_bytes = json.dumps(publication_payload).encode("utf-8")
    payload_sha256 = hashlib.sha256(payload_bytes).hexdigest()
    if record.get("publish_payload_sha256", payload_sha256) != payload_sha256:
        raise SystemExit("The immutable publication request changed")
    record["publish_payload_sha256"] = payload_sha256

    def save():
        record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
        record_path.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    def request(method, path, **kwargs):
        status, body = p2m._request(method, path, token=p2m.get_token(), **kwargs)
        return status, json.loads(body)

    def readback(theorem_id):
        status, existing = request("GET", "/theorems/" + theorem_id)
        record["target_readback"] = {"http_status": status, "body": existing}
        save()
        if (status != 200 or existing.get("theorem_id") != theorem_id
                or existing.get("theorem_name") != manifest["theorem_name"]
                or existing.get("mathlib_rev") != ENV
                or existing.get("visibility") != "public"
                or existing.get("deprecated_at") is not None
                or existing.get("formal_statement") != manifest["formal_statement"]
                or existing.get("preamble") != manifest["preamble"]):
            raise SystemExit("Target identity, exact text, visibility or environment differs; nothing verified")
        return existing

    if not record.get("theorem_id") and not record.get("publish_intent"):
        matches, offset = [], 0
        while True:
            status, body = request("GET", "/theorems?theorem_name=" + quote(manifest["theorem_name"]) +
                                   f"&env={ENV}&limit=100&offset={offset}")
            if status != 200:
                raise SystemExit(f"Exact-name lookup failed with HTTP {status}; nothing posted")
            page = body["theorems"]
            matches.extend(item for item in page if item["theorem_name"] == manifest["theorem_name"])
            offset += len(page)
            if offset >= body["total"]:
                break
            if not page:
                raise SystemExit("Exact-name lookup pagination is incomplete; nothing posted")
        if matches:
            if len(matches) != 1:
                raise SystemExit("Ambiguous existing theorem; inspect environment before reusing")
            existing = readback(matches[0]["theorem_id"])
            record["theorem_id"] = existing["theorem_id"]
            save()
        else:
            status, environments = request("GET", "/environments")
            if status != 200 or not any(
                    item.get("mathlib_rev") == ENV and item.get("toolchain") == "leanprover/lean4:v4.33.1"
                    for item in environments.get("environments", [])):
                raise SystemExit("Pinned platform environment is unavailable; nothing posted")
            record["publish_intent"] = {"at_utc": datetime.now(timezone.utc).isoformat(),
                                        "statement_sha256": manifest["statement_sha256"],
                                        "payload": publication_payload,
                                        "payload_sha256": payload_sha256}
            save()
            status, body = request("POST", "/submit-problem", raw_body=payload_bytes)
            record["publish_response"] = {"http_status": status, "body": body}
            jobs = body.get("jobs", [])
            if (status == 202 and not body.get("errors") and len(jobs) == 1
                    and jobs[0].get("name") == manifest["theorem_name"] and jobs[0].get("job_id")):
                record["job_id"] = jobs[0]["job_id"]
            save()
            print(json.dumps(record["publish_response"], ensure_ascii=False))
            return
    if not record.get("theorem_id"):
        if not record.get("job_id"):
            raise SystemExit("An uncertain publish attempt is recorded; inspect it before another POST")
        status, body = request("GET", "/publish-jobs/" + record["job_id"])
        record["last_publish_verdict"] = body
        if status == 200 and body.get("status") == "PUBLISHED":
            record["theorem_id"] = body["theorem_id"]
        save()
        print(json.dumps({"http_status": status, "status": body.get("status"),
                          "theorem_id": record.get("theorem_id"), "error_message": body.get("error_message")}))
        if not record.get("theorem_id"):
            return
    if not record.get("submission_id"):
        readback(record["theorem_id"])
        if record.get("verify_intent"):
            raise SystemExit("An uncertain verify attempt is recorded; inspect it before another POST")
        solution = ROOT / manifest["solution"]
        payload, ctype = p2m._multipart(
            {"theorem_id": record["theorem_id"], "proof_type": "prove", "explanation": metadata["explanation"]},
            {"file": (solution.name, solution.read_bytes())})
        record["verify_intent"] = {"at_utc": datetime.now(timezone.utc).isoformat(),
                                   "solution_sha256": manifest["solution_sha256"],
                                   "theorem_id": record["theorem_id"],
                                   "multipart_sha256": hashlib.sha256(payload).hexdigest()}
        save()
        status, body = request("POST", "/verify", raw_body=payload, ctype=ctype)
        record["verify_response"] = {"http_status": status, "body": body}
        if status in (200, 202) and body.get("status") in ("PENDING", "COMPILING"):
            record["submission_id"] = body.get("submission_id") or body.get("id")
        save()
        print(json.dumps(record["verify_response"], ensure_ascii=False))
    else:
        status, body = request("GET", "/verify?submission_id=" + record["submission_id"])
        record["last_verify_verdict"] = body
        save()
        if status == 200 and body.get("theorem_id") != record["theorem_id"]:
            raise SystemExit("Verification response belongs to a different theorem")
        if status == 200 and body.get("status") == "ACCEPTED":
            existing = readback(record["theorem_id"])
            record["confirmed_proved"] = existing.get("status") == "Proved"
            save()
        print(json.dumps({"http_status": status, "theorem_id": record["theorem_id"],
                          "submission_id": record["submission_id"], "status": body.get("status"),
                          "error_message": body.get("error_message")}))


if __name__ == "__main__":
    main()
