"""Publish independently reviewed generic numerator PF, without mission writes.

The seven business POSTs have write-ahead journals and are never retried
automatically. The current proposal is frozen during review. New global
theorems are audited separately from its existing 88 references.
"""
from __future__ import annotations

import argparse
import hashlib
import http.client
import json
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
import uuid
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

import audit_new_mission_2026_10_07 as docs_gate
import publish_mission_2026_10_02 as official
import publish_formalization_2026_10_02 as helpers
from publish_matrix_proofs_new_mission_2026_10_07 import same_title

TASK = docs_gate.TASK
WORKSPACE = TASK.parents[1]
PF = TASK / "formalization/platform/coefficient-map-numerator-pf"
PREP = PF / "publication-preparation-2026-10-07"
OUT = PF / "publications-for-new-mission-2026-10-07"
PIN = PF / "Root-reviewed-publication-pin-2026-10-07.json"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
NEW = "19653cff-d481-498a-a717-10630d1ca1b7"
OLD = {"8195d8fe-059f-4515-92b4-57b585e2bac6", "06faf23f-00c2-4edf-92ab-1212cdb7d7d6"}
SOURCE = "2dd97638ab3fbc86124db40b78ef2f38fd7536c630d0240cb33fb4f35f8ffc77"
AUTHOR = "5a9491c73cbbb980b411a3389a4c5acd6f0e5ceb71149c8a508f9553660f0ebf"
ROOT_ID = "523f37b8-ae98-406c-a3f7-43aa8e002dd7"
PREP_PINS = {
    "prepared-publication-v4.json": "ec831fe3b832805e53292211aea5fac9723ebe5a29f3be9d0cfd91e427b35883",
    "definitions-request-v4.json": "b3de7abb267f0b965565d770caafcf9c09605405ace3c6c6e83291d4a6b9448d",
    "problems-request-v4.json": "c6c4572470d1aad9feb307f6aee3ba029ac04dd1a9c2b9c283d0f92217fc3b2e",
    "proof-explanations-v4.json": "43f9167fcff5e507ebace01211ddbf72c571ff1c649b505036acfc2609ec9b7d",
}


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1048576), b""):
            h.update(chunk)
    return h.hexdigest()


def binding(row):
    key = "task_relative" if row.get("task_relative") else "root_relative"
    relative = PurePosixPath(row[key])
    assert not relative.is_absolute() and ".." not in relative.parts
    assert relative.name.lower() not in {"credentials.json", ".env"}
    path = (TASK if key == "task_relative" else WORKSPACE).joinpath(*relative.parts)
    assert path.stat().st_size == row["bytes"] and sha(path) == row["sha256"], str(relative)
    return path


def prepare():
    if not PIN.is_file():
        raise RuntimeError("Awaiting Root's complete independent review pin; no API operation or credentials access")
    pin = load(PIN)
    assert pin["source_sha256"] == SOURCE and pin["author_sha256"] == AUTHOR
    for key in ["Root_rehashed_all_author_bindings", "Root_rehashed_all_independent_bindings",
                "complete_original_forall_domains_verified", "all_new_definition_full_types_and_values_verified",
                "independent_own_source_compilation_no_foreign_objects", "exact_seven_payloads_independently_compiled",
                "all_reachable_proofs_Std3", "complete_source_span_reachability_verified"]:
        assert pin[key] is True, key
    author_path = binding(pin["author_report"])
    independent_path = binding(pin["independent_report"])
    assert sha(author_path) == AUTHOR
    author, independent = load(author_path), load(independent_path)
    assert author["verdict"] == independent["verdict"] == "PASS"
    for report in [author, independent]:
        with ThreadPoolExecutor(max_workers=2) as pool:
            checked = list(pool.map(binding, report["stable_files"]))
        assert len(checked) == len(report["stable_files"])
    for row in pin["prepared_metadata_bindings"]:
        binding(row)
    for name, expected in PREP_PINS.items():
        assert sha(PREP / name) == expected
    manifest = load(PREP / "prepared-publication-v4.json")
    assert manifest["native_source_sha256"] == SOURCE and manifest["platform_author_sha256"] == AUTHOR
    assert manifest["new_proposal_id"] == NEW and manifest["environment"] == ENV
    assert not manifest["proposal_mutation_permitted"] and not manifest["mission_link_permitted"]
    assert len(manifest["seven_payloads"]) == 7
    for row in manifest["seven_payloads"]:
        original = binding(row["staged_source"])
        copied = binding(row["publication_source_copy"])
        assert original.read_bytes() == copied.read_bytes()
    definitions = load(PREP / "definitions-request-v4.json")
    problem_request = load(PREP / "problems-request-v4.json")
    explanations = load(PREP / "proof-explanations-v4.json")
    assert len(definitions) == 1 and len(problem_request["problems"]) == 3
    assert problem_request["env"] == ENV and problem_request["private"] is False
    assert definitions[0]["definition"] == (PF / "staged/Definitions/Def_ZetaNine_CoefficientMapNumeratorPF.lean").read_text(encoding="utf-8")
    plan = load(PF / "target-plan.json")
    originals = {r["theorem_name"]: r for r in load(PF / "problems-request.json")["problems"]}
    targets = {r["theorem_name"]: r for r in plan["targets"]}
    problems = []
    for item in problem_request["problems"]:
        name = item["theorem_name"]
        for key in ["theorem_name", "formal_statement", "preamble"]:
            assert item[key] == originals[name][key]
        source = PF / "staged" / targets[name]["local_solution"]
        code = helpers.without_lean_comments(source.read_text(encoding="utf-8"))
        assert re.search(r"(?m)^theorem solution\b", code)
        assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code)
        assert "import Theorems." not in code
        assert (PF / "staged" / targets[name]["local_reference"]).read_text(encoding="utf-8") == item["preamble"] + "\n" + item["formal_statement"] + "\n"
        problems.append({**item, "local_solution": targets[name]["local_solution"], "explanation": explanations[name]})
    save(OUT / "offline-gate.json", {"checked_at": datetime.now(timezone.utc).isoformat(),
         "Root_pin_sha256": sha(PIN), "source_sha256": SOURCE, "author_sha256": AUTHOR,
         "independent_sha256": sha(independent_path), "author_bindings_rehashed": len(author["stable_files"]),
         "independent_bindings_rehashed": len(independent["stable_files"]), "seven_payloads_exact": True,
         "new_proposal_id": NEW, "Lean_calls": 0, "credentials_access": False})
    print("Exact seven payloads and every author/independent binding reverified; no Lean calls", flush=True)
    return definitions, problems, plan


class GlobalClient(official.Client):
    def call(self, method, path, data=None, authenticated=True):
        assert not any(identifier in path for identifier in OLD)
        assert method == "GET" or (method == "POST" and path == "/agent/refresh" and not authenticated)
        if path.startswith("/mission"):
            assert method == "GET" and path == "/mission-proposals/" + NEW
        return super().call(method, path, data, authenticated)

    def post_public(self, endpoint, body, content_type):
        assert endpoint in {"/submit-definition", "/submit-problem", "/verify"}
        request = urllib.request.Request(official.BASE + endpoint, data=body, method="POST",
                  headers={"Authorization": "Bearer " + self.token, "Content-Type": content_type})
        try:
            with self.opener.open(request, timeout=40) as response:
                return json.load(response)
        except urllib.error.HTTPError as e:
            raise RuntimeError(f"Official {endpoint} returned HTTP {e.code}; inspect the journal and remote history") from None
        except (urllib.error.URLError, http.client.IncompleteRead, TimeoutError, json.JSONDecodeError):
            raise RuntimeError("POST outcome uncertain; inspect recorded history before any further business POST") from None


def client():
    docs_gate.docs()
    official.VERSION = "0.12.1"
    value = load(TASK / "publication/2026-10-07/new-public-mission/CURRENT_PLATFORM_TARGET.json")
    assert value["proposal_id"] == NEW and value["visibility"] == "public" and same_title(value["name"])
    return GlobalClient()


def proposal(remote):
    value = remote.call("GET", "/mission-proposals/" + NEW)
    assert value["id"] == NEW and value["visibility"] == "public" and same_title(value["name"])
    save(OUT / "proposal-current.json", value)
    return value


def transact(remote, operation, endpoint, body, content_type, receipt, metadata):
    if receipt.exists():
        return load(receipt)
    journal_path = OUT / "business-post-journal.json"
    journal = load(journal_path) if journal_path.exists() else {"new_proposal_id": NEW, "attempts": []}
    if any(row["operation"] == operation for row in journal["attempts"]):
        raise RuntimeError("Previous POST already journaled without a receipt; resolve from documented remote history, never blindly retry")
    wire = OUT / "wire" / (hashlib.sha256(operation.encode("utf-8")).hexdigest()[:16] + ".body")
    wire.parent.mkdir(parents=True, exist_ok=True)
    wire.write_bytes(body)
    row = {"operation": operation, "endpoint": endpoint, "intended_at": datetime.now(timezone.utc).isoformat(),
           "wire_body_sha256": sha(wire), "wire_body_bytes": len(body), "wire_body_task_relative": wire.relative_to(TASK).as_posix(),
           "content_type": content_type, "receipt_task_relative": receipt.relative_to(TASK).as_posix(),
           "receipt_saved": False, "old_mission_write": False, **metadata}
    journal["attempts"].append(row)
    save(journal_path, journal)
    result = remote.post_public(endpoint, body, content_type)
    save(receipt, result)
    row["receipt_saved"] = True
    row["job_id"] = result.get("job_id")
    row["submission_id"] = result.get("submission_id")
    if endpoint == "/submit-problem":
        assert not result.get("errors") and len(result.get("jobs", [])) == 1
        row["job_id"] = result["jobs"][0]["job_id"]
    save(journal_path, journal)
    return result


def validate_canonical(value, item, kind):
    name = item["definition_name" if kind == "definition" else "theorem_name"]
    assert value["theorem_name"] == name and value["visibility"] == "public"
    assert value["mathlib_rev"] == ENV and not value.get("deprecated_at")
    for key in ["natural_language_statement", "source"]:
        if key in item:
            assert value[key].strip() == item[key].strip(), key
    title = item.get("definition_title" if kind == "definition" else "theorem_title")
    if title is not None:
        assert value["theorem_title"] == title
    if kind == "definition":
        assert value["status"] == "Definition" and value["definition"].strip() == item["definition"].strip()
    else:
        assert value["formal_statement"].strip() == item["formal_statement"].strip()
        assert value["preamble"].strip() == item["preamble"].strip()
    return value


def published(remote, kind, item):
    name = item["definition_name" if kind == "definition" else "theorem_name"]
    receipt = load(PF / f"{kind}-receipts/{helpers.slug(name)}.json")
    if kind == "problem":
        receipt = receipt["jobs"][0] if "jobs" in receipt else receipt
    job = remote.call("GET", "/publish-jobs/" + receipt["job_id"])
    save(PF / f"{kind}-jobs/{helpers.slug(name)}.json", job)
    assert job["status"] == "PUBLISHED", f"Wait for the existing {kind} job ({job['status']}); do not resubmit"
    value = remote.call("GET", "/theorems/" + job["theorem_id"])
    validate_canonical(value, item, kind)
    save(OUT / f"canonical/{value['theorem_id']}.json", value)
    return value


def dependency_check(remote, plan):
    index = load(TASK / "formalization/platform/readback-2026-10-07/new-public-post-matrix/canonical-index.json")
    lookup = {row["theorem_name"]: row["theorem_id"] for row in index if row["status"] == "Definition"}
    for row in plan["existing_definitions"]:
        source = binding(row)
        name = row["module"].split(".")[-1].removeprefix("Def_")
        value = remote.call("GET", "/theorems/" + lookup[name])
        validate_canonical(value, {"definition_name": name, "definition": source.read_text(encoding="utf-8")}, "definition")
        save(OUT / f"dependency-readbacks/{name}.json", value)


def registration(mode):
    definitions, problems, plan = prepare()
    remote = client()
    proposal(remote)
    dependency_check(remote, plan)
    if mode == "definitions":
        for item in definitions:
            body = json.dumps(item, ensure_ascii=False).encode("utf-8")
            name = item["definition_name"]
            transact(remote, "definition_" + name, "/submit-definition", body, "application/json",
                     PF / f"definition-receipts/{name}.json", {"kind": "definition", "name": name, "env": ENV})
            print("Definition job receipt saved:", name, flush=True)
    else:
        for item in definitions:
            published(remote, "definition", item)
        for item in problems:
            name = item["theorem_name"]
            payload = {"env": ENV, "private": False, "problems": [{k: v for k, v in item.items() if k not in {"local_solution", "explanation"}}]}
            body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
            transact(remote, "problem_" + name, "/submit-problem", body, "application/json",
                     PF / f"problem-receipts/{helpers.slug(name)}.json", {"kind": "problem", "name": name, "env": ENV})
            print("Problem job receipt saved:", name, flush=True)


def poll_jobs():
    definitions, problems, _ = prepare()
    remote = client()
    proposal(remote)
    for kind, items in [("definition", definitions), ("problem", problems)]:
        for item in items:
            name = item["definition_name" if kind == "definition" else "theorem_name"]
            receipt_path = PF / f"{kind}-receipts/{helpers.slug(name)}.json"
            if not receipt_path.exists():
                continue
            receipt = load(receipt_path)
            if "jobs" in receipt:
                receipt = receipt["jobs"][0]
            value = remote.call("GET", "/publish-jobs/" + receipt["job_id"])
            save(PF / f"{kind}-jobs/{helpers.slug(name)}.json", value)
            print(kind, name, value["status"], flush=True)
            if value["status"] == "PUBLISHED":
                published(remote, kind, item)
            elif value["status"] in {"FAILED", "ERROR"}:
                raise RuntimeError("Existing publication job terminated unsuccessfully; inspect its saved diagnostics")


def verify():
    definitions, problems, plan = prepare()
    remote = client()
    proposal(remote)
    dependency_check(remote, plan)
    for item in definitions:
        published(remote, "definition", item)
    for item in problems:
        name = item["theorem_name"]
        canonical = published(remote, "problem", item)
        identifier = canonical["theorem_id"]
        source = PF / "staged" / item["local_solution"]
        boundary = "zeta9numeratorpf" + uuid.uuid4().hex
        chunks = []
        for field, value in {"theorem_id": identifier, "proof_type": "prove", "explanation": item["explanation"]}.items():
            chunks.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{field}"\r\n\r\n{value}\r\n'.encode("utf-8"))
        chunks.append(f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="{source.name}"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n'.encode("utf-8"))
        chunks.append(source.read_bytes())
        chunks.append(f"\r\n--{boundary}--\r\n".encode("utf-8"))
        result = transact(remote, "proof_" + name, "/verify", b"".join(chunks), "multipart/form-data; boundary=" + boundary,
                          PF / f"proof-receipts/{helpers.slug(name)}.json", {"kind": "proof", "name": name,
                          "theorem_id": identifier, "solution_sha256": sha(source), "env": ENV})
        assert result.get("submission_id")
        print("Proof submission receipt saved:", name, result["submission_id"], flush=True)


def proof_audit(require_accepted=False):
    definitions, problems, _ = prepare()
    remote = client()
    detail = proposal(remote)
    referenced = {row["theorem_id"] for row in detail["items"]}
    rows = []
    for item in problems:
        name = item["theorem_name"]
        receipt_path = PF / f"proof-receipts/{helpers.slug(name)}.json"
        if not receipt_path.exists():
            continue
        receipt = load(receipt_path)
        verdict = remote.call("GET", "/verify?submission_id=" + receipt["submission_id"])
        save(PF / f"proof-verdicts/{helpers.slug(name)}.json", verdict)
        canonical = published(remote, "problem", item)
        assert verdict["theorem_id"] == canonical["theorem_id"]
        rows.append({"theorem_name": name, "theorem_id": canonical["theorem_id"], "status": canonical["status"],
                    "proof_status": verdict["status"], "submission_id": receipt["submission_id"],
                    "referenced_by_new_proposal": canonical["theorem_id"] in referenced})
        print(name, verdict["status"], canonical["status"], flush=True)
    if require_accepted:
        assert len(rows) == 3 and all(row["proof_status"] == "ACCEPTED" and row["status"] == "Proved" for row in rows)
        for item in definitions:
            published(remote, "definition", item)
        root = remote.call("GET", "/theorems/" + ROOT_ID)
        assert root["status"] == "Open"
        save(OUT / "root-current.json", root)
        save(OUT / "publication-audit.json", {"checked_at": datetime.now(timezone.utc).isoformat(),
             "new_proposal_id": NEW, "proposal_status": detail["status"], "proposal_visibility": detail["visibility"],
             "new_global_complete_proofs": rows, "all_three_Accepted_public_Proved": True,
             "new_proposal_reference_count": len(referenced), "unreferenced_new_PF_proofs": sum(not row["referenced_by_new_proposal"] for row in rows),
             "new_PF_proofs_linked_by_this_script": 0, "old_mission_operations": 0, "root_status": "Open",
             "whole_local_research_formalized": False, "Lean_calls": 0})


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["prepare", "definitions", "problems", "poll-jobs", "verify", "poll-proofs", "audit"])
    args = parser.parse_args()
    try:
        if args.mode == "prepare": prepare()
        elif args.mode in {"definitions", "problems"}: registration(args.mode)
        elif args.mode == "poll-jobs": poll_jobs()
        elif args.mode == "verify": verify()
        else: proof_audit(args.mode == "audit")
    except RuntimeError as e:
        raise SystemExit(str(e)) from None
