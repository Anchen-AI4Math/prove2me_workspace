"""Resume-safe publication of the reviewed six-theorem Lean batch.

Credentials are accessed only by the official API client during a requested
platform operation. They never enter payloads, logs, archives or receipts.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import urllib.error
import urllib.request
import uuid
from pathlib import Path

from publish_mission_2026_10_02 import BASE, Client, MISSION

TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
OUT = TASK / "formalization/platform"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"


def read(name):
    return json.loads((OUT / name).read_text(encoding="utf-8"))


def save(name, value):
    path = OUT / name
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def slug(name):
    result = name.replace(".", "_")
    assert re.fullmatch(r"[A-Za-z0-9_]+", result)
    return result


def without_lean_comments(code):
    result = []
    i = 0
    depth = 0
    while i < len(code):
        if code.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and code.startswith("-/", i):
            depth -= 1
            i += 2
        elif not depth and code.startswith("--", i):
            end = code.find("\n", i)
            i = len(code) if end < 0 else end
        else:
            if not depth or code[i] == "\n":
                result.append(code[i])
            i += 1
    assert depth == 0
    return "".join(result)


def gate():
    review = read("independent-statement-review.json")
    assert review["overall_status"] == "PASS"
    assert len(review["targets"]) == 6
    assert (OUT / "task-build-exit.txt").read_text(encoding="utf-8").strip() == "0"
    for relative, expected in review["sha256"].items():
        path = TASK / relative
        if not path.exists():
            path = WORKSPACE / relative
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, relative
    log = (OUT / "task-build.log").read_text(encoding="utf-8")
    assert "Build completed successfully" in log
    assert "sorryAx" not in log
    definitions = read("definitions-request.json")
    problems = read("problems-request.json")["problems"]
    assert len(definitions) == 3 and len(problems) == 6
    proof_hashes = {}
    for item in problems:
        path = WORKSPACE / item["local_solution"]
        code = path.read_text(encoding="utf-8")
        assert re.search(r"(?m)^theorem solution\b", code), item["theorem_name"]
        assert not re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", without_lean_comments(code)), path
        assert "import Theorems." not in code, "This batch uses direct proofs only"
        assert f"{path.stem}.lean:" in log, path
        proof_hashes[item["theorem_name"]] = hashlib.sha256(path.read_bytes()).hexdigest()
    save("local-build-audit.json", {"environment": ENV, "task_build_exit": 0,
         "theorems": 6, "definitions": 3, "solution_sha256": proof_hashes,
         "independent_statement_review": "PASS", "no_sorryAx": True,
         "whole_local_research_formalized": False})
    return definitions, problems


def publish_definitions(client, definitions):
    for item in definitions:
        name = slug(item["definition_name"])
        file = f"definition-receipts/{name}.json"
        if (OUT / file).exists():
            print("Existing definition job:", name, read(file)["job_id"], flush=True)
            continue
        payload = {k: v for k, v in item.items() if k != "local_path"}
        result = client.call("POST", "/submit-definition", payload)
        assert result.get("job_id"), result
        save(file, result)
        print("Queued definition:", name, result["job_id"], flush=True)


def poll_jobs(client, definitions, problems):
    output = []
    for kind, items in [("definition", definitions), ("problem", problems)]:
        for item in items:
            name = item["definition_name" if kind == "definition" else "theorem_name"]
            receipt = OUT / f"{kind}-receipts/{slug(name)}.json"
            if not receipt.exists():
                continue
            job_id = json.loads(receipt.read_text(encoding="utf-8"))["job_id"]
            result = client.call("GET", "/publish-jobs/" + job_id)
            save(f"{kind}-jobs/{slug(name)}.json", result)
            output.append({"kind": kind, "name": name, "job_id": job_id,
                           "status": result["status"], "theorem_id": result.get("theorem_id")})
            print("Publish job:", name, result["status"], flush=True)
            if result["status"] in ("FAILED", "ERROR"):
                print("Diagnostic:", result.get("error_message", ""), flush=True)
    save("publish-job-snapshot.json", output)


def publish_problems(client, definitions, problems):
    for item in definitions:
        job = read(f"definition-jobs/{slug(item['definition_name'])}.json")
        assert job["status"] == "PUBLISHED", "Poll definition jobs before submitting targets"
    remaining = [item for item in problems if not (OUT / f"problem-receipts/{slug(item['theorem_name'])}.json").exists()]
    if not remaining:
        print("All six problem jobs already have receipts.", flush=True)
        return
    keys = ("theorem_name", "theorem_title", "formal_statement", "natural_language_statement", "preamble", "source", "tags")
    result = client.call("POST", "/submit-problem", {
        "env": ENV, "private": False,
        "problems": [{k: item[k] for k in keys} for item in remaining]})
    save("problem-batch-response.json", result)
    for job in result.get("jobs", []):
        save(f"problem-receipts/{slug(job['name'])}.json", job)
        print("Queued theorem:", job["name"], job["job_id"], flush=True)
    assert not result.get("errors"), result.get("errors")


def verify(client, problems):
    for item in problems:
        name = slug(item["theorem_name"])
        if (OUT / f"proof-receipts/{name}.json").exists():
            print("Existing proof submission:", name, flush=True)
            continue
        job = read(f"problem-jobs/{name}.json")
        assert job["status"] == "PUBLISHED", "Poll statement jobs before verifying"
        theorem_id = job["theorem_id"]
        theorem = client.call("GET", "/theorems/" + theorem_id)
        assert theorem["formal_statement"].strip() == item["formal_statement"].strip(), name
        assert theorem["visibility"] == "public"
        assert theorem["mathlib_rev"] == ENV
        save(f"target-readback/{name}.json", theorem)
        path = WORKSPACE / item["local_solution"]
        boundary = "zeta9" + uuid.uuid4().hex
        chunks = []
        for field, value in {"theorem_id": theorem_id, "proof_type": "prove", "explanation": item["explanation"]}.items():
            chunks.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{field}"\r\n\r\n{value}\r\n'.encode("utf-8"))
        chunks.append(f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="{path.name}"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n'.encode("utf-8"))
        chunks.append(path.read_bytes())
        chunks.append(f"\r\n--{boundary}--\r\n".encode())
        request = urllib.request.Request(BASE + "/verify", data=b"".join(chunks), method="POST",
            headers={"Authorization": "Bearer " + client.token,
                     "Content-Type": "multipart/form-data; boundary=" + boundary})
        try:
            with client.opener.open(request, timeout=40) as response:
                result = json.load(response)
        except urllib.error.HTTPError as error:
            raise RuntimeError(f"Official proof verification returned HTTP {error.code}") from None
        except urllib.error.URLError:
            raise RuntimeError("Proof submission network outcome uncertain; inspect the target's submission history before retrying") from None
        assert result.get("submission_id"), result
        save(f"proof-receipts/{name}.json", result)
        print("Queued proof:", name, result["submission_id"], flush=True)


def poll_proofs(client, problems):
    results = []
    for item in problems:
        name = slug(item["theorem_name"])
        path = OUT / f"proof-receipts/{name}.json"
        if not path.exists():
            continue
        identifier = read(f"proof-receipts/{name}.json")["submission_id"]
        result = client.call("GET", "/verify?submission_id=" + identifier)
        save(f"proof-verdicts/{name}.json", result)
        results.append({"name": item["theorem_name"], "submission_id": identifier, "status": result["status"]})
        print("Proof verdict:", item["theorem_name"], result["status"], flush=True)
        if result["status"] not in ("PENDING", "COMPILING", "VERIFYING", "RUNNING", "ACCEPTED"):
            print(json.dumps(result, ensure_ascii=False), flush=True)
    save("proof-verdict-snapshot.json", results)


def link(client, problems):
    current = client.call("GET", f"/missions/{MISSION}/milestones?limit=200&offset=0")["milestones"]
    linked = {row["theorem"]["id"]: row for row in current if row.get("theorem")}
    titles = ["Equation (5) — Primitive-row Gram content", "Equation (6) — Center denominator divisor",
              "Opening endpoint statement — Eightfold derivative cancellation",
              "Theorem 1, clearing bound — Harmonic denominator lcm power",
              "Lemma 2, limit consequence — Normalized denominator error",
              "Corollary 3, stability step — Transfer of an established rate"]
    audit = []
    for item, title in zip(problems, titles, strict=True):
        name = slug(item["theorem_name"])
        verdict = read(f"proof-verdicts/{name}.json")
        assert verdict["status"] == "ACCEPTED", name
        job = read(f"problem-jobs/{name}.json")
        identifier = job["theorem_id"]
        theorem = client.call("GET", "/theorems/" + identifier)
        assert theorem["status"] == "Proved" and theorem["visibility"] == "public"
        assert theorem["formal_statement"].strip() == item["formal_statement"].strip()
        save(f"proved-readback/{name}.json", theorem)
        if identifier not in linked:
            result = client.call("POST", f"/missions/{MISSION}/milestones", {
                "title": title, "milestone_description": item["natural_language_statement"],
                "theorem_id": identifier})
            save(f"milestone-receipts/{name}.json", result)
        audit.append({"theorem_name": item["theorem_name"], "theorem_id": identifier,
                      "status": "Proved", "visibility": "public", "submission_id": verdict.get("submission_id")})
    after = client.call("GET", f"/missions/{MISSION}/milestones?limit=200&offset=0")["milestones"]
    after_linked = {row["theorem"]["id"] for row in after if row.get("theorem")}
    assert all(row["theorem_id"] in after_linked for row in audit)
    mission = client.mission()
    assert mission["main_theorem"]["status"] == "Open"
    save("mission-after.json", mission)
    save("milestones-after.json", after)
    save("publication-audit.json", {"mission_id": MISSION, "new_proved_theorems": audit,
        "linked_readback_verified": True, "root_status": "Open",
        "milestones": len(after), "completed_milestones": sum(bool(r.get("completed")) for r in after),
        "whole_local_research_formalized": False})
    print("All six public proofs are Proved and linked to the original mission; root remains Open.", flush=True)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("definitions", "poll-jobs", "problems", "verify", "poll-proofs", "link"))
    args = parser.parse_args()
    definitions, problems = gate()
    client = Client()
    if args.mode == "definitions": publish_definitions(client, definitions)
    elif args.mode == "poll-jobs": poll_jobs(client, definitions, problems)
    elif args.mode == "problems": publish_problems(client, definitions, problems)
    elif args.mode == "verify": verify(client, problems)
    elif args.mode == "poll-proofs": poll_proofs(client, problems)
    else: link(client, problems)


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        raise SystemExit(str(error)) from None
