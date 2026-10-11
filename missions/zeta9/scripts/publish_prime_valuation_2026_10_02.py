"""Resume-safe API publication of the reviewed finite-prime arithmetic batch."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys

import publish_formalization_2026_10_02 as api

OUT = api.TASK / "formalization/platform/prime-valuation"


def gate():
    api.OUT = OUT
    review = api.read("independent-integration-review.json")
    assert review["verdict"] == "PASS" and not review["findings"]
    assert len(review["checks"]) >= 40 and all(row["pass"] for row in review["checks"])
    for relative, expected in review["sha256"].items():
        path = api.TASK / relative
        if not path.exists():
            path = api.WORKSPACE / relative
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, relative
    assert (OUT / "task-build-exit.txt").read_text().strip() == "0"
    log = (OUT / "task-build.log").read_text(encoding="utf-8")
    assert "Build completed successfully" in log and "sorryAx" not in log
    definitions = api.read("definitions-request.json")
    problems = api.read("problems-request.json")["problems"]
    assert len(definitions) == 1 and len(problems) == 3
    for item in problems:
        path = api.WORKSPACE / item["local_solution"]
        code = path.read_text(encoding="utf-8")
        assert re.search(r"(?m)^theorem solution\b", code)
        assert not re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", api.without_lean_comments(code))
        assert "import Theorems." not in code
        assert f"{path.stem}.lean:" in log
    api.save("local-build-audit.json", {"environment": api.ENV, "task_build_exit": 0,
        "definitions": 1, "theorems": 3, "independent_integration_review": "PASS",
        "no_sorryAx": True, "full_harmonic_asymptotic_formalized": False})
    return definitions, problems


def link(client, problems):
    rows = client.call("GET", f"/missions/{api.MISSION}/milestones?limit=200&offset=0")["milestones"]
    linked = {r["theorem"]["id"] for r in rows if r.get("theorem")}
    titles = {
        "harmonic_finite_prime_product_dvd": "Finite prime blocks — Product divisor of the harmonic denominator",
        "harmonic_finite_prime_log_lower_bound": "Finite prime blocks — Actual harmonic log denominator lower bound",
        "harmonic_large_prime_den_valuation": "Finite prime blocks — Exact exponent with the actual unit prefix",
    }
    audit = []
    for item in problems:
        name = api.slug(item["theorem_name"])
        verdict = api.read(f"proof-verdicts/{name}.json")
        assert verdict["status"] == "ACCEPTED"
        identifier = api.read(f"problem-jobs/{name}.json")["theorem_id"]
        theorem = client.call("GET", "/theorems/" + identifier)
        assert theorem["status"] == "Proved" and theorem["visibility"] == "public"
        assert theorem["formal_statement"].strip() == item["formal_statement"].strip()
        api.save(f"proved-readback/{name}.json", theorem)
        if identifier not in linked:
            result = client.call("POST", f"/missions/{api.MISSION}/milestones", {
                "title": titles[item["theorem_name"].split(".")[-1]],
                "milestone_description": item["natural_language_statement"], "theorem_id": identifier})
            api.save(f"milestone-receipts/{name}.json", result)
        audit.append({"theorem_name": item["theorem_name"], "theorem_id": identifier,
                      "status": "Proved", "visibility": "public"})
    rows = client.call("GET", f"/missions/{api.MISSION}/milestones?limit=200&offset=0")["milestones"]
    linked = {r["theorem"]["id"] for r in rows if r.get("theorem")}
    assert all(t["theorem_id"] in linked for t in audit)
    mission = client.mission()
    assert mission["main_theorem"]["status"] == "Open"
    api.save("mission-after.json", mission)
    api.save("milestones-after.json", rows)
    api.save("publication-audit.json", {"mission_id": api.MISSION, "new_proved_theorems": audit,
        "linked_readback_verified": True, "root_status": "Open", "milestones": len(rows),
        "completed_milestones": sum(bool(r.get("completed")) for r in rows),
        "full_harmonic_asymptotic_formalized": False})
    print("Three finite-prime proofs are public, Proved, and linked to the original mission; root remains Open.", flush=True)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("definitions", "poll-jobs", "problems", "verify", "poll-proofs", "link"))
    args = parser.parse_args()
    definitions, problems = gate()
    client = api.Client()
    if args.mode == "definitions":
        # A real published dependency is required before queueing this definition.
        receipt = json.loads((api.TASK / "formalization/platform/definition-receipts/ZetaNine_HarmonicStability.json").read_text(encoding="utf-8"))
        job = client.call("GET", "/publish-jobs/" + receipt["job_id"])
        assert job["status"] == "PUBLISHED", "Existing harmonic definition is still queued"
        api.publish_definitions(client, definitions)
    elif args.mode == "poll-jobs": api.poll_jobs(client, definitions, problems)
    elif args.mode == "problems": api.publish_problems(client, definitions, problems)
    elif args.mode == "verify": api.verify(client, problems)
    elif args.mode == "poll-proofs": api.poll_proofs(client, problems)
    else: link(client, problems)


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        raise SystemExit(str(error)) from None
