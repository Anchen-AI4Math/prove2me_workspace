"""Publish the exact all-even C3 coefficient results after independent review."""
from __future__ import annotations

import argparse
import hashlib
import re
import sys

import publish_formalization_2026_10_02 as api

OUT = api.TASK / "formalization/platform/coefficient"


def gate():
    api.OUT = OUT
    review = api.read("independent-integration-review.json")
    assert review["verdict"] == "PASS"
    assert not [f for f in review.get("findings", []) if f.get("severity") != "informational"]
    assert len(review["checks"]) >= 12 and all(row["pass"] for row in review["checks"])
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
    assert len(definitions) == 1 and len(problems) == 2
    for item in problems:
        path = api.WORKSPACE / item["local_solution"]
        code = path.read_text(encoding="utf-8")
        assert re.search(r"(?m)^theorem solution\b", code)
        assert not re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", api.without_lean_comments(code))
        assert "import Theorems." not in code
        assert f"{path.stem}.lean:" in log
    api.save("local-build-audit.json", {"environment": api.ENV, "task_build_exit": 0,
        "definitions": 1, "theorems": 2, "independent_integration_review": "PASS",
        "C3_all_even_coefficient_complete": True, "no_sorryAx": True,
        "linear_form_nonvanishing_proved": False, "whole_local_research_formalized": False})
    return definitions, problems


def link(client, problems):
    rows = client.call("GET", f"/missions/{api.MISSION}/milestones?limit=200&offset=0")["milestones"]
    linked = {r["theorem"]["id"] for r in rows if r.get("theorem")}
    titles = {
        "A_even_signed_lower": "C3 — Genuine coefficient signed lower bound for every even degree",
        "A_ne_zero_of_even": "C3 — Genuine short-zero coefficient nonvanishing for all even degrees",
    }
    audit = []
    for item in problems:
        name = api.slug(item["theorem_name"])
        assert api.read(f"proof-verdicts/{name}.json")["status"] == "ACCEPTED"
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
    assert all(t["theorem_id"] in {r["theorem"]["id"] for r in rows if r.get("theorem")} for t in audit)
    mission = client.mission()
    assert mission["main_theorem"]["status"] == "Open"
    api.save("mission-after.json", mission)
    api.save("milestones-after.json", rows)
    api.save("publication-audit.json", {"mission_id": api.MISSION, "new_proved_theorems": audit,
        "linked_readback_verified": True, "root_status": "Open", "milestones": len(rows),
        "completed_milestones": sum(bool(r.get("completed")) for r in rows)})
    print("Two public C3 coefficient proofs are Proved and linked to the original mission.", flush=True)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("definitions", "poll-jobs", "problems", "verify", "poll-proofs", "link"))
    args = parser.parse_args()
    definitions, problems = gate()
    client = api.Client()
    if args.mode == "definitions": api.publish_definitions(client, definitions)
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
