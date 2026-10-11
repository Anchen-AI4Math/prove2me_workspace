"""Publish the reviewed actual finite pole-coefficient entry, preserving its scope."""
from __future__ import annotations
import argparse
import hashlib
import re
import sys

import publish_formalization_2026_10_02 as api

OUT = api.TASK / "formalization/platform/coefficient-map"
SOURCE = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_CHECKS = 11
EXPLANATION_OVERRIDES = {}
TITLE_OVERRIDES = {}
SCOPE_LABEL = "finite pole-coefficient entry"
EXPECTED_AUTHOR_HASH = None
AUTHOR_METADATA_ADAPTER = None
TARGET_AUDIT_ADAPTER = None
INDEPENDENT_REVIEW_PATH = "independent-integration-review.json"
EXPECTED_INDEPENDENT_HASH = None
INDEPENDENT_REVIEW_ADAPTER = None
EXTRA_SCOPE_AUDIT = {}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def gate():
    api.OUT = OUT
    author = api.read("author-audit.json")
    if EXPECTED_AUTHOR_HASH is not None:
        assert digest(OUT / "author-audit.json") == EXPECTED_AUTHOR_HASH
    assert author["verdict"] == "PASS" and author["source_sha256"] == SOURCE
    if AUTHOR_METADATA_ADAPTER is not None:
        author = AUTHOR_METADATA_ADAPTER(author)
    assert author["mathlib_rev"] == api.ENV and author["lean_toolchain"] == "leanprover/lean4:v4.33.1"
    assert len(author["checks"]) == EXPECTED_CHECKS and all(c["pass"] for c in author["checks"])
    for row in author["stable_files"]:
        path = api.TASK / row["task_relative"]
        assert path.resolve().is_relative_to(api.TASK.resolve())
        assert digest(path) == row["sha256"] and path.stat().st_size == row["bytes"]
    if EXPECTED_INDEPENDENT_HASH is not None:
        assert digest(OUT / INDEPENDENT_REVIEW_PATH) == EXPECTED_INDEPENDENT_HASH
    review = api.read(INDEPENDENT_REVIEW_PATH)
    if INDEPENDENT_REVIEW_ADAPTER is not None:
        review = INDEPENDENT_REVIEW_ADAPTER(review)
    assert review["verdict"] == "PASS"
    assert review["checks"] and all(c["pass"] for c in review["checks"])
    assert all(f.get("severity") in {"informational", "information"} for f in review.get("findings", []))
    assert review.get("sha256") or review.get("stable_files"), "Independent bindings required."
    for relative, expected in review.get("sha256", {}).items():
        path = api.TASK / relative
        if not path.exists():
            path = api.WORKSPACE / relative
        assert digest(path) == expected, relative
    for row in review.get("stable_files", []):
        base = api.TASK if row.get("task_relative") else api.WORKSPACE
        relative = row.get("task_relative") or row["root_relative"]
        path = base / relative
        assert path.resolve().is_relative_to(base.resolve())
        assert path.stat().st_size == row["bytes"] and digest(path) == row["sha256"], relative
    assert (OUT / "task-build-exit.txt").read_text().strip() == "0"
    log = (OUT / "task-build.log").read_text(encoding="utf-8")
    assert "Build completed successfully" in log
    plan = api.read("target-plan.json")
    if TARGET_AUDIT_ADAPTER is not None:
        author = TARGET_AUDIT_ADAPTER(author, plan)
    definitions = api.read("definitions-request.json")
    definitions = [{**d, "local_path": plan["local_definition"]} for d in definitions]
    problem_request = api.read("problems-request.json")
    assert problem_request["env"] == api.ENV and problem_request["private"] is False
    problems = problem_request["problems"]
    assert len(definitions) == 1 and len(problems) == 3
    plan_rows = {t["theorem_name"]: t for t in plan["targets"]}
    author_rows = {t["theorem_name"]: t for t in author["targets"]}
    explanations = {
        "clear_highest_pole": "Factor the actual finite pole product at j, with every t+k nonzero. Cancel only these proved nonzero factors to identify the genuine cleared rational expression. This is a regular-point identity and does not evaluate a pole through totalized division.",
        "leadingPoleCoefficient_eq": "Evaluate the actual cleared numerator and erased pole product at -j using the proved rising and falling finite factorial products. Their nonzero factorial quotient gives the signed ninth-power binomial formula for every natural n and j<=n, including n=0; the coefficient is not defined by this formula.",
        "weightedLeadingPoleCoefficient_eq_even": "Use the actual rational family multiplied by W(t(t+n)), its legitimate cleared local expression, and the proved unweighted leading formula. Evenness removes the (-1)^n phase and the actual local coordinate gives W(-j(n-j)). Arbitrary W may make this weighted coefficient zero; no full coefficient-map invertibility or irrationality conclusion is asserted.",
    }
    explanations.update(EXPLANATION_OVERRIDES)
    combined = []
    for item in problems:
        target = plan_rows[item["theorem_name"]]
        checked = author_rows[item["theorem_name"]]
        assert checked["original_solution_reference_type_exactly_equal"] is True
        assert checked["extra_top_level_solution_binders"] == []
        assert set(checked["original_axioms"]) == set(checked["solution_axioms"]) == STANDARD
        path = api.WORKSPACE / target["local_solution"]
        assert digest(path) == checked["solution_sha256"]
        assert path.read_bytes() == (OUT / "staged" / target["local_solution"]).read_bytes()
        reference = api.WORKSPACE / target["local_reference"]
        assert digest(reference) == checked["reference_sha256"]
        code = path.read_text(encoding="utf-8")
        assert re.search(r"(?m)^theorem solution\b", code)
        assert not re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", api.without_lean_comments(code))
        assert not re.search(r"(?m)^import (?:Theorems|Solutions)\.", code)
        assert path.name + ":" in log
        combined.append({**item, "local_solution": target["local_solution"],
            "local_reference": target["local_reference"],
            "explanation": explanations[item["theorem_name"].split(".")[-1]]})
    definition_path = api.WORKSPACE / plan["local_definition"]
    assert definition_path.read_bytes() == (OUT / "staged" / plan["local_definition"]).read_bytes()
    assert definition_path.read_text(encoding="utf-8") == definitions[0]["definition"]
    local_audit = {"environment": api.ENV, "task_build_exit": 0,
        "definitions": 1, "theorems": 3, "independent_integration_review": "PASS",
        "new_three_solutions_standard_three_only": True,
        "root_other_PNT_mirror_is_type_integration_only": True,
        "scope": SCOPE_LABEL, "full_F_proved": False, "root_irrationality_proved": False}
    assert not set(EXTRA_SCOPE_AUDIT).intersection(local_audit)
    api.save("local-build-audit.json", {**local_audit, **EXTRA_SCOPE_AUDIT})
    return definitions, combined


def link(client, problems):
    rows = client.call("GET", f"/missions/{api.MISSION}/milestones?limit=200&offset=0")["milestones"]
    linked = {r["theorem"]["id"] for r in rows if r.get("theorem")}
    titles = {
        "clear_highest_pole": "Z9.F finite entry — Actual rational-function pole clearance",
        "leadingPoleCoefficient_eq": "Z9.F finite entry — Genuine highest-pole integer formula",
        "weightedLeadingPoleCoefficient_eq_even": "Z9.F finite entry — Actual weighted highest-pole multiplier",
    }
    titles.update(TITLE_OVERRIDES)
    audit = []
    for item in problems:
        name = api.slug(item["theorem_name"])
        verdict = api.read(f"proof-verdicts/{name}.json")
        assert verdict["status"] == "ACCEPTED"
        identifier = api.read(f"problem-jobs/{name}.json")["theorem_id"]
        theorem = client.call("GET", "/theorems/" + identifier)
        assert theorem["status"] == "Proved" and theorem["visibility"] == "public"
        assert theorem["mathlib_rev"] == api.ENV
        assert theorem["formal_statement"].strip() == item["formal_statement"].strip()
        api.save(f"proved-readback/{name}.json", theorem)
        if identifier not in linked:
            result = client.call("POST", f"/missions/{api.MISSION}/milestones", {
                "title": titles[item["theorem_name"].split(".")[-1]],
                "milestone_description": item["natural_language_statement"], "theorem_id": identifier})
            api.save(f"milestone-receipts/{name}.json", result)
        audit.append({"theorem_name": item["theorem_name"], "theorem_id": identifier,
            "status": "Proved", "visibility": "public",
            "submission_id": api.read(f"proof-receipts/{name}.json")["submission_id"]})
    rows = client.call("GET", f"/missions/{api.MISSION}/milestones?limit=200&offset=0")["milestones"]
    actual_links = {r["theorem"]["id"] for r in rows if r.get("theorem")}
    assert all(t["theorem_id"] in actual_links for t in audit)
    mission = client.mission()
    assert mission["main_theorem"]["status"] == "Open"
    api.save("mission-after.json", mission)
    api.save("milestones-after.json", rows)
    publication = {"mission_id": api.MISSION, "new_proved_theorems": audit,
        "linked_readback_verified": True, "root_status": "Open", "milestones": len(rows),
        "linked_theorems": len(actual_links), "completed_milestones": sum(bool(r.get("completed")) for r in rows),
        "scope": SCOPE_LABEL, "full_F_invertibility_proved": False}
    assert not set(EXTRA_SCOPE_AUDIT).intersection(publication)
    api.save("publication-audit.json", {**publication, **EXTRA_SCOPE_AUDIT})
    print(f"Three {SCOPE_LABEL} proofs are public Proved and linked to the original mission.", flush=True)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("definitions", "poll-jobs", "problems", "verify", "poll-proofs", "link", "check-only"))
    args = parser.parse_args()
    definitions, problems = gate()
    if args.mode == "check-only":
        print("Frozen original, independent review, installed bytes and scoped build verified. No API operation.")
        return
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
