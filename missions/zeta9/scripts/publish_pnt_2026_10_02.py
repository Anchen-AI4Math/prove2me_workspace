"""Publish four exact harmonic endpoints with the sole already-Proved PNT boundary."""
from __future__ import annotations

import argparse
import hashlib
import re
import sys

import publish_formalization_2026_10_02 as api

OUT = api.TASK / "formalization/platform/pnt"
BOUNDARY = "7cfa31c8-4063-4b52-81fc-8b2f2a59495e"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
ENDPOINTS = {"psi_pnt_rate", "harmonic_log_den_rate", "harmonic_nine_double_log_den_rate",
             "harmonic_perturbed_log_den_rate"}


def gate():
    api.OUT = OUT
    review = api.read("independent-integration-review.json")
    assert review["verdict"] == "PASS"
    assert review["checks"] and all(row["pass"] for row in review["checks"])
    assert not [f for f in review.get("findings", []) if f.get("severity") != "informational"]
    for label, record in review["reviewed_hashes"].items():
        path = api.WORKSPACE / record["root_relative"]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == record["sha256"], label
    audit = api.read("integration-audit.json")
    assert audit["verdict"] == "PASS_OFFLINE_MECHANICAL_FIDELITY"
    assert audit["four_original_endpoints"] is True
    assert audit["new_pnt_or_harmonic_baseline_assumptions"] == []
    assert audit["new_public_definitions"] == []
    assert audit["native_identical_canonical_solution_bytes_standard_three_axioms"] is True
    assert audit["canonical_stub_build_standard_three_axioms"] is False
    assert audit["root_formal_build_with_type_only_medium_pnt_mirror_is_closed_proof"] is False
    assert audit["only_external_proved_theorem_boundary"]["id"] == BOUNDARY
    assert len(audit["checks"]) == 4
    checked = {row["theorem_name"]: row for row in audit["checks"]}
    definitions = api.read("definitions-request.json")
    problems = api.read("problems-request.json")["problems"]
    assert definitions == []
    assert {p["theorem_name"].split(".")[-1] for p in problems} == ENDPOINTS
    assert (OUT / "task-build-exit.txt").read_text().strip() == "0"
    assert "Build completed successfully" in (OUT / "task-build.log").read_text(encoding="utf-8")
    hashes = {}
    for item in problems:
        row = checked[item["theorem_name"]]
        assert row["type_equal_original_native_stub_reference"] is True
        assert row["native_solution_is_closed_proof"] is True
        assert row["stub_solution_is_closed_proof"] is False
        assert set(row["native_canonical_solution_axioms"]) <= STANDARD
        assert set(row["original_axioms"]) <= STANDARD
        assert set(row["stub_canonical_solution_axioms"]) <= STANDARD | {"sorryAx"}
        assert "sorryAx" in row["stub_canonical_solution_axioms"]
        path = api.WORKSPACE / item["local_solution"]
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        assert digest == row["solution_sha256"]
        assert path.read_bytes() == (OUT / "staged" / item["local_solution"]).read_bytes()
        code = path.read_text(encoding="utf-8")
        assert re.search(r"(?m)^theorem solution\b", code)
        assert not re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", api.without_lean_comments(code))
        imports = [line.split()[1] for line in code.splitlines() if line.startswith("import Theorems.")]
        assert imports == ["Theorems.Thm_MediumPNT"]
        assert item["proved_theorem_dependencies"] == [{"theorem_name": "MediumPNT", "theorem_id": BOUNDARY}]
        hashes[item["theorem_name"]] = digest
    api.save("local-build-audit.json", {"environment": api.ENV, "task_build_exit": 0,
        "definitions": 0, "theorems": 4, "solution_sha256": hashes,
        "independent_integration_review": "PASS", "own_sorry_free": True,
        "native_identical_bytes_closed_standard_three": True, "root_stub_build_is_closed_proof": False,
        "sole_platform_proved_boundary": BOUNDARY, "root_irrationality_proved": False})
    return definitions, problems


def check_boundary(client):
    theorem = client.call("GET", "/theorems/" + BOUNDARY)
    assert theorem["status"] == "Proved" and theorem["visibility"] == "public"
    assert theorem["mathlib_rev"] == api.ENV
    assert theorem["formal_statement"].strip() == api.read("medium-pnt-proved-readback.json")["formal_statement"].strip()
    api.save("boundary-live-readback.json", theorem)


def link(client, problems):
    rows = client.call("GET", f"/missions/{api.MISSION}/milestones?limit=200&offset=0")["milestones"]
    linked = {r["theorem"]["id"] for r in rows if r.get("theorem")}
    titles = {
        "psi_pnt_rate": "PNT transfer — Actual Chebyshev psi normalized rate",
        "harmonic_log_den_rate": "Theorem 1 — Unconditional actual harmonic denominator rate",
        "harmonic_nine_double_log_den_rate": "Mellin harmonic baseline — Ninth-order doubled denominator rate eighteen",
        "harmonic_perturbed_log_den_rate": "Corollary 3 — Unconditional harmonic baseline under small-denominator perturbations",
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
    print("Four public PNT and harmonic-rate proofs are Proved and linked to the original mission.", flush=True)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("poll-jobs", "problems", "verify", "poll-proofs", "link"))
    args = parser.parse_args()
    definitions, problems = gate()
    client = api.Client()
    check_boundary(client)
    if args.mode == "poll-jobs": api.poll_jobs(client, definitions, problems)
    elif args.mode == "problems": api.publish_problems(client, definitions, problems)
    elif args.mode == "verify": api.verify(client, problems)
    elif args.mode == "poll-proofs": api.poll_proofs(client, problems)
    else: link(client, problems)


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        raise SystemExit(str(error)) from None
