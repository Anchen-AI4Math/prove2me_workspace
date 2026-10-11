"""Immutable read-only checkpoint: new proposal plus all saved zeta9 proofs."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import argparse
import json
import re
import sys

import audit_current_public_proposal_2026_10_07 as baseline
import publish_matrix_proofs_new_mission_2026_10_07 as matrix

TASK = matrix.TASK
ROOT_ID = baseline.ROOT_ID
PF = TASK / "formalization/platform/coefficient-map-numerator-pf"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("checkpoint")
    label = parser.parse_args().checkpoint
    assert re.fullmatch(r"[a-z0-9-]{1,64}", label)
    out = TASK / "formalization/platform/readback-2026-10-07" / label
    assert not out.exists(), "Use a fresh checkpoint name; preserve previous readbacks"
    out.mkdir(parents=True)

    def save(name, value):
        matrix.docs_gate.save(out / name, value)

    remote = matrix.client()
    proposal = remote.call("GET", "/mission-proposals/" + matrix.NEW_PROPOSAL)
    assert proposal["id"] == matrix.NEW_PROPOSAL and matrix.same_title(proposal["name"])
    assert proposal["visibility"] == "public"
    save("proposal.json", proposal)
    references = {row["theorem_id"] for row in proposal["items"]}
    assert len(references) == 88
    main_item = next(row for row in proposal["items"] if row["id"] == proposal["main_item_id"])
    assert main_item["theorem_id"] == ROOT_ID
    milestones = remote.call("GET", "/mission-proposals/" + matrix.NEW_PROPOSAL + "/milestones")
    save("milestones.json", milestones)
    entries = milestones["milestones"] if isinstance(milestones, dict) else milestones
    assert len(entries) == 69

    def theorem(identifier):
        value = remote.call("GET", "/theorems/" + identifier)
        assert value["visibility"] == "public" and not value.get("deprecated_at")
        save("canonical/" + identifier + ".json", value)
        return {"theorem_id": identifier, "theorem_name": value["theorem_name"], "status": value["status"],
                "visibility": value["visibility"], "referenced_by_new_proposal": identifier in references}

    with ThreadPoolExecutor(max_workers=4) as pool:
        canonical = list(pool.map(theorem, sorted(references)))
    save("proposal-canonical-index.json", canonical)
    work = []
    for label in baseline.BATCHES + ["coefficient-map-numerator-pf"]:
        folder = TASK / "formalization/platform" / label
        for path in sorted((folder / "proof-receipts").glob("*.json")):
            receipt = json.loads(path.read_text(encoding="utf-8"))
            work.append((label or "core", path.stem, receipt["submission_id"]))
    assert len(work) == len({row[2] for row in work}) == 57

    def proof(row):
        batch, name, identifier = row
        value = remote.call("GET", "/verify?submission_id=" + identifier)
        save("proofs/" + identifier + ".json", value)
        assert value["status"] == "ACCEPTED"
        return {"batch": batch, "name": name, "submission_id": identifier,
                "theorem_id": value["theorem_id"], "status": value["status"]}

    with ThreadPoolExecutor(max_workers=4) as pool:
        proofs = list(pool.map(proof, work))
    save("proof-index.json", proofs)
    extra_ids = {row["theorem_id"] for row in proofs} - references
    assert len(extra_ids) == 3
    definition_job = json.loads((PF / "definition-jobs/ZetaNine_CoefficientMapNumeratorPF.json").read_text(encoding="utf-8"))
    assert definition_job["status"] == "PUBLISHED"
    extra_ids.add(definition_job["theorem_id"])
    with ThreadPoolExecutor(max_workers=4) as pool:
        extra = list(pool.map(theorem, sorted(extra_ids)))
    save("new-global-unreferenced-index.json", extra)
    by_id = {row["theorem_id"]: row for row in canonical + extra}
    assert all(by_id[row["theorem_id"]]["status"] == "Proved" for row in proofs)
    root = by_id[ROOT_ID]
    assert root["status"] == "Open"
    result = {"checked_at": datetime.now(timezone.utc).isoformat(), "platform_version": "0.12.1",
              "new_proposal_id": matrix.NEW_PROPOSAL, "actual_name": proposal["name"],
              "visibility": proposal["visibility"], "proposal_status": proposal["status"],
              "mission_id": proposal.get("mission_id"), "references": len(references),
              "proposal_definitions": sum(r["status"] == "Definition" for r in canonical),
              "proposal_milestones": len(entries),
              "Proved_supporting_theorems_referenced": sum(r["status"] == "Proved" for r in canonical),
              "Open_supporting_theorems_referenced": sum(r["status"] == "Open" for r in canonical) - 1,
              "root_status": root["status"], "saved_complete_proof_receipts": len(proofs),
              "Accepted_complete_proof_receipts": len(proofs), "all_saved_complete_proofs_Accepted_public_Proved": True,
              "new_global_PF_Proved_not_referenced": sum(r["status"] == "Proved" for r in extra),
              "new_global_PF_Definitions_not_referenced": sum(r["status"] == "Definition" for r in extra),
              "remote_content_writes": 0, "old_mission_operations": 0, "Lean_calls": 0}
    save("progress-audit.json", result)
    print(json.dumps(result, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    main()
