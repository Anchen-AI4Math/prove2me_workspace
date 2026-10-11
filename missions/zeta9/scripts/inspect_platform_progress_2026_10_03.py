"""Read-only remote audit of the original mission and every existing batch handle."""
from __future__ import annotations

import hashlib
import json
import sys
import urllib.request
import argparse
import re
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path

import publish_mission_2026_10_02 as api

TASK = Path(__file__).resolve().parents[1]
PLATFORM = TASK / "formalization/platform"
OUT = PLATFORM / "readback-2026-10-04"
DOCS = OUT / "api-docs-v0.11.8"
EXPECTED_VERSION = "0.11.8"


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def refresh_docs():
    names = ["SKILL.md", "references/mission_captain.md", "references/missions.md",
             "references/prove.md", "references/contribute.md"]
    base = "https://raw.githubusercontent.com/prove2me/prove2me_workspace/v0.11.8/"
    receipts = []
    for name in names:
        with urllib.request.urlopen(base + name, timeout=40) as response:
            data = response.read()
        target = DOCS / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        receipts.append({"path": name, "url": base + name, "sha256": hashlib.sha256(data).hexdigest()})
    assert f'version: "{EXPECTED_VERSION}"' in (DOCS / "SKILL.md").read_text(encoding="utf-8")
    save(DOCS / "download-receipt.json", {"checked_at": datetime.now(timezone.utc).isoformat(), "version": EXPECTED_VERSION, "files": receipts})
    print("Downloaded matching official API documents:", EXPECTED_VERSION, flush=True)


def inspect():
    # This per-audit override is used only after reviewing the saved matching docs.
    assert f'version: "{EXPECTED_VERSION}"' in (DOCS / "SKILL.md").read_text(encoding="utf-8")
    api.VERSION = EXPECTED_VERSION
    client = api.Client()
    mission = client.mission()
    rows = client.call("GET", f"/missions/{api.MISSION}/milestones?limit=200&offset=0")["milestones"]
    proposal = client.call("GET", f"/mission-proposals/{api.PROPOSAL}")
    root_id = mission["main_theorem"].get("id") or mission["main_theorem"].get("theorem_id")
    assert root_id == "523f37b8-ae98-406c-a3f7-43aa8e002dd7"
    root = client.call("GET", "/theorems/" + root_id)
    save(OUT / "mission.json", mission)
    save(OUT / "milestones.json", rows)
    save(OUT / "proposal.json", proposal)
    save(OUT / "root-theorem.json", root)
    work = []
    for label, folder in (("core", PLATFORM), ("finite-prime", PLATFORM / "prime-valuation"),
                          ("coefficient", PLATFORM / "coefficient"), ("pnt", PLATFORM / "pnt"),
                          ("coefficient-map", PLATFORM / "coefficient-map"),
                          ("coefficient-map-jet", PLATFORM / "coefficient-map-jet"),
                          ("coefficient-map-injectivity", PLATFORM / "coefficient-map-injectivity"),
                          ("coefficient-map-partial-fractions", PLATFORM / "coefficient-map-partial-fractions"),
                          ("coefficient-map-reflection", PLATFORM / "coefficient-map-reflection"),
                          ("coefficient-map-finite-sum", PLATFORM / "coefficient-map-finite-sum"),
                          ("coefficient-map-summation", PLATFORM / "coefficient-map-summation"),
                          ("coefficient-map-shift-degree", PLATFORM / "coefficient-map-shift-degree"),
                          ("coefficient-map-aggregate", PLATFORM / "coefficient-map-aggregate"),
                          ("coefficient-map-telescoper", PLATFORM / "coefficient-map-telescoper"),
                          ("coefficient-map-kernel-bridge", PLATFORM / "coefficient-map-kernel-bridge"),
                          ("coefficient-map-connection", PLATFORM / "coefficient-map-connection"),
                          ("coefficient-map-matrix", PLATFORM / "coefficient-map-matrix")):
        for kind in ("definition", "problem", "proof"):
            for receipt in sorted((folder / (kind + "-receipts")).glob("*.json")):
                value = json.loads(receipt.read_text(encoding="utf-8"))
                identifier = value["submission_id" if kind == "proof" else "job_id"]
                endpoint = "/verify?submission_id=" + identifier if kind == "proof" else "/publish-jobs/" + identifier
                work.append((label, kind, receipt.stem, identifier, endpoint))

    def poll(item):
        label, kind, name, identifier, endpoint = item
        result = client.call("GET", endpoint)
        # Shorten only snapshot directory labels to keep Windows paths readable.
        # Actual theorem names, handles and returned evidence remain unchanged.
        folder_label = {"coefficient-map-partial-fractions": "pf",
                        "coefficient-map-reflection": "reflection",
                        "coefficient-map-finite-sum": "finite-sum",
                        "coefficient-map-summation": "summation",
                        "coefficient-map-shift-degree": "shift",
                        "coefficient-map-aggregate": "aggregate",
                        "coefficient-map-telescoper": "telescoper",
                        "coefficient-map-kernel-bridge": "kernel",
                        "coefficient-map-connection": "connection",
                        "coefficient-map-matrix": "matrix"}.get(label, label)
        save(OUT / folder_label / (kind + "-results") / (name + ".json"), result)
        theorem = None
        if kind == "problem" and result.get("theorem_id"):
            theorem = client.call("GET", "/theorems/" + result["theorem_id"])
            save(OUT / folder_label / "theorem-readbacks" / (name + ".json"), theorem)
        return {"batch": label, "kind": kind, "name": name, "handle": identifier,
                "status": result["status"], "theorem_id": result.get("theorem_id"),
                "theorem_status": theorem.get("status") if theorem else None,
                "visibility": theorem.get("visibility") if theorem else None,
                "error_message": result.get("error_message", "")}

    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(poll, work))
    linked = {row["theorem"]["id"] for row in rows if row.get("theorem")}
    for result in results:
        result["linked_to_mission"] = result.get("theorem_id") in linked
    summary = {"checked_at": datetime.now(timezone.utc).isoformat(), "platform_version": EXPECTED_VERSION,
        "mission_id": api.MISSION, "mission_visibility": mission["visibility"],
        "release_requested_at": mission.get("release_requested_at"), "proposal_status": proposal["status"],
        "root_status": root["status"], "root_visibility": root["visibility"],
        "milestones": len(rows), "linked_theorems": len(linked),
        "completed_milestones": sum(bool(row.get("completed")) for row in rows),
        "existing_handles": results,
        "pnt_has_submission_receipts": any(r["batch"] == "pnt" for r in results),
        "remote_writes_performed": False}
    save(OUT / "progress-audit.json", summary)
    print(f"Read-only audit: {len(rows)} milestones, {len(linked)} theorem links, "
          f"{summary['completed_milestones']} completed; root {root['status']}, "
          f"mission {mission['visibility']}, proposal {proposal['status']}.", flush=True)
    proofs = [r for r in results if r["kind"] == "proof"]
    print(f"Existing proof submissions: {len(proofs)}; Accepted: "
          f"{sum(r['status'] == 'ACCEPTED' for r in proofs)}. "
          f"Snapshot: {OUT.relative_to(TASK).as_posix()}/progress-audit.json", flush=True)


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", nargs="?", choices=("docs", "audit"), default="audit")
    parser.add_argument("--snapshot", help="New named snapshot directory; preserve the pre-work audit.")
    args = parser.parse_args()
    if args.mode == "docs":
        assert args.snapshot is None
        refresh_docs()
    else:
        if args.snapshot:
            assert re.fullmatch(r"[a-z0-9][a-z0-9-]{0,63}", args.snapshot)
            OUT = OUT / args.snapshot
            assert not (OUT / "progress-audit.json").exists(), "Snapshot already exists; choose a new label."
        inspect()
