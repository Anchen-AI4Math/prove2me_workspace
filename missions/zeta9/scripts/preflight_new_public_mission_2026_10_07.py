"""Focused canonical readback, without enumerating the whole mission catalog."""
from __future__ import annotations
import json
import sys
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import audit_new_mission_2026_10_07 as gate
import publish_mission_2026_10_02 as api

OUT = gate.TASK / "publication/2026-10-07/new-public-mission/focused-preflight"

def read(client, relative, path):
    value = client.call("GET", relative)
    gate.save(OUT/path, value)
    return value

def main():
    gate.docs()
    api.VERSION = "0.12.1"
    print("Authenticating with preserved official-domain and version guards",flush=True)
    client = api.Client()
    print("Reading existing canonical root, source milestones, fields and proposal metadata",flush=True)
    root = read(client,"/theorems/523f37b8-ae98-406c-a3f7-43aa8e002dd7","root.json")
    milestones = read(client,f"/missions/{api.MISSION}/milestones?limit=200&offset=0","milestones.json")["milestones"]
    proposal = read(client,f"/mission-proposals/{api.PROPOSAL}","old-proposal.json")
    fields = read(client,"/fields?q=number&limit=50&offset=0","fields.json")
    own = read(client,"/mission-proposals?limit=20&offset=0","own-proposals.json")
    assert root["status"] == "Open" and root["visibility"] == "public"
    assert any(row["id"] == "e76e77ab-38dd-426d-a533-0b37fb6dbabc" for row in fields["fields"])
    identifiers = {root.get("theorem_id") or root.get("id")}
    identifiers.update(row["theorem"]["id"] for row in milestones if row.get("theorem"))
    # Already published definition bundle handles provide actual reusable definitions.
    excluded_jobs=[]
    for folder in [gate.TASK/"formalization/platform"]+[
        gate.TASK/"formalization/platform"/name for name in ["prime-valuation","coefficient","pnt",
        "coefficient-map","coefficient-map-jet","coefficient-map-injectivity","coefficient-map-partial-fractions",
        "coefficient-map-reflection","coefficient-map-finite-sum","coefficient-map-summation",
        "coefficient-map-shift-degree","coefficient-map-aggregate","coefficient-map-telescoper",
        "coefficient-map-kernel-bridge","coefficient-map-connection","coefficient-map-matrix"]]:
        for receipt in sorted((folder/"definition-receipts").glob("*.json")):
            handle=json.loads(receipt.read_text(encoding="utf-8"))["job_id"]
            result=read(client,"/publish-jobs/"+handle, "definition-jobs/"+handle+".json")
            if result["status"].upper() == "PUBLISHED":
                identifiers.add(result["theorem_id"])
            else:
                excluded_jobs.append({"job_id":handle,"status":result["status"],
                    "included_in_new_proposal":False})
    progress=gate.TASK/"publication/2026-10-07/new-public-mission/preflight/progress-audit.json"
    if progress.exists():
        for row in json.loads(progress.read_text(encoding="utf-8"))["existing_handles"]:
            if row.get("theorem_id") and row["status"].upper()=="PUBLISHED":
                identifiers.add(row["theorem_id"])
    print(f"Reading {len(identifiers)} canonical published references",flush=True)
    def get(identifier):
        value=read(client,"/theorems/"+identifier,"canonical/"+identifier+".json")
        assert value["visibility"] == "public" and not value.get("deprecated_at"), identifier
        return {"id":identifier,"name":value["theorem_name"],"status":value["status"],
                "is_definition":value.get("is_definition"),"visibility":value["visibility"]}
    with ThreadPoolExecutor(max_workers=4) as pool:
        canonical=list(pool.map(get, sorted(identifiers)))
    gate.save(OUT/"canonical-index.json",canonical)
    summary={"checked_at":datetime.now(timezone.utc).isoformat(),"version":"0.12.1",
        "root_status":root["status"],"root_visibility":root["visibility"],
        "source_mission_id":api.MISSION,"source_milestones":len(milestones),
        "source_linked":sum(bool(x.get("theorem")) for x in milestones),
        "source_completed":sum(bool(x.get("completed")) for x in milestones),
        "old_proposal_status":proposal["status"],"canonical_items":len(canonical),
        "excluded_historical_definition_jobs":excluded_jobs,
        "remote_content_writes":0}
    gate.save(OUT/"summary.json",summary)
    print(json.dumps(summary,ensure_ascii=False),flush=True)

if __name__=="__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    main()
