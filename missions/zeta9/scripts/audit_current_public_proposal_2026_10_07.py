"""Read only the current proposal, its canonical theorem references and saved proofs."""
from __future__ import annotations
import json
import sys
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import publish_matrix_proofs_new_mission_2026_10_07 as matrix

TASK=matrix.TASK
OUT=TASK/"formalization/platform/readback-2026-10-07/new-public-post-matrix"
ROOT_ID="523f37b8-ae98-406c-a3f7-43aa8e002dd7"
BATCHES=["", "prime-valuation","coefficient","pnt","coefficient-map","coefficient-map-jet",
    "coefficient-map-injectivity","coefficient-map-partial-fractions","coefficient-map-reflection",
    "coefficient-map-finite-sum","coefficient-map-summation","coefficient-map-shift-degree",
    "coefficient-map-aggregate","coefficient-map-telescoper","coefficient-map-kernel-bridge",
    "coefficient-map-connection","coefficient-map-matrix"]

def save(relative,value):matrix.docs_gate.save(OUT/relative,value)

def main():
    assert not (OUT/"progress-audit.json").exists(),"Keep this immutable snapshot; create a new audit name for another checkpoint"
    client=matrix.client()
    proposal=client.call("GET","/mission-proposals/"+matrix.NEW_PROPOSAL)
    save("proposal.json",proposal)
    assert proposal["id"]==matrix.NEW_PROPOSAL and matrix.same_title(proposal["name"])
    assert proposal["visibility"]=="public"
    references={r["theorem_id"] for r in proposal["items"]}
    assert len(references)==88
    main_items=[r for r in proposal["items"] if r["id"]==proposal["main_item_id"]]
    assert len(main_items)==1 and main_items[0]["theorem_id"]==ROOT_ID
    milestones=client.call("GET","/mission-proposals/"+matrix.NEW_PROPOSAL+"/milestones")
    save("milestones.json",milestones)
    entries=milestones["milestones"] if isinstance(milestones,dict) else milestones
    assert len(entries)==69
    def theorem(identifier):
        value=client.call("GET","/theorems/"+identifier)
        save("canonical/"+identifier+".json",value)
        assert value["visibility"]=="public" and not value.get("deprecated_at")
        return {"theorem_id":identifier,"theorem_name":value["theorem_name"],"status":value["status"],"visibility":value["visibility"]}
    with ThreadPoolExecutor(max_workers=4) as pool:
        canonical=list(pool.map(theorem,sorted(references)))
    save("canonical-index.json",canonical)
    root=next(r for r in canonical if r["theorem_id"]==ROOT_ID)
    assert root["status"]=="Open"
    work=[]
    for label in BATCHES:
        folder=TASK/"formalization/platform"/label
        for path in sorted((folder/"proof-receipts").glob("*.json")):
            receipt=json.loads(path.read_text(encoding="utf-8"))
            work.append((label or "core",path.stem,receipt["submission_id"]))
    assert len(work)==54
    def proof(item):
        label,name,identifier=item
        value=client.call("GET","/verify?submission_id="+identifier)
        save("proofs/"+identifier+".json",value)
        return {"batch":label,"name":name,"submission_id":identifier,"status":value["status"]}
    with ThreadPoolExecutor(max_workers=4) as pool:
        proofs=list(pool.map(proof,work))
    save("proof-index.json",proofs)
    assert all(row["status"]=="ACCEPTED" for row in proofs)
    assert sum(r["status"]=="Definition" for r in canonical)==18
    assert sum(r["status"]=="Proved" for r in canonical)==67
    assert sum(r["status"]=="Open" for r in canonical)==3
    result={"checked_at":datetime.now(timezone.utc).isoformat(),"platform_version":"0.12.1",
        "new_proposal_id":matrix.NEW_PROPOSAL,"actual_name":proposal["name"],"visibility":proposal["visibility"],
        "proposal_status":proposal["status"],"mission_id":proposal.get("mission_id"),"references":88,
        "definitions":18,"milestones":69,"Proved_supporting_theorems":67,"Open_supporting_theorems":2,
        "root_status":"Open","existing_complete_proof_receipts":54,"Accepted_complete_proof_receipts":54,
        "all_saved_complete_proof_receipts_Accepted":True,"all_references_public_non_deprecated":True,
        "remote_content_writes":0,"old_mission_operations":0,"scope":"current new public proposal only"}
    save("progress-audit.json",result)
    print(json.dumps(result,ensure_ascii=False),flush=True)

if __name__=="__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    main()
