"""Create the specifically authorized NEW public proposal using published references.

No writes to the old mission; no undocumented submit/self-audit endpoints.
Every mutation is preceded by a journal entry and followed by an authoritative readback.
An interrupted create is recovered from the documented own-proposal listing.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
import audit_new_mission_2026_10_07 as gate
import publish_mission_2026_10_02 as api

OUT=gate.TASK/"publication/2026-10-07/new-public-mission"
PRE=OUT/"focused-preflight"
ROOT_ID="523f37b8-ae98-406c-a3f7-43aa8e002dd7"
NAME="Irrationality of ζ（9）"
ORIGINAL_NAME="Irrationality of ζ(9): coefficient map and weighted lattice"
OLD_MISSION="8195d8fe-059f-4515-92b4-57b585e2bac6"
OLD_PROPOSAL="06faf23f-00c2-4edf-92ab-1212cdb7d7d6"

def load(path): return json.loads(path.read_text(encoding="utf-8"))
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def save(path,value): gate.save(path,value)

def prepare():
    checkpoint=load(PRE/"summary.json")
    assert checkpoint["version"]=="0.12.1" and checkpoint["canonical_items"]==88
    index=load(PRE/"canonical-index.json")
    values={r["id"]:load(PRE/"canonical"/(r["id"]+".json")) for r in index}
    assert len(values)==88 and values[ROOT_ID]["status"]=="Open"
    assert all(v["visibility"]=="public" and not v.get("deprecated_at") for v in values.values())
    definitions={k:v for k,v in values.items() if v["status"]=="Definition"}
    assert len(definitions)==18
    modules={"Definitions.Def_"+v["theorem_name"].replace(".","_"):k for k,v in definitions.items()}
    ordered=[];remaining=set(definitions)
    while remaining:
        available=[]
        for k in remaining:
            imports=re.findall(r"(?m)^import\s+(Definitions\.Def_[A-Za-z0-9_]+)",definitions[k]["definition"])
            if not any(modules.get(m) in remaining for m in imports): available.append(k)
        assert available,"Definition import cycle"
        for k in sorted(available,key=lambda k:definitions[k]["theorem_name"]):
            ordered.append(k);remaining.remove(k)
    milestones=[]
    for row in load(PRE/"milestones.json")["milestones"]:
        if not row.get("theorem"): continue
        k=row["theorem"]["id"]
        assert k!=ROOT_ID and values[k]["status"]!="Definition"
        description=(row["milestone_description"].replace("existing open theorem","existing published theorem")
            .replace("genuine positive weighted sequence","genuine weighted sequence on positive natural arguments")
            .replace("genuine positive sequence","genuine sequence on positive natural arguments"))
        if k=="60c1cf49-6b01-448c-b38a-88dc2fcb8ba0":
            description=("There is a real c>0 such that, for every sufficiently large natural n, there exist integers b,a with "
              "0 < |b+a Re(riemannZeta(9))| < exp(-c n). The published statement places no bound on b or a and does not "
              "require them to come from the coefficient-map or weighted-lattice construction. The index n labels only the "
              "error threshold. Producing these forms with the actual construction and its denominator, height and "
              "nonvanishing controls is a separate concrete obligation; this unrestricted existence statement is not "
              "claimed to be strictly stronger than irrationality.")
        elif k=="691b1665-f122-47f7-a3e4-2c28a06055f2":
            description=("There is a real c>0 such that, for every sufficiently large natural n, there exist integers "
              "b1,a1,b2,a2 with b1*a2 != b2*a1 and both |bi+ai Re(riemannZeta(9))| < exp(-c n). The determinant "
              "condition requires independent integer coefficient pairs. No coefficient-height or prescribed-lattice "
              "condition occurs in the published statement. Its unrestricted existence formulation must be distinguished "
              "from constructing the actual weighted-lattice outputs with the required arithmetic and analytic controls; "
              "it is not claimed to be strictly stronger than the irrationality goal.")
        milestones.append({"theorem_id":k,"milestone_title":row["title"],"milestone_description":description,
                           "source_milestone_id":row["id"]})
    matrix={
      "3e15df20-1023-4b72-95ab-1ad07c34b3e5":("Z9.F — Actual five-output matrix is nonsingular for even n≥2",
        "For every even natural number n≥2, the matrix whose monomial rows are the actual constant/rho3/rho5/rho7/rho9 coefficient outputs has nonzero determinant. This is the actual rational-function coefficient matrix, with the specified row convention; it does not assert the result for odd n or n=0."),
      "134e564c-4327-43b0-9ecd-e7d08fa133ec":("Z9.F — Selected rational quartic coefficients equal (b,a) S F inverse",
        "For even n≥2 and integer target values b,a, the coefficients of the selected rational quartic with actual output (b,0,0,0,a) are exactly (b,a) times the two-row selection matrix times the actual F inverse. The preimage is rational; neither integral polynomial coefficients nor a height or denominator bound is asserted."),
      "bb7477e4-5539-4015-b8cf-9bad57e1c8a0":("Z9.F — Selected actual rational function has absolute sum b+a ζ(9)",
        "For even n≥2 and integers b,a, the genuine weighted rational function belonging to the selected rational quartic is absolutely summable on positive natural arguments and has sum b+a times the real part of riemannZeta at 9. The target preserves the exact chosen multiplier and output order; it does not claim nonvanishing or integer polynomial coefficients.")}
    for k,(title,description) in matrix.items():
        assert values[k]["status"]=="Open"
        milestones.append({"theorem_id":k,"milestone_title":title,"milestone_description":description,
                           "source":"formalization/platform/coefficient-map-matrix"})
    assert len(milestones)==69 and len({r["theorem_id"] for r in milestones})==69
    ordered += [ROOT_ID]+[r["theorem_id"] for r in milestones]
    assert len(ordered)==len(set(ordered))==88 and set(ordered)==set(values)
    description=(OUT/"content/mission-introduction.md").read_text(encoding="utf-8")
    assert len(description.split())>=800 and description.count("\n## ")==6
    plan={"name":NAME,"description":description,"mission_type":"OpenProblem",
          "field_ids":["e76e77ab-38dd-426d-a533-0b37fb6dbabc"],
          "env":values[ROOT_ID]["mathlib_rev"],"visibility":"public","root_theorem_id":ROOT_ID,
          "reference_order":ordered,"milestones":milestones,
          "counts":{"definitions":18,"goal":1,"milestones":69,"currently_proved_supporting_theorems":64},
          "bindings":[{"path":str(p.relative_to(gate.TASK)).replace("\\","/"),"sha256":digest(p),"bytes":p.stat().st_size}
                      for p in [PRE/"summary.json",PRE/"canonical-index.json",OUT/"content/mission-introduction.md"]+
                      [PRE/"canonical"/(k+".json") for k in ordered]]}
    save(OUT/"proposal-plan.json",plan)
    print("Reviewable NEW public proposal plan: 18 definitions, 69 milestones, canonical Open goal",flush=True)

def own_proposals(client):
    rows=[]
    for offset in range(0,10000,20):
        page=client.call("GET",f"/mission-proposals?limit=20&offset={offset}")
        batch=page["proposals"];rows.extend(batch)
        if len(batch)<20: return rows
    raise RuntimeError("Own-proposal pagination did not terminate")

def publish():
    gate.docs();api.VERSION="0.12.1"
    plan=load(OUT/"proposal-plan.json")
    assert plan["visibility"]=="public" and plan["name"]==NAME
    for row in plan["bindings"]:
        p=gate.TASK/row["path"]
        assert p.stat().st_size==row["bytes"] and digest(p)==row["sha256"],row["path"]
    state_path=OUT/"publication-state.json"
    state=load(state_path) if state_path.exists() else {"authorization":"User requested a NEW mission proposal, directly public, on 2026-10-07", "old_mission_writes":0,"journal":[]}
    client=api.Client()
    def write(method,path,body,label):
        assert OLD_MISSION not in path and OLD_PROPOSAL not in path
        state["journal"].append({"label":label,"method":method,"path":path,"intended_at":datetime.now(timezone.utc).isoformat(),
            "body_sha256":hashlib.sha256(json.dumps(body,ensure_ascii=False,sort_keys=True).encode()).hexdigest(),"response_saved":False})
        save(state_path,state)
        result=client.call(method,path,body)
        save(OUT/"responses"/(str(len(state["journal"])).zfill(3)+".json"),result)
        state["journal"][-1]["response_saved"]=True
        save(state_path,state)
        return result
    identifier=state.get("proposal_id")
    if not identifier:
        matches=[r for r in own_proposals(client) if r["name"]==NAME]
        assert len(matches)<=1,"Ambiguous proposal recovery"
        if matches:
            identifier=matches[0]["id"]
        else:
            body={k:plan[k] for k in ["name","description","mission_type","field_ids","env","visibility"]}
            result=write("POST","/mission-proposals",body,"create-new-public-proposal")
            identifier=result["id"]
        assert identifier!=OLD_PROPOSAL
        state["proposal_id"]=identifier;save(state_path,state)
    endpoint="/mission-proposals/"+identifier
    detail=client.call("GET",endpoint)
    if detail["name"] != NAME:
        assert detail["name"]==ORIGINAL_NAME and identifier==state["proposal_id"]
        assert detail["status"]=="Draft" and detail["visibility"]=="public"
        write("PATCH",endpoint,{"name":NAME},"rename-as-explicitly-requested-by-user")
        renamed=client.call("GET",endpoint)
        assert renamed["name"]==NAME and renamed["visibility"]=="public"
        save(OUT/"rename-readback.json",{"proposal_id":identifier,"before":detail["name"],
            "after":renamed["name"],"visibility":renamed["visibility"],"status":renamed["status"],
            "reference_count":len(renamed["items"]),"readback_verified":True})
        detail=renamed
    assert detail["name"]==NAME and detail["status"]=="Draft" and detail["visibility"]=="public"
    item_ids={r["theorem_id"]:r["id"] for r in detail["items"]}
    assert set(item_ids)<=set(plan["reference_order"]),"Unplanned proposal item"
    for number,k in enumerate(plan["reference_order"],1):
        if k in item_ids: continue
        result=write("POST",endpoint+"/items",{"kind":"reference","theorem_id":k},"add-reference-"+k)
        item_ids[k]=result["id"]
        state["item_ids"]=item_ids;save(state_path,state)
        if number%10==0: print(f"Saved published references: {number}/88",flush=True)
    metadata={k:plan[k] for k in ["description","mission_type","field_ids","visibility"]}
    metadata.update({"main_item_id":item_ids[ROOT_ID],"item_order":[item_ids[k] for k in plan["reference_order"]]})
    write("PATCH",endpoint,metadata,"set-public-goal-and-full-dependency-order")
    # Re-read on every resumed run, rather than assuming a preceding POST committed.
    current=client.call("GET",endpoint+"/milestones")
    entries=current["milestones"] if isinstance(current,dict) else current
    existing={r["item_id"]:{**r,"milestone_title":r.get("milestone_title",r.get("title"))} for r in entries}
    for number,row in enumerate(plan["milestones"],1):
        body={"item_id":item_ids[row["theorem_id"]],"milestone_title":row["milestone_title"],"milestone_description":row["milestone_description"]}
        old=existing.get(body["item_id"])
        if old and all(old.get(k)==v for k,v in body.items()): continue
        write("POST",endpoint+"/milestones",body,"milestone-"+row["theorem_id"])
        if number%10==0: print(f"Saved faithful milestones: {number}/69",flush=True)
    final=client.call("GET",endpoint)
    final_milestones=client.call("GET",endpoint+"/milestones")
    save(OUT/"proposal-readback.json",final);save(OUT/"milestones-readback.json",final_milestones)
    assert final["name"]==NAME and final["visibility"]=="public" and final["status"]=="Draft" and final["description"]==plan["description"]
    assert final["main_item_id"]==item_ids[ROOT_ID] and final["item_order"]==metadata["item_order"]
    assert len(final["items"])==88 and all(r["kind"]=="reference" for r in final["items"])
    final_entries=final_milestones["milestones"] if isinstance(final_milestones,dict) else final_milestones
    assert len(final_entries)==69
    by_item={r["item_id"]:{**r,"milestone_title":r.get("milestone_title",r.get("title"))} for r in final_entries}
    for row in plan["milestones"]:
        got=by_item[item_ids[row["theorem_id"]]]
        assert got["milestone_title"]==row["milestone_title"] and got["milestone_description"]==row["milestone_description"]
    receipt={"checked_at":datetime.now(timezone.utc).isoformat(),"proposal_id":identifier,"name":NAME,
        "visibility":"public","status":final["status"],"goal_theorem_id":ROOT_ID,"references":88,"definitions":18,
        "milestones":69,"source_supporting_theorems_already_proved":64,"readback_verified":True,
        "old_mission_writes":0,"draft_theorem_declarations_created":0,"public_catalog_live":False,
        "remaining_launch_step":"Human confirms reference items and clicks Submit Proposal in the web app; public missions then require moderator approval",
        "plan_sha256":digest(OUT/"proposal-plan.json")}
    save(OUT/"proposal-receipt.json",receipt)
    print(json.dumps(receipt,ensure_ascii=False),flush=True)

if __name__=="__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    parser=argparse.ArgumentParser();parser.add_argument("mode",choices=["prepare","publish"])
    args=parser.parse_args()
    if args.mode=="prepare": prepare()
    else: publish()
