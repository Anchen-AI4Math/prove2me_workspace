"""Publish complete reviewed Matrix proofs; only associate with the NEW proposal.

No live-mission/link mutation, no self-audit or proposal launch, no Lean calls.
An uncertain proof POST is journaled and cannot be silently resubmitted.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import sys
import unicodedata
from datetime import datetime, timezone
from pathlib import Path
import audit_new_mission_2026_10_07 as docs_gate
import publish_mission_2026_10_02 as official
import publish_coefficient_map_matrix_2026_10_04 as matrix

TASK=docs_gate.TASK
OUT=TASK/"formalization/platform/coefficient-map-matrix/proofs-for-new-mission-2026-10-07"
NEW_PROPOSAL="19653cff-d481-498a-a717-10630d1ca1b7"
NEW_NAME="Irrationality of ζ（9）"
OLD_MISSION="8195d8fe-059f-4515-92b4-57b585e2bac6"
OLD_PROPOSAL="06faf23f-00c2-4edf-92ab-1212cdb7d7d6"
common=matrix.common
api=common.api

def save(name,value):docs_gate.save(OUT/name,value)
def load(name):return json.loads((OUT/name).read_text(encoding="utf-8"))
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def same_title(value):return unicodedata.normalize("NFKC",value)==unicodedata.normalize("NFKC",NEW_NAME)

class ProofOnlyClient(official.Client):
    def call(self,method,path,data=None,authenticated=True):
        assert OLD_MISSION not in path and OLD_PROPOSAL not in path
        assert method=="GET" or (method=="POST" and path=="/agent/refresh" and not authenticated)
        return super().call(method,path,data,authenticated)

def client():
    docs_gate.docs()
    official.VERSION="0.12.1"
    target=json.loads((TASK/"publication/2026-10-07/new-public-mission/CURRENT_PLATFORM_TARGET.json").read_text(encoding="utf-8"))
    assert target["proposal_id"]==NEW_PROPOSAL and same_title(target["name"]) and target["visibility"]=="public"
    return ProofOnlyClient()

def prepare():
    pin_path=common.OUT/"independent/Root-reviewed-publication-pin.json"
    pin=json.loads(pin_path.read_text(encoding="utf-8"))
    assert pin["Root_rehashed_all_independent_bindings"] is True
    assert pin["source_sha256"]==common.SOURCE and pin["author_sha256"]==common.EXPECTED_AUTHOR_HASH
    assert pin["independent_report_sha256"]=="d86385c79cf9b56457323f8d8fcf9d6d15cff9336cd8b998a6c6ee9b8dbb7110"
    common.EXPECTED_INDEPENDENT_HASH=pin["independent_report_sha256"]
    definitions,problems=common.gate()
    save("prepared-proof-plan.json",{"new_proposal_id":NEW_PROPOSAL,"name":NEW_NAME,
        "source_sha256":common.SOURCE,"author_checks":33,"author_bound_files_rehashed":1543,
        "independent_checks":49,"independent_bound_files_rehashed":3488,
        "independent_report_sha256":pin["independent_report_sha256"],"definitions":definitions,"problems":problems,
        "proof_inputs":[{"root_relative":p["local_solution"],"sha256":sha(api.WORKSPACE/p["local_solution"]),
                         "bytes":(api.WORKSPACE/p["local_solution"]).stat().st_size} for p in problems]})
    print("Exact Matrix proof inputs and all author/independent bindings rechecked; no Lean calls",flush=True)
    return definitions,problems

def submit():
    definitions,problems=prepare()
    remote=client()
    detail=remote.call("GET","/mission-proposals/"+NEW_PROPOSAL)
    assert detail["id"]==NEW_PROPOSAL and same_title(detail["name"]) and detail["visibility"]=="public"
    save("proposal-before-proof-submissions.json",detail)
    api.poll_jobs(remote,definitions,problems)
    existing={item["theorem_id"] for item in detail["items"]}
    state=load("proof-post-journal.json") if (OUT/"proof-post-journal.json").exists() else {"new_proposal_id":NEW_PROPOSAL,"attempts":[]}
    unresolved=[]
    for problem in problems:
        name=api.slug(problem["theorem_name"])
        receipt_path=common.OUT/f"proof-receipts/{name}.json"
        if receipt_path.exists():
            print("Existing Matrix proof receipt:",name,flush=True)
            continue
        if any(r["slug"]==name for r in state["attempts"]):
            unresolved.append(name)
            print("Unreceipted previous POST; inspect this target's history before any retry:",name,flush=True)
            continue
        job=api.read(f"problem-jobs/{name}.json")
        assert job["status"]=="PUBLISHED" and job["theorem_id"] in existing
        row={"slug":name,"theorem_id":job["theorem_id"],"intended_at":datetime.now(timezone.utc).isoformat(),
            "source_sha256":sha(api.WORKSPACE/problem["local_solution"]),"receipt_saved":False,
            "new_proposal_reference_verified":True,"old_mission_write":False}
        state["attempts"].append(row);save("proof-post-journal.json",state)
        try:
            api.verify(remote,[problem])
        except Exception:
            row["remote_outcome_uncertain_or_error"]=True
            save("proof-post-journal.json",state)
            raise
        receipt=json.loads(receipt_path.read_text(encoding="utf-8"))
        row["receipt_saved"]=True;row["submission_id"]=receipt["submission_id"]
        save("proof-post-journal.json",state)
    assert not unresolved,"Resolve journaled unknown POSTs from the documented submission history; do not duplicate them"
    api.poll_proofs(remote,problems)

def poll():
    plan=load("prepared-proof-plan.json")
    api.OUT=common.OUT
    api.poll_proofs(client(),plan["problems"])

def audit():
    plan=load("prepared-proof-plan.json")
    api.OUT=common.OUT
    remote=client()
    details=remote.call("GET","/mission-proposals/"+NEW_PROPOSAL)
    assert details["id"]==NEW_PROPOSAL and same_title(details["name"]) and details["visibility"]=="public"
    references={row["theorem_id"] for row in details["items"]}
    rows=[]
    for problem in plan["problems"]:
        slug=api.slug(problem["theorem_name"])
        receipt=api.read(f"proof-receipts/{slug}.json")
        verdict=remote.call("GET","/verify?submission_id="+receipt["submission_id"])
        api.save(f"proof-verdicts/{slug}.json",verdict)
        identifier=api.read(f"problem-jobs/{slug}.json")["theorem_id"]
        theorem=remote.call("GET","/theorems/"+identifier)
        save(f"verdicts/{slug}.json",verdict);save(f"proved-readbacks/{slug}.json",theorem)
        assert verdict["status"]=="ACCEPTED" and theorem["status"]=="Proved" and theorem["visibility"]=="public"
        assert theorem["mathlib_rev"]==api.ENV and theorem["formal_statement"].strip()==problem["formal_statement"].strip()
        assert identifier in references
        rows.append({"theorem_id":identifier,"theorem_name":theorem["theorem_name"],"status":"Proved","visibility":"public",
                     "submission_id":receipt["submission_id"],"proof_status":verdict["status"],"referenced_by_new_proposal":True})
    root=remote.call("GET","/theorems/523f37b8-ae98-406c-a3f7-43aa8e002dd7")
    assert root["status"]=="Open"
    save("proposal-current.json",details);save("root-current.json",root)
    save("publication-audit.json",{"checked_at":datetime.now(timezone.utc).isoformat(),"new_proposal_id":NEW_PROPOSAL,
        "requested_name":NEW_NAME,"actual_proposal_name":details["name"],"proposal_visibility":details["visibility"],"proposal_status":details["status"],
        "new_complete_proofs":rows,"all_three_Accepted_public_Proved_and_referenced":True,"old_mission_writes":0,
        "root_status":"Open","native_or_Root_compiler_calls":0,
        "scope":"even n>=2 actual matrix, rational selected coordinates, exact HasSum and absolute summability",
        "integer_polynomial_preimage_or_height_bound_proved":False,"five_output_parameter_transport_proved":False})
    print("Three complete Matrix proofs are Accepted/public Proved and referenced by the NEW public proposal; root remains Open",flush=True)

if __name__=="__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    parser=argparse.ArgumentParser();parser.add_argument("mode",choices=["prepare","submit","poll","audit"])
    mode=parser.parse_args().mode
    if mode=="prepare":prepare()
    elif mode=="submit":submit()
    elif mode=="poll":poll()
    else:audit()
