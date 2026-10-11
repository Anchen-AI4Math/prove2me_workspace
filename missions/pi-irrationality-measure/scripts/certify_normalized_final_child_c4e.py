"""Strict read-only consumer for the already compiled ap6/c4 child."""
from __future__ import annotations
import argparse, hashlib, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import validate_namespace_context_providers as context

STAGE = ROOT / "verification/ap6/c4e"
THEOREM = "OAI.PiExponent.exists_normalized_successive_approximations"
MODULE = "Theorems.Thm_OAI_PiExponent_exists_normalized_successive_approximations"
N3 = ROOT / "verification/ap5/n3"
STD3 = {"propext", "Classical.choice", "Quot.sound"}

def need(x, msg):
    if not x: raise ValueError(msg)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_text(encoding="utf-8"))
def dump(p, x): Path(p).write_text(json.dumps(x, indent=2, sort_keys=True)+"\n", encoding="utf-8")
def task_rel(p): return "missions/pi-irrationality-measure/" + Path(p).resolve().relative_to(ROOT).as_posix()

def typed(path, name):
    rows=read(path); need(isinstance(rows,list) and len(rows)==1,"expected one modern type row")
    r=rows[0]; need(set(r)=={"levelParams","name","prettyType","type","value"} and r["name"]==name and r["value"] is None,
        "modern type-only row schema/identity differs")
    return r

def norm(r):
    mp={n:"u"+str(i) for i,n in enumerate(r["levelParams"])}
    def walk(x):
        if isinstance(x,list):
            if len(x)==2 and x[0]=="param" and x[1] in mp: return ["param",mp[x[1]]]
            return [walk(y) for y in x]
        return x
    return [len(r["levelParams"]),walk(r["type"])]

def refs(path, owner_kind, owner_module):
    d=read(path); need(set(d)=={"schemaVersion","probeMainModule","rows"} and d["schemaVersion"]==1 and len(d["rows"])==1,
        "modern proof-reference document schema differs")
    r=d["rows"][0]; need(set(r)=={"name","kind","closedType","closedValue","typeRefs","valueRefs","axioms","owner"},
        "modern proof-reference row schema differs")
    need(r["name"]==THEOREM and r["kind"]=="theorem" and r["closedType"] is True and r["closedValue"] is True,
        "proof-reference theorem identity/closure differs")
    need(set(r["axioms"]).issubset(STD3),"proof exceeds Std3")
    own=r["owner"]; need(own["kind"]==owner_kind and own["module"]==owner_module,"actual first-search owner differs")
    if owner_kind=="ImportedModule": need(set(own)=={"kind","module","index"} and type(own["index"]) is int,"imported owner schema differs")
    else: need(set(own)=={"kind","module"},"own owner schema differs")
    need(r["typeRefs"]==sorted(set(r["typeRefs"])) and r["valueRefs"]==sorted(set(r["valueRefs"])),"reference lists not canonical")
    return d,r

def summary(pf):
    d=pf["data"]
    out={"source":d["source"],"manifest":d["manifest"],"mode":d["mode"],
        "module":d["actual_module_identity"],"seconds":d["seconds"],"log":d["log"],
        "log_sha256":d["log_sha256"],"runtime_sha256":d["runtime_sha256"],
        "dependency_oleans":d["dependency_oleans"],"success":d["success"]}
    s=pf["summary"]
    need(s["path"]==pf["record"] and s["sha256"]==pf["record_sha256"] and s["seconds"]==out["seconds"]
         and s["log"]==out["log"] and s["log_sha256"]==out["log_sha256"],
         "context.record summary does not match full modern record")
    return out

def certify():
    prep=read(STAGE/"preparation.json"); bind=read(STAGE/"postcompile-bindings.json")
    need(prep["parent_validation_sha256"]==sha(N3/"n3-validation.json"),"n3 certificate drift")
    publication=read(N3/"publication-draft/publication.json")
    need(publication["last_verify_verdict"]["body"]["status"]=="ACCEPTED" and publication["target_readback"]["body"]["status"]=="Proved",
        "OwnedAccepted parent replay failed")
    source=STAGE/"Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean"
    pfs={
      "theorem":context.record(source,STAGE/"child-module.json","emit-olean",MODULE,STAGE),
      "source":context.record(STAGE/"SourceSnapshot.lean",STAGE/"source-snapshot.json","modecheck","SourceSnapshot",STAGE),
      "child":context.record(STAGE/"ChildSnapshot.lean",STAGE/"child-snapshot.json","modecheck","ChildSnapshot",STAGE)}
    for n,pf in pfs.items():
        need(pf["data"]["success"] is True and pf["data"]["seconds"]<=300 and pf["data"]["runtime_unchanged"] is True,
            n+" actual preflight invalid")
        summary(pf)
    actual_source=typed(STAGE/"source-type.json",THEOREM); actual_child=typed(STAGE/"child-type.json",THEOREM)
    parent_source=typed(N3/"original-type.json",THEOREM); parent_solution=typed(N3/"generated-type.json","solution")
    need(len({json.dumps(norm(x),sort_keys=True) for x in (actual_source,actual_child,parent_source,parent_solution)})==1,
        "fresh source/child type differs from parent source/solution")
    sd,sr=refs(STAGE/"source-proof-references.json","OwnModule","SourceSnapshot")
    cd,cr=refs(STAGE/"child-proof-references.json","ImportedModule",MODULE)
    parent_refs=read(N3/"proof-references.json")["rows"]
    need(len(parent_refs)==1 and parent_refs[0]["name"]=="solution","parent modern proof row differs")
    expected=parent_refs[0]["valueRefs"]
    need(sr["valueRefs"]==expected and cr["valueRefs"]==expected,"fresh proof refs differ from parent solution")
    oai=[x for x in expected if x.startswith("OAI.PiExponent.")]
    need(oai==["OAI.PiExponent.exists_normalized_selection_of_selector","OAI.PiExponent.exists_successive_approximations"],
        "parent proof does not reference exactly the two actual proved children")
    outputs=[STAGE/x for x in ("source-type.json","source-proof-references.json","child-type.json","child-proof-references.json")]
    cert={"schema_version":1,"artifact_kind":"ap6-c4e-normalized-final-actual-child-validation","validated":True,
      "theorem_name":THEOREM,"module":MODULE,"child_source":task_rel(source),"child_source_sha256":sha(source),
      "child_olean":bind["child_olean"],"child_olean_sha256":bind["child_olean_sha256"],
      "parent_validation":task_rel(N3/"n3-validation.json"),"parent_validation_sha256":sha(N3/"n3-validation.json"),
      "own_accepted_record":task_rel(N3/"publication-draft/publication.json"),"own_accepted_record_sha256":sha(N3/"publication-draft/publication.json"),
      "OwnedAccepted_parent_replay":True,"theorem_id":publication["target_readback"]["body"]["theorem_id"],
      "submission_id":publication["last_verify_verdict"]["body"]["id"],
      "kernel_type_equal_to_parent_source_and_solution":True,"actual_proved_child_value_refs":oai,
      "source_owner":sr["owner"],"child_owner":cr["owner"],"Std3_only":True,
      "output_json_sha256":{task_rel(p):sha(p) for p in outputs},
      "implementation_hashes":{task_rel(Path(__file__)):sha(Path(__file__)),task_rel(ROOT/"scripts/stage_normalized_final_child_c4e.py"):sha(ROOT/"scripts/stage_normalized_final_child_c4e.py")},
      "preflights":{n:{"record":pf["record"],"record_sha256":pf["record_sha256"],
          "full_context_record":pf,"derived_summary":summary(pf)} for n,pf in pfs.items()},
      "workspace_root":str(ROOT.parent.parent),"task_root":str(ROOT),"workspace_vs_task_paths_explicit":True,
      "max_file_seconds":max(pf["data"]["seconds"] for pf in pfs.values()),"Lean_started_by_consumer":False,"API_used":False}
    dump(STAGE/"actual-child-validation.json",cert)
    return {"validated":True,"certificate":task_rel(STAGE/"actual-child-validation.json"),"certificate_sha256":sha(STAGE/"actual-child-validation.json"),"max_file_seconds":cert["max_file_seconds"]}

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument("--certify-existing",action="store_true",required=True)
    print(json.dumps(certify(),sort_keys=True))
if __name__=="__main__": main()
