"""Durably publish three Open source parents, then verify the existing source root.

Offline modes never use credentials or a network. ``--advance`` publishes the
three exact Open parent sketches in one ``problems[]`` request, polls only saved
job ids, and then submits the sorry-free root reduction to the already existing
e717 target. No campaign proposal or Draft is created.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import certify_source_root_graph_existing as consumer
import stage_source_root_graph as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v2"
SELF = Path(__file__).resolve()
API = ROOT / "scripts/p2m_api.py"
CERT = STAGE / stage.CERTIFICATE
ROOT_SNAPSHOT = TASK / "verification/graph-refresh-20261011T131418_012581Z/e717eef2-11b1-4b14-9789-65f52c0502e1-target.json"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
PUBLISH_STATUSES = {"PENDING", "COMPILING", "PUBLISHED", "FAILED", "ERROR"}
VERIFY_STATUSES = {"PENDING", "COMPILING", "SKETCH_ACCEPTED", "ACCEPTED",
                   "CE", "WA", "SORRY", "FAILED", "ERROR"}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value): return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen source-root publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(raw)


def static():
    stage.check_only(); prep = read(STAGE / "preparation.json")
    need(prep["root_id"] == stage.ROOT_ID and prep["root_name"] == stage.ROOT_NAME
         and prep["closed_proof"] is False and prep["Open_placeholders_emit_reference_oleans"] is True
         and prep["excluded_community_adapters_imported"] is False,
         "Source-root stage identity/Open semantics differ")
    parents, problems = [], []
    for config, parent in zip(stage.CONFIGS, prep["parents"], strict=True):
        metadata = read(STAGE / f"parents/{config['key']}/academic-metadata.json")
        wire = STAGE / f"parents/{config['key']}/wire-theorem-source.lean"
        source = STAGE / config["file"]
        need(parent["name"] == config["name"] and parent["status"] == "Open"
             and parent["placeholder_semantics"].startswith("Open reference emitter")
             and source.read_bytes() == wire.read_bytes() ==
                 (parent["preamble"] + parent["formal_statement"]).encode()
             and b"sorry" in source.read_bytes(),
             "Open parent wire/identity differs: " + config["key"])
        problem = {"theorem_name": config["name"], "theorem_title": metadata["title"],
                   "preamble": parent["preamble"], "formal_statement": parent["formal_statement"],
                   "natural_language_statement": metadata["statement"],
                   "source": metadata["source_url"], "tags": metadata["tags"]}
        problems.append(problem)
        parents.append({"key": config["key"], "name": config["name"],
                        "module": config["module"], "source_sha256": sha(source),
                        "wire_sha256": sha(wire), "metadata_sha256": sha_bytes(encode(metadata))})
    publish = {"problems": problems, "env": ENV, "private": False}
    solution = STAGE / stage.SOLUTION_FILE; root_snapshot = read(ROOT_SNAPSHOT)
    need(root_snapshot["theorem_id"] == stage.ROOT_ID
         and root_snapshot["theorem_name"] == stage.ROOT_NAME
         and root_snapshot["status"] == "Open" and root_snapshot["mathlib_rev"] == ENV,
         "Existing source root snapshot differs")
    raw = solution.read_bytes()
    need(raw == (prep["root_preamble"] + prep["root_solution"]).encode()
         and raw == (STAGE / "root-sketch-wire.lean").read_bytes()
         and b"theorem solution : PiEventualLowerBound" in raw
         and b"sorry" not in raw and stage.ROOT_NAME.encode() not in raw,
         "Root sketch wire is not the exact sorry-free target-independent reduction")
    explanation = (
        "This is the original OpenAI source reduction. The conditional determinant theorem "
        "proves PiEventualLowerBound from the original global interpolation and analytic "
        "aggregate statements. The root solution supplies those two source statements to "
        "the original consequence theorem. All three imported children remain Open, so this "
        "submission is intentionally a SKETCH_ACCEPTED reduction and not a closed proof."
    )
    verify = {"theorem_id": stage.ROOT_ID, "proof_type": "prove", "explanation": explanation,
              "file": {"filename": Path(stage.SOLUTION_FILE).name,
                       "source": stage.rel(solution), "sha256": sha(solution),
                       "utf8": raw.decode()}}
    return prep, parents, publish, verify


def replay(cert, prep):
    need(consumer.validate() == cert, "Source-root certificate differs from exact strict replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "source-root-three-parent-open-sketch-validation"
         and cert["validated"] is True and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft"
         and cert["Open_sketch"] is True and cert["closed_proof"] is False
         and cert["source_proofs_Std3_only"] is True
         and cert["sorryAx_expected_only_from_Open_parents"] is True
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False,
         "Source-root certificate semantic state differs")
    need(cert["root_id"] == stage.ROOT_ID and cert["root_name"] == stage.ROOT_NAME
         and cert["parent_names"] == stage.NAMES and cert["parent_status"] == "Open"
         and cert["source_and_generated_parent_types_equal"] is True
         and cert["source_main_and_global_solution_types_equal"] is True
         and cert["actual_root_value_references"] == sorted(stage.NAMES)
         and cert["root_sketch_source_sha256"] == sha(STAGE / stage.SOLUTION_FILE)
         and cert["preparation_sha256"] == sha(STAGE / "preparation.json")
         and 0 < cert["max_file_seconds"] <= 300,
         "Source-root certificate identity/type/reference/budget differs")
    for name, expected in cert["parent_wire_sha256"].items():
        config = next(c for c in stage.CONFIGS if c["name"] == name)
        need(sha(STAGE / config["file"]) == expected, "Parent wire changed: " + name)
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "Source-root implementation changed: " + path)
    for path, expected in cert["snapshot_json_sha256"].items():
        need(sha(STAGE / path) == expected, "Source-root snapshot changed: " + path)


def artifacts(require_cert=True):
    prep, parents, publish, verify = static()
    cert = None
    if require_cert:
        need(CERT.is_file(), "Actual source-root certificate is pending")
        cert = read(CERT); replay(cert, prep)
    spec = importlib.util.spec_from_file_location("p2m_api_offline", API)
    api = importlib.util.module_from_spec(spec); spec.loader.exec_module(api)
    multipart, ctype = api._multipart(
        {"theorem_id": verify["theorem_id"], "proof_type": verify["proof_type"],
         "explanation": verify["explanation"]},
        {"file": (verify["file"]["filename"], verify["file"]["utf8"].encode())})
    payloads = {"publish-payload.json": json.dumps(publish, ensure_ascii=False).encode(),
                "verification-payload.json": encode(verify),
                "verification-request.multipart": multipart}
    pins = {"schema_version": 1,
        "artifact_kind": "source-root-three-parent-publish-and-existing-root-verify-preparation",
        "root_id": stage.ROOT_ID, "root_name": stage.ROOT_NAME,
        "parent_names": stage.NAMES, "environment": ENV,
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "validation_sha256": sha(CERT) if CERT.is_file() else None,
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "wrapper_sha256": sha(SELF), "api_client_sha256": sha(API),
        "root_snapshot_sha256": sha(ROOT_SNAPSHOT),
        "parents": parents, "payload_sha256": {k: sha_bytes(v) for k,v in payloads.items()},
        "multipart_content_type": ctype,
        "publish_route": "/submit-problem", "verify_route": "/verify",
        "parent_publication_batch_size": 3, "exact_existing_root_only": True,
        "creates_campaign_proposal": False,
        "durable_policy": "write intent before POST; never repeat an existing intent; poll only known ids",
        "Open_sketch": True, "closed_proof": False,
        "API_used": False, "submission_ready": False}
    return prep, parents, publish, verify, payloads, pins, cert


def pending():
    *_, payloads, pins, cert = artifacts(require_cert=False)
    for name, raw in payloads.items(): exact(DEST / name, raw)
    record = dict(pins); record.update({"artifact_kind": "source-root-pending-publication",
                                       "strict_validation_pending": cert is None,
                                       "network_used": False})
    exact(DEST / "pending-preparation.json", encode(record))
    return {"prepared": True, "validation_pending": cert is None, "network_used": False,
            "Open_sketch": True, "closed_proof": False, "payload_sha256": pins["payload_sha256"]}


def prepare():
    prep, parents, publish, verify, payloads, pins, cert = artifacts()
    for name, raw in payloads.items(): exact(DEST / name, raw)
    exact(DEST / "validation.json", CERT.read_bytes()); exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "API_used": False,
            "Open_sketch": True, "closed_proof": False, "payload_sha256": pins["payload_sha256"]}


def check():
    prep, parents, publish, verify, payloads, pins, cert = artifacts()
    need((DEST / "validation.json").read_bytes() == CERT.read_bytes()
         and (DEST / "preparation.json").read_bytes() == encode(pins),
         "Frozen source-root preparation differs")
    for name, raw in payloads.items(): need((DEST / name).read_bytes() == raw, "Payload differs: " + name)
    return prep, parents, publish, verify, payloads, pins, cert


def exact_theorem(current, problem, theorem_id=None):
    need((theorem_id is None or current.get("theorem_id") == theorem_id)
         and current.get("theorem_name") == problem["theorem_name"]
         and current.get("preamble") == problem["preamble"]
         and current.get("formal_statement") == problem["formal_statement"]
         and current.get("mathlib_rev") == ENV and current.get("visibility") == "public"
         and current.get("deprecated_at") is None,
         "Server theorem identity/text/environment differs: " + problem["theorem_name"])


def graph_check(graph, decompositions, submission_id, parent_ids):
    sketch = "sketch-" + submission_id
    edges = {(x.get("source"),x.get("target"),x.get("kind")) for x in graph.get("edges",[])}
    need(graph.get("root_id") == stage.ROOT_ID
         and (sketch, stage.ROOT_ID, "sketch") in edges
         and all((parent_ids[name], sketch, "sketch") in edges for name in stage.NAMES),
         "Refreshed source-root graph lacks one of the three actual parent edges")
    rows=[x for x in decompositions.get("decompositions",[]) if x.get("submission_id")==submission_id]
    need(len(rows)==1 and {x.get("theorem_id") for x in rows[0].get("children",[])} >= set(parent_ids.values()),
         "Refreshed source-root decomposition lacks the three actual Open parents")
    return {"sketch_node":sketch,"three_parent_edges":True,"sketch_to_root":True,
            "nodes":len(graph.get("nodes",[])),"edges":len(graph.get("edges",[]))}


def advance():
    prep, parents, publish, verify, payloads, pins, cert = check()
    root_frozen=read(ROOT_SNAPSHOT); record_path=DEST/"publication.json"
    record=read(record_path) if record_path.exists() else {"root_id":stage.ROOT_ID,
        "parent_names":stage.NAMES,"environment":ENV,"preparation_sha256":sha(DEST/"preparation.json")}
    need(record["root_id"]==stage.ROOT_ID and record["parent_names"]==stage.NAMES
         and record["environment"]==ENV and record["preparation_sha256"]==sha(DEST/"preparation.json"),
         "Existing source-root durable record differs")
    def save():
        record["updated_at_utc"]=datetime.now(timezone.utc).isoformat();record_path.write_bytes(encode(record))
    spec=importlib.util.spec_from_file_location("p2m_api",API);api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
    token=None
    def request(method,path,**kwargs):
        nonlocal token
        need(sha(SELF)==pins["wrapper_sha256"] and sha(API)==pins["api_client_sha256"]
             and sha(DEST/"preparation.json")==record["preparation_sha256"],"Frozen request inputs changed")
        if token is None: token=api.get_token()
        status,raw=api._request(method,path,token=token,**kwargs)
        return status,json.loads(raw)
    def get(path):
        status,body=request("GET",path);need(status==200 and isinstance(body,dict),"GET failed: "+path);return body

    if not record.get("parent_ids") and not record.get("publish_intent"):
        found={}
        for problem in publish["problems"]:
            matches=[];offset=0
            while True:
                status,body=request("GET","/theorems?theorem_name="+quote(problem["theorem_name"])+f"&env={ENV}&limit=100&offset={offset}")
                need(status==200 and isinstance(body.get("theorems"),list),"Exact parent lookup failed")
                page=body["theorems"];matches += [x for x in page if x.get("theorem_name")==problem["theorem_name"]]
                offset += len(page)
                if offset>=body["total"]:break
                need(bool(page),"Incomplete exact parent pagination")
            need(len(matches)<=1,"Duplicate exact parent name")
            if matches:
                theorem_id=matches[0].get("theorem_id")
                need(isinstance(theorem_id,str) and theorem_id,"Exact parent match lacks theorem id")
                item=get("/theorems/"+theorem_id);exact_theorem(item,problem,theorem_id)
                need(item.get("status")=="Open","Existing source parent is not Open")
                found[problem["theorem_name"]]=theorem_id
        need(len(found) in {0,3},"Partial pre-existing parent batch; refusing ambiguous publication")
        if len(found)==3:
            record["parent_ids"]=found;record["reused_exact_existing_parents"]=True;save()
        else:
            env=get("/environments");need(any(x.get("mathlib_rev")==ENV and x.get("toolchain")==TOOLCHAIN for x in env.get("environments",[])),"Pinned environment unavailable")
            record["publish_intent"]={"at_utc":datetime.now(timezone.utc).isoformat(),"endpoint":"/submit-problem",
                "problem_names":stage.NAMES,"payload_sha256":pins["payload_sha256"]["publish-payload.json"]};save()
            status,body=request("POST","/submit-problem",raw_body=payloads["publish-payload.json"])
            record["publish_response"]={"http_status":status,"body":body}
            jobs=body.get("jobs",[])
            if status==202 and not body.get("errors") and len(jobs)==3 and {x.get("name") for x in jobs}==set(stage.NAMES):
                record["publish_jobs"]={x["name"]:x["job_id"] for x in jobs if x.get("job_id")}
            save();need(len(record.get("publish_jobs",{}))==3,"Uncertain batch POST recorded; never repeat");return record
    if not record.get("parent_ids"):
        need(len(record.get("publish_jobs",{}))==3,"Publish intent lacks three known jobs; never repeat")
        ids={};verdicts={}
        for name,job in record["publish_jobs"].items():
            status,body=request("GET","/publish-jobs/"+job);verdicts[name]={"http_status":status,"body":body}
            need(status==200 and body.get("status") in PUBLISH_STATUSES,"Unknown parent publish status")
            if body.get("status")=="PUBLISHED":
                theorem_id=body.get("theorem_id") or body.get("definition_id")
                need(isinstance(theorem_id,str) and theorem_id,"PUBLISHED parent job lacks theorem id")
                ids[name]=theorem_id
        record["last_publish_verdicts"]=verdicts
        if len(ids)==3:record["parent_ids"]=ids
        save()
        if len(ids)!=3:return record
    parent_readback_sha={}
    key_by_name={c["name"]:c["key"] for c in stage.CONFIGS}
    for problem in publish["problems"]:
        theorem_id=record["parent_ids"].get(problem["theorem_name"])
        need(isinstance(theorem_id,str) and theorem_id,"Saved parent id is absent")
        item=get("/theorems/"+theorem_id);exact_theorem(item,problem,theorem_id);need(item.get("status")=="Open","Published parent not Open")
        path=DEST/"parent-readbacks"/(key_by_name[problem["theorem_name"]]+".json")
        path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(encode(item))
        parent_readback_sha[problem["theorem_name"]]={"path":stage.rel(path),"sha256":sha(path),"theorem_id":theorem_id,"status":"Open"}
    record["exact_parent_readbacks"]=parent_readback_sha;save()

    if not record.get("verify_intent"):
        root=get("/theorems/"+stage.ROOT_ID)
        exact_theorem(root,{"theorem_name":root_frozen["theorem_name"],"preamble":root_frozen["preamble"],"formal_statement":root_frozen["formal_statement"]},stage.ROOT_ID)
        need(root.get("status")=="Open","Existing source root no longer Open")
        record["verify_intent"]={"at_utc":datetime.now(timezone.utc).isoformat(),"endpoint":"/verify",
            "theorem_id":stage.ROOT_ID,"multipart_sha256":pins["payload_sha256"]["verification-request.multipart"],
            "content_type":pins["multipart_content_type"],"solution_sha256":verify["file"]["sha256"]};save()
        status,body=request("POST","/verify",raw_body=payloads["verification-request.multipart"],ctype=pins["multipart_content_type"])
        record["verify_response"]={"http_status":status,"body":body}
        if status in (200,202) and body.get("status") in VERIFY_STATUSES:record["submission_id"]=body.get("submission_id") or body.get("id")
        save();need(record.get("submission_id"),"Uncertain verify POST recorded; never repeat")
        if body.get("status")!="SKETCH_ACCEPTED":return record
    else:
        need(record.get("submission_id"),"Verify intent lacks known submission; never repeat")
        status,body=request("GET","/verify?submission_id="+record["submission_id"])
        record["last_verify_verdict"]={"http_status":status,"body":body};save()
        need(status==200 and body.get("theorem_id")==stage.ROOT_ID and body.get("status") in VERIFY_STATUSES,"Unknown root verify status")
        if body.get("status")!="SKETCH_ACCEPTED":return record
    post_root=get("/theorems/"+stage.ROOT_ID)
    exact_theorem(post_root,{"theorem_name":root_frozen["theorem_name"],"preamble":root_frozen["preamble"],"formal_statement":root_frozen["formal_statement"]},stage.ROOT_ID)
    need(post_root.get("status")=="Open","SKETCH_ACCEPTED root should remain Open while its children are Open")
    graph=get("/theorems/"+stage.ROOT_ID+"/graph");decompositions=get("/theorems/"+stage.ROOT_ID+"/decompositions")
    record["actual_three_parent_edges"]=graph_check(graph,decompositions,record["submission_id"],record["parent_ids"])
    (DEST/"post-root-target.json").write_bytes(encode(post_root));(DEST/"post-graph.json").write_bytes(encode(graph));(DEST/"post-decompositions.json").write_bytes(encode(decompositions))
    record["post_acceptance_readback_sha256"]={name:sha(DEST/name) for name in ["post-root-target.json","post-graph.json","post-decompositions.json"]}
    record["confirmed_SKETCH_ACCEPTED"]=True;save();return record


def main():
    parser=argparse.ArgumentParser(description=__doc__);m=parser.add_mutually_exclusive_group(required=True)
    m.add_argument("--prepare-pending",action="store_true");m.add_argument("--prepare-only",action="store_true")
    m.add_argument("--check-only",action="store_true");m.add_argument("--advance",action="store_true");a=parser.parse_args()
    if a.prepare_pending:result=pending()
    elif a.prepare_only:result=prepare()
    elif a.check_only:
        *_,pins,_=check();result={"checked":True,"network_used":False,"API_used":False,"Open_sketch":True,"closed_proof":False,"payload_sha256":pins["payload_sha256"]}
    else:result=advance()
    print(json.dumps(result,ensure_ascii=False,indent=2))


if __name__=="__main__":main()
