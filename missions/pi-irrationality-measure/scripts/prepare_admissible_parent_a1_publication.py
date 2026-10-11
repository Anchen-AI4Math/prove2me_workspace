"""Freeze the minimal source017e admissible-parent publication bundle offline."""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path

import publish_standalone_platform_node as publisher
import stage_admissible_parent_a1 as stage
import certify_admissible_parent_a1_existing as consumer
import validate_namespace_context_providers as context

TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-draft"
CERT = consumer.CERT
SELF = Path(__file__).resolve()

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p): return json.loads(Path(p).read_text(encoding="utf-8"))
def encode(x): return publisher.encode(x)
def need(x,m):
    if not x: raise ValueError(m)
def rel(p): return Path(p).resolve().relative_to(TASK.resolve()).as_posix()
def exact(p, raw):
    p=Path(p)
    if p.exists() and p.read_bytes()!=raw: raise ValueError("frozen a1 publication artifact differs: "+str(p))
    if not p.exists(): p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(raw)

CERT_FIELDS={"schema_version","artifact_kind","stage","source_name","theorem_name","source_commit",
 "stage_manifest_sha256","preparation_sha256","implementation_hashes","definition_dependencies",
 "proved_child_dependencies","preflights","compiled_Thm_exact_assembly","type_equalities","source_axioms",
 "solution_axioms","proof_references","project_proof_references","output_json_sha256","max_file_seconds",
 "validated","Lean_started_by_consumer","API_used","submission_ready","proposal_status"}

def static_artifacts():
    stage.check_outputs(stage.stage_files())
    manifest=read(STAGE/"manifest.json"); academic=read(STAGE/"academic-metadata.json")
    need(set(academic)=={"tags","source_commit","source_url","theorem_title","natural_language_statement",
        "mathematical_role","explanation","formalization_note","source_lines"},"academic paper metadata shape differs")
    need(academic["source_commit"]==stage.COMMIT and academic["source_url"].endswith("#L105-L220"),"academic source provenance differs")
    statement=ROOT/manifest["statement"]
    assembled=(manifest["preamble"]+manifest["formal_statement"]).encode("utf-8")
    need(statement.read_bytes()==assembled and sha(statement)==manifest["statement_sha256"],"strict Thm differs from preamble+formal bytes")
    metadata={"theorem_name":manifest["theorem_name"],"theorem_title":academic["theorem_title"],
      "natural_language_statement":academic["natural_language_statement"],"tags":academic["tags"],
      "explanation":academic["explanation"],"source_witness":{"commit":academic["source_commit"],
      "source_url":academic["source_url"],"source_module":manifest["source_module"],
      "source_lines":academic["source_lines"],"mathematical_role":academic["mathematical_role"],
      "formalization_note":academic["formalization_note"],"source_sha256":manifest["source_sha256"]}}
    payloads=publisher.payloads(DEST,manifest,metadata)
    problem=json.loads(payloads["publish-payload.json"])["problems"][0]
    need((problem["preamble"]+problem["formal_statement"]).encode()==assembled,"publish payload changes strict Thm")
    verify=json.loads(payloads["verification-payload.json"]); solution=ROOT/manifest["solution"]
    need(verify["file"]["utf8"].encode()==solution.read_bytes() and verify["file"]["sha256"]==sha(solution),"verification payload changes solution")
    return manifest,metadata,payloads,assembled

def replay_certificate(cert, manifest):
    need(set(cert)==CERT_FIELDS,"actual a1 consumer report schema differs")
    need(cert["validated"] is True and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False
         and cert["submission_ready"] is False and cert["proposal_status"]=="Draft","a1 report state differs")
    need(cert["source_name"]==stage.SOURCE_NAME and cert["theorem_name"]==stage.NAME and cert["source_commit"]==stage.COMMIT,"a1 report identity differs")
    need(cert["stage_manifest_sha256"]==sha(STAGE/"manifest.json") and cert["preparation_sha256"]==sha(STAGE/"preparation.json"),"a1 report stage pins stale")
    strict=cert["compiled_Thm_exact_assembly"]
    need(set(strict)=={"preamble_sha256","formal_statement_sha256","compiled_file_sha256","byte_equal"}
         and strict["byte_equal"] is True and strict["compiled_file_sha256"]==manifest["statement_sha256"],"a1 strict Thm report differs")
    for p,h in cert["implementation_hashes"].items(): need(sha(TASK/p)==h,"a1 implementation changed: "+p)
    for p,h in cert["output_json_sha256"].items(): need(sha(TASK/p)==h,"a1 output JSON changed: "+p)
    need(len(cert["preflights"])==4,"a1 must bind exactly four actual preflights")
    for name,row in cert["preflights"].items():
        data=row["data"]; source=context.file(data["source"]); mp=context.file(data["manifest"])
        current=context.record(source,mp,"modecheck",data["actual_module_identity"],STAGE)
        need(current==row,"actual context.record gate changed: "+name)
    for dep in [*cert["definition_dependencies"],*cert["proved_child_dependencies"]]:
        need(sha(TASK/dep["olean"])==dep["olean_sha256"],"actual first-search OLean changed: "+dep["module"])

def artifacts():
    manifest,metadata,payloads,assembled=static_artifacts()
    need(CERT.is_file(),"strict a1 consumer certificate is pending")
    cert=read(CERT); replay_certificate(cert,manifest)
    return manifest,metadata,payloads,assembled,cert

def pins(manifest,metadata,payloads):
    return {"theorem_name":stage.NAME,"environment":publisher.ENV,"proposal_status":"Draft",
      "manifest_sha256":hashlib.sha256(encode(manifest)).hexdigest(),"validation_sha256":sha(CERT),
      "metadata_sha256":hashlib.sha256(encode(metadata)).hexdigest(),"publisher_sha256":sha(Path(publisher.__file__)),
      "api_client_sha256":sha(ROOT/"scripts/p2m_api.py"),"payload_sha256":{n:hashlib.sha256(b).hexdigest() for n,b in payloads.items()},
      "offline_wrapper_sha256":sha(SELF),"local_node_validated":True,"submission_ready":False,"full_tree_ready":False,
      "verification_payload_is_offline_descriptor":True,"verification_theorem_id_late_bound_only":True,"api_used":False}

def pending():
    manifest,metadata,payloads,assembled=static_artifacts()
    exact(DEST/"metadata.json",encode(metadata)); exact(DEST/"wire-theorem-source.lean",assembled)
    for n,b in payloads.items(): exact(DEST/n,b)
    return {"prepared":True,"validation_pending":not CERT.is_file(),"network_used":False,"proposal_status":"Draft"}

def prepare():
    manifest,metadata,payloads,assembled,cert=artifacts(); p=pins(manifest,metadata,payloads)
    exact(DEST/"manifest.json",encode(manifest)); exact(DEST/"validation.json",CERT.read_bytes())
    exact(DEST/"metadata.json",encode(metadata)); exact(DEST/"wire-theorem-source.lean",assembled)
    for n,b in payloads.items(): exact(DEST/n,b)
    exact(DEST/"preparation.json",encode(p))
    return {"prepared":True,"network_used":False,"proposal_status":"Draft","payload_sha256":p["payload_sha256"]}

def check():
    manifest,metadata,payloads,assembled,cert=artifacts(); p=pins(manifest,metadata,payloads)
    need((DEST/"manifest.json").read_bytes()==encode(manifest) and (DEST/"validation.json").read_bytes()==CERT.read_bytes()
         and (DEST/"metadata.json").read_bytes()==encode(metadata) and (DEST/"wire-theorem-source.lean").read_bytes()==assembled
         and (DEST/"preparation.json").read_bytes()==encode(p),"frozen a1 publication evidence differs")
    for n,b in payloads.items(): need((DEST/n).read_bytes()==b,"frozen a1 payload differs: "+n)
    return {"checked":True,"network_used":False,"proposal_status":"Draft","payload_sha256":p["payload_sha256"]}

if __name__=="__main__":
    a=argparse.ArgumentParser(description=__doc__); g=a.add_mutually_exclusive_group(required=True)
    g.add_argument("--prepare-pending",action="store_true"); g.add_argument("--prepare-only",action="store_true"); g.add_argument("--check-only",action="store_true")
    x=a.parse_args(); print(json.dumps(pending() if x.prepare_pending else prepare() if x.prepare_only else check(),ensure_ascii=False,indent=2))
