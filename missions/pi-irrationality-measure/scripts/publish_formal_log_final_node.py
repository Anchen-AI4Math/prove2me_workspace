"""Prepare and explicitly publish one certified FormalLog proof node.

The default path is offline. Only explicit ``--advance`` or ``--prepare-and-advance`` modes read API
credentials or make requests. Each publication and verification POST is
preceded by a durable intent and is never retried after an uncertain result.
"""
from __future__ import annotations

import argparse
from bisect import bisect_right
from datetime import datetime, timezone
from difflib import SequenceMatcher
import hashlib
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import validate_formal_log_final_node as checker
import publish_formal_log_successor_node as retained_successor
import formal_log_final_security_pins as securitypins

TASK, ROOT = checker.TASK, checker.ROOT
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
NODE_ROOT = TASK / "verification/flp3"
DEFAULT_STAGE = NODE_ROOT / "f4"
DEFAULT_METADATA = TASK / "platform/formal-log-node-metadata/formalLog_packets_surjective_iff_truncated.json"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SECURITY_HELPER_SHA256 = "f27f063a8b65cac8861ff74ee186e398479f4e04034aad045c72d6e7f07f3daa"
FINAL_CHECKER_SHA256 = "afe8425642784280bd49e66e5ebbaf134642213e830a5ef381942c3351163d75"
RETAINED_SUCCESSOR_SHA256 = "b084ca262fbbfdceb687c8b41afd42ba32aedcd10d7e0f8e78c557cadf99dc89"
PARENTS = {
    "f2": {"theorem_id": "bc74060f-2602-42a2-ab0a-7435517bae27", "submission_id": "4f54c75a-6ac6-409a-8da5-3f016779cd13", "certificate": "successor-node-validation.json"},
    "f3": {"theorem_id": "9e8a05d9-eb6a-4e92-92d2-640defa3421c", "submission_id": "d1bf8788-830c-4f74-92c6-3dbbf427fa1b", "certificate": "complete-node-validation.json"},
}


def parent_server_gate(request, record, save):
    """Both exact own Accepted parents plus fresh public Proved readbacks."""
    gates={}
    for key,identity in PARENTS.items():
        stage=TASK/"verification/flp3"/key
        path=stage/"publication/publication.json";before=sha(path);parent=read(path);m=read(stage/"manifest.json")
        tid,sid=identity["theorem_id"],identity["submission_id"]
        accepted=parent.get("last_verify_verdict",{})
        body=accepted.get("body",{})
        if (parent.get("theorem_id")!=tid or parent.get("submission_id")!=sid
                or parent.get("accepted") is not True or parent.get("confirmed_proved") is not True
                or accepted.get("http_status")!=200 or body.get("status")!="ACCEPTED"
                or body.get("theorem_id")!=tid or (body.get("submission_id") or body.get("id"))!=sid
                or parent.get("preparation",{}).get("certificate_sha256")!=sha(stage/identity["certificate"])
                or parent.get("target_binding",{}).get("manifest_sha256")!=sha(stage/"manifest.json")):
            raise ValueError("Exact own Accepted parent receipt/certified binding missing: "+key)
        status,verdict=request("GET","/verify?submission_id="+quote(sid,safe=""))
        record.setdefault("parent_submission_readbacks",{})[key]={"http_status":status,"body":verdict};save()
        if (status!=200 or verdict.get("status")!="ACCEPTED" or verdict.get("theorem_id")!=tid
                or (verdict.get("submission_id") or verdict.get("id"))!=sid):
            raise ValueError("Fresh exact own Accepted parent verification failed: "+key)
        status,target=request("GET","/theorems/"+quote(tid,safe=""))
        record.setdefault("parent_target_readbacks",{})[key]={"http_status":status,"body":target};save()
        if (status!=200 or target.get("theorem_id")!=tid or target.get("status")!="Proved"
                or target.get("theorem_name")!=m["theorem_name"] or target.get("mathlib_rev")!=ENV
                or target.get("visibility")!="public" or target.get("deprecated_at") is not None
                or target.get("formal_statement")!=m["formal_statement"] or target.get("preamble")!=m["preamble"]
                or sha(path)!=before):
            raise ValueError("Fresh exact Proved parent/readback stability failed: "+key)
        gates[key]={"validated":True,"own_accepted":True,"fresh_exact_proved":True,"theorem_id":tid,
            "submission_id":sid,"publication_record_sha256":before,"checked_at_utc":datetime.now(timezone.utc).isoformat()}
    record["parent_server_gate"]={"validated":True,"parents":gates};save()


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def encode(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")


def read(path: Path):
    return json.loads(path.read_bytes().decode("utf-8"))


def confined_file(value, *, base: Path) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = base / path
    path = path.resolve()
    if not path.is_relative_to(TASK.resolve()) or not path.is_file():
        raise ValueError("Evidence path is absent or outside the mission: " + str(value))
    return path


def stage_path(value) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = TASK / path
    path = path.resolve()
    if path not in [(NODE_ROOT / "f4").resolve()] or not path.is_dir():
        raise ValueError("Expected one FormalLog proof-node stage directly under verification/flp3")
    return path


def source_witness(manifest, evidence):
    changed_name='OAI.PiExponent.FormalLogTruncation.rationalCoefficientPacket_surjective'
    requests=manifest['public_inline_ci_requests']
    changed=[r for r in requests if r['source_graph_name']==changed_name]
    if len(changed)!=1 or changed[0]['source_unit']!='OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:9129':
        raise ValueError('Expected the exact retained rationalCoefficientPacket_surjective AST unit')
    filtered={**manifest,'public_inline_ci_requests':[r for r in requests if r['source_graph_name']!=changed_name]}
    # Main and four unchanged inline command boundaries use the frozen exact
    # whole-file line mapper. The remaining helper has one real port edit at
    # its proof-end line; keep separate original/port spans and raw hashes.
    witness=retained_successor.source_witness(filtered,evidence)
    c=manifest['source_components'][0];original=(ROOT/c['original_source']).read_bytes();ported=(ROOT/c['source']).read_bytes()
    old_lines,new_lines=original.splitlines(keepends=True),ported.splitlines(keepends=True)
    def offsets(lines):
        out=[0]
        for line in lines:out.append(out[-1]+len(line))
        return out
    old_offsets,new_offsets=offsets(old_lines),offsets(new_lines)
    old_contents=[line.rstrip(b'\r\n') for line in old_lines];new_contents=[line.rstrip(b'\r\n') for line in new_lines]
    blocks=SequenceMatcher(None,old_contents,new_contents,autojunk=False).get_matching_blocks()
    request=changed[0];pa,pb=[request['source_command_range'][k]['offset'] for k in ['start','end']]
    if (pa,pb)!=(9129,9436):raise ValueError('Exact version-edited helper port AST coordinates changed')
    start_line=bisect_right(new_offsets,pa)-1;end_line=bisect_right(new_offsets,pb)-1
    start_block=next(b for b in blocks if b.b<=start_line<b.b+b.size)
    oa=old_offsets[start_block.a+start_line-start_block.b]+pa-new_offsets[start_line]
    before=next(b for b in blocks if b.size and b.b+b.size==end_line)
    after=next(b for b in blocks if b.size and b.b==end_line+1)
    old_end_line=before.a+before.size
    if (after.a!=old_end_line+1 or pb-new_offsets[end_line]!=len(new_contents[end_line])
            or old_contents[old_end_line]!=b'  exact dite_eq_left d.property'
            or new_contents[end_line]!=b'  exact dif_pos d.property'):
        raise ValueError('Only the exact single proof-end-line port edit between unchanged full-file line blocks is supported')
    ob=old_offsets[old_end_line]+len(old_contents[old_end_line])
    if original[oa:ob].splitlines()[:-1]!=ported[pa:pb].splitlines()[:-1]:
        raise ValueError('Edited helper differs outside the exact final-line version change/line endings')
    first,last=bisect_right(old_offsets,oa),bisect_right(old_offsets,ob-1)
    row={'source_graph_name':changed_name,'source_module':request['source_module'],
        'source_url':'https://github.com/openai/math/blob/'+COMMIT+'/lean/'+request['source_module'].replace('.','/')+f'.lean#L{first}-L{last}',
        'port_source':c['source'],'port_source_sha256':c['source_sha256'],'port_command_range':{'start':pa,'end':pb},
        'port_command_sha256':sha_bytes(ported[pa:pb]),'original_source':c['original_source'],
        'original_source_sha256':c['original_source_sha256'],'original_command_range':{'start':oa,'end':ob},
        'original_command_sha256':sha_bytes(original[oa:ob]),'port_and_original_command_bytes_equal':False,
        'proof_end_line_version_edit':{'original_line':old_end_line+1,'port_line':end_line+1,
            'original_text':old_contents[old_end_line].decode(),'port_text':new_contents[end_line].decode(),
            'original_raw_line_sha256':sha_bytes(old_lines[old_end_line]),'port_raw_line_sha256':sha_bytes(new_lines[end_line]),
            'exact_single_replaced_line_between_unchanged_full_file_line_blocks':True,
            'all_preceding_helper_line_contents_equal':True}}
    by_name={r['source_graph_name']:r for r in witness['inline_support_witnesses']};by_name[changed_name]=row
    witness['inline_support_witnesses']=[by_name[r['source_graph_name']] for r in requests]
    for row in witness['inline_support_witnesses']:
        row['purpose']='Retained original public inline support theorem in the source proof of formalLog_packets_surjective_iff_truncated.'
    return witness


def check_metadata(metadata, manifest, evidence):
    expected = {"theorem_name", "theorem_title", "natural_language_statement", "tags", "explanation", "source_witness"}
    if set(metadata) != expected or metadata["theorem_name"] != manifest["theorem_name"]:
        raise ValueError("Metadata schema or target theorem name differs")
    for field in ("theorem_title", "natural_language_statement", "explanation"):
        if not isinstance(metadata[field], str) or not metadata[field].strip():
            raise ValueError("Missing academic metadata text: " + field)
    tags = metadata["tags"]
    if (not isinstance(tags, list) or not tags
            or any(not isinstance(tag, str) or not tag.strip() for tag in tags)
            or len(tags) != len(set(tags)) or "openai-pi-exponent-017" not in tags):
        raise ValueError("Metadata tags must be unique and retain source-family provenance")
    witness = source_witness(manifest, evidence)
    if metadata["source_witness"] != witness:
        raise ValueError("Metadata source witness differs from the exact original/ported source spans")


def seal_metadata(path,metadata,manifest,evidence,*,write):
    """Complete only the supplied five-field draft after actual full review.

    The draft bytes are retained once. Existing six-field metadata is never
    rewritten, and an established publication intent makes metadata immutable.
    """
    fields={"theorem_name","theorem_title","natural_language_statement","tags","explanation"}
    if set(metadata)==fields:
        if not write:
            raise ValueError("Metadata draft lacks actual certified source witness; run offline prepare first")
        publication=Path(evidence["stage"])/"publication"
        state=publication/"publication.json"
        if state.is_file():
            r=read(state)
            if r.get("publication_intent") or r.get("verification_intent"):
                raise ValueError("Cannot complete metadata after a durable publication intent")
        if publication.is_symlink() or state.is_symlink() or path.is_symlink():
            raise ValueError("Metadata/publication paths must not be symlinks")
        original=path.read_bytes()
        completed={**metadata,"source_witness":source_witness(manifest,evidence)}
        check_metadata(completed,manifest,evidence)
        publication.mkdir(exist_ok=True)
        archive=publication/"metadata-five-field-draft.json"
        if archive.is_symlink() or archive.is_file() and archive.read_bytes()!=original:
            raise ValueError("Retained five-field academic metadata draft differs")
        if not archive.exists():archive.write_bytes(original)
        path.write_bytes((json.dumps(completed,ensure_ascii=False,indent=2)+"\n").encode("utf-8"))
        return completed
    return metadata


def check_certificate(evidence, stage):
    if evidence.get("validated") is not True or evidence.get("submission_ready") is not False:
        raise ValueError("Read-only formal node validation is missing or claims submission readiness")
    if evidence["stage"].resolve() != stage.resolve():
        raise ValueError("Current certificate belongs to a different stage")
    cert_path = confined_file(evidence["certificate"]["path"], base=TASK)
    if cert_path != (stage / "final-node-validation.json").resolve():
        raise ValueError("Certificate is not at the exact FormalLog stage path")
    cert = evidence["certificate"]["data"]
    if sha(cert_path) != evidence["certificate"]["sha256"] or read(cert_path) != cert:
        raise ValueError("Current read-only replay and saved certificate differ")
    for flag in ("validated", "source_skeleton_and_inventory_reconstructed", "kernel_types_equal", "inline_kernel_types_equal",
                 "source_target_solution_universes_equal", "theorem_values_null", "target_stub_unused",
                 "actual_project_reference_coverage_complete", "Std3_only"):
        if cert.get(flag) is not True:
            raise ValueError("Formal node certificate lacks required kernel evidence: " + flag)
    if (cert.get("proof_axioms") != "Std3" or cert.get("submission_ready") is not False
            or cert.get("full_tree_ready") is not False or cert.get("source_scope_partial") is not True):
        raise ValueError("Certificate has an invalid axiom, scope, or readiness status")
    manifest_path = confined_file(evidence["manifest"], base=TASK)
    manifest = evidence["manifest_data"]
    if (manifest_path != (stage / "manifest.json").resolve()
            or cert.get("manifest") != manifest_path.relative_to(TASK.resolve()).as_posix()
            or cert.get("manifest_sha256") != sha(manifest_path)):
        raise ValueError("Certificate does not bind the exact staged manifest")
    if cert.get("node") != manifest.get("node") or cert.get("theorem_name") != manifest.get("theorem_name"):
        raise ValueError("Certificate target identity differs from the manifest")
    if cert.get("source_commit") != COMMIT:
        raise ValueError("Certificate source commit differs from the pinned OpenAI math commit")
    if cert.get("statement_sha256") != manifest.get("statement_sha256") or cert.get("solution_sha256") != manifest.get("solution_sha256"):
        raise ValueError("Certificate statement or solution bytes differ from the manifest")
    if cert.get("source_components") != manifest.get("source_components"):
        raise ValueError("Certificate source lineage differs from the node manifest")
    if cert.get("max_file_seconds", 301) > 300:
        raise ValueError("A node file exceeds the 300-second compilation cap")
    dependencies = cert.get("definition_certificates")
    if (not isinstance(dependencies, list)
            or len(dependencies) != len(manifest.get("definition_dependency_witnesses", []))):
        raise ValueError("Definition dependency certificate domain is incomplete")
    for row in dependencies:
        if row.get("validated") is not True or row.get("proof_axioms") != "Std3":
            raise ValueError("A Definition dependency lacks current standard-axiom certification")
    return cert_path, cert


def make_payloads(evidence, manifest, metadata):
    witness = metadata["source_witness"]
    problem = {
        "theorem_name": manifest["theorem_name"],
        "theorem_title": metadata["theorem_title"],
        "natural_language_statement": metadata["natural_language_statement"],
        "formal_statement": manifest["formal_statement"],
        "preamble": manifest["preamble"],
        "source": witness["source_url"],
        "tags": metadata["tags"],
    }
    publish = {"problems": [problem], "env": ENV, "private": False}
    solution_path = confined_file(manifest["solution"], base=ROOT)
    solution = evidence["solution_bytes"]
    if (solution_path.read_bytes() != solution or sha_bytes(solution) != manifest["solution_sha256"]):
        raise ValueError("Exact solution bytes differ from the validated stage")
    verify = {
        "target_theorem_name": manifest["theorem_name"], "env": ENV, "theorem_id": None,
        "theorem_id_binding": "exact public theorem name/environment/preamble/formal_statement readback",
        "proof_type": "prove", "explanation": metadata["explanation"],
        "file": {"filename": solution_path.name, "source": manifest["solution"],
                 "sha256": sha_bytes(solution), "utf8": solution.decode("utf-8")},
    }
    return {"publish-payload.json": encode(publish), "verification-payload.json": encode(verify)}


def target_binding(manifest, pins):
    preamble = manifest["preamble"]
    statement = manifest["formal_statement"]
    return {
        "theorem_name": manifest["theorem_name"],
        "mathlib_rev": ENV,
        "visibility": "public",
        "preamble": preamble,
        "preamble_sha256": sha_bytes(preamble.encode("utf-8")),
        "formal_statement": statement,
        "formal_statement_sha256": sha_bytes(statement.encode("utf-8")),
        "manifest_sha256": pins["manifest_sha256"],
        "certificate_sha256": pins["certificate_sha256"],
        "metadata_sha256": pins["metadata_sha256"],
    }


def prepare(stage_value, metadata_value, *, write=True):
    stage = stage_path(stage_value)
    if sha(Path(securitypins.__file__).resolve()) != SECURITY_HELPER_SHA256:
        raise ValueError("Typed FormalLog security-pin helper differs from the frozen implementation")
    if sha(Path(checker.__file__)) != FINAL_CHECKER_SHA256 or sha(Path(retained_successor.__file__)) != RETAINED_SUCCESSOR_SHA256:
        raise ValueError("Frozen final checker/source-witness utility changed")
    evidence = checker.validate_formal_final_node(stage)
    cert_path, cert = check_certificate(evidence, stage)
    manifest = evidence["manifest_data"]
    if manifest.get("source_commit") != COMMIT or manifest.get("formal_statement") is None:
        raise ValueError("Missing exact source commit or formal statement")
    if manifest.get("node_generated_names") or len(manifest.get("child_nodes", {})) != 2 or len(cert.get("child_certificates", [])) != 2:
        raise ValueError("Final node requires two exact actual-certified proved successor children without aliases")
    metadata_path = confined_file(metadata_value, base=TASK)
    metadata = read(metadata_path)
    metadata = seal_metadata(metadata_path,metadata,manifest,evidence,write=write)
    check_metadata(metadata, manifest, evidence)
    payloads = make_payloads(evidence, manifest, metadata)
    publication_dir = stage / "publication"
    if publication_dir.resolve().parent != stage.resolve():
        raise ValueError("Publication record directory escaped the stage")
    pins = {
        "schema_version": 1,
        "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "definition_name": manifest["theorem_name"],
        "environment": ENV,
        "toolchain": TOOLCHAIN,
        "proposal_status": "Draft",
        "stage": stage.relative_to(TASK).as_posix(),
        "metadata_file": metadata_path.relative_to(TASK).as_posix(),
        "manifest_sha256": sha(stage / "manifest.json"),
        "certificate_sha256": sha(cert_path),
        "metadata_sha256": sha(metadata_path),
        "publisher_sha256": sha(Path(__file__).resolve()),
        "checker_sha256": sha(Path(checker.__file__).resolve()),
        "retained_successor_sha256": RETAINED_SUCCESSOR_SHA256,
        "certificate_file": cert_path.relative_to(TASK).as_posix(),
        "security_helper_sha256": SECURITY_HELPER_SHA256,
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "payload_sha256": {name: sha_bytes(data) for name, data in payloads.items()},
        "source_commit": COMMIT,
        "source_component_sha256": {row["source"]: row["source_sha256"] for row in manifest["source_components"]},
        "original_source_sha256": {row["original_source"]: row["original_source_sha256"] for row in manifest["source_components"]},
        "node_kernel_types_equal": True,
        "standard_axioms_only": True,
        "source_scope_partial": True,
        "full_tree_ready": False,
        "submission_ready": False,
        "proof_file_seconds": cert["max_file_seconds"],
    }
    pins["security_pins"] = securitypins.reviewed_security_pins(evidence)
    record_path = publication_dir / "publication.json"
    if publication_dir.is_symlink():
        raise ValueError("Publication directory must not be a symlink")
    prep_path = publication_dir / "preparation.json"
    if record_path.is_symlink() or prep_path.is_symlink():
        raise ValueError("Publication state files must not be symlinks")
    if record_path.is_file():
        record = read(record_path)
        if record.get("publication_intent") or record.get("verification_intent"):
            durable = record.get("preparation")
            if not isinstance(durable, dict):
                raise ValueError("Durable publication intent fixes the exact prepared payload")
            durable_comparable = {key: value for key, value in durable.items() if key != "prepared_at_utc"}
            current_comparable = {key: value for key, value in pins.items() if key != "prepared_at_utc"}
            if durable_comparable != current_comparable or not prep_path.is_file():
                raise ValueError("Durable publication intent fixes the exact prepared payload")
            pins = read(prep_path)
            if pins != durable:
                raise ValueError("Durable publication record and offline preparation disagree")
    if not write:
        if not prep_path.is_file():
            raise ValueError("Offline payloads are not prepared and pinned; run default mode first")
        saved_pins = read(prep_path)
        saved_comparable = {key: value for key, value in saved_pins.items() if key != "prepared_at_utc"}
        current_comparable = {key: value for key, value in pins.items() if key != "prepared_at_utc"}
        if saved_comparable != current_comparable:
            raise ValueError("Current inputs differ from the frozen offline preparation")
        pins = saved_pins
        for filename, data in payloads.items():
            path = publication_dir / filename
            if path.is_symlink() or not path.is_file() or path.read_bytes() != data:
                raise ValueError("Reviewed payload bytes changed: " + filename)
        return stage, publication_dir, evidence, manifest, metadata, pins, payloads
    publication_dir.mkdir(exist_ok=True)
    for filename, data in payloads.items():
        path = publication_dir / filename
        if path.is_symlink():
            raise ValueError("Prepared payload must not be a symlink: " + filename)
        if path.is_file() and path.read_bytes() != data and record_path.is_file():
            record = read(record_path)
            if record.get("publication_intent") or record.get("verification_intent"):
                raise ValueError("Cannot change prepared bytes after a durable API intent")
        path.write_bytes(data)
    (publication_dir / "preparation.json").write_bytes(encode(pins))
    return stage, publication_dir, evidence, manifest, metadata, pins, payloads


def advance(stage, publication_dir, evidence, manifest, metadata, pins, payloads):
    # Credentials and the API client are loaded only inside this explicit branch.
    securitypins.assert_security_pins(pins["security_pins"])
    if sha(ROOT / "scripts/p2m_api.py") != pins["api_client_sha256"]:
        raise ValueError("Pinned API client changed before import")
    spec = importlib.util.spec_from_file_location("formal_log_p2m_api", ROOT / "scripts/p2m_api.py")
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    record_path = publication_dir / "publication.json"
    if publication_dir.is_symlink() or record_path.is_symlink():
        raise ValueError("Publication state must not be stored through symlinks")
    expected_binding = target_binding(manifest, pins)
    record = read(record_path) if record_path.is_file() else {
        "schema_version": 1, "artifact_kind": "formal-log-proof-node-publication-record",
        "theorem_name": manifest["theorem_name"], "environment": ENV,
        "target_binding": expected_binding, "preparation": pins,
        "proposal_status": "Draft", "advance_requested_at_utc": datetime.now(timezone.utc).isoformat(),
    }
    if (record.get("schema_version") != 1
            or record.get("artifact_kind") != "formal-log-proof-node-publication-record"
            or record.get("theorem_name") != manifest["theorem_name"]
            or record.get("environment") != ENV
            or record.get("target_binding") != expected_binding
            or record.get("preparation") != pins):
        raise ValueError("Durable publication record does not bind the exact reviewed successor target")

    def save():
        if record_path.is_symlink():
            raise ValueError("Publication record must not be a symlink")
        record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
        record_path.write_bytes(encode(record))

    def guard():
        metadata_path = confined_file(pins["metadata_file"], base=TASK)
        securitypins.assert_security_pins(pins["security_pins"])
        if (publication_dir.is_symlink()
                or (publication_dir / "publication.json").is_symlink()
                or (publication_dir / "preparation.json").is_symlink()
                or (publication_dir / "preparation.json").read_bytes() != encode(pins)
                or sha(stage / "manifest.json") != pins["manifest_sha256"]
                or sha(TASK / pins["certificate_file"]) != pins["certificate_sha256"]
                or sha(Path(__file__).resolve()) != pins["publisher_sha256"]
                or sha(Path(checker.__file__).resolve()) != pins["checker_sha256"]
                or sha(Path(retained_successor.__file__).resolve()) != pins["retained_successor_sha256"]
                or pins["security_helper_sha256"] != SECURITY_HELPER_SHA256
                or sha(Path(securitypins.__file__).resolve()) != SECURITY_HELPER_SHA256
                or sha(ROOT / "scripts/p2m_api.py") != pins["api_client_sha256"]
                or sha(metadata_path) != pins["metadata_sha256"]):
            raise ValueError("Reviewed source, certificate, metadata, publisher, or API client changed")
        for filename, expected in pins["payload_sha256"].items():
            payload_path = publication_dir / filename
            if payload_path.is_symlink() or sha(payload_path) != expected:
                raise ValueError("Reviewed payload changed: " + filename)

    def request(method, path, **kwargs):
        guard()
        token = api.get_token()
        guard()
        status, body = api._request(method, path, token=token, **kwargs)
        guard()
        return status, json.loads(body)

    def readback(theorem_id):
        status, body = request("GET", "/theorems/" + quote(theorem_id, safe=""))
        record["target_readback"] = {"http_status": status, "body": body}
        save()
        if (status != 200 or body.get("theorem_id") != theorem_id
                or body.get("theorem_name") != manifest["theorem_name"]
                or body.get("mathlib_rev") != ENV or body.get("visibility") != "public"
                or body.get("deprecated_at") is not None
                or body.get("formal_statement") != manifest["formal_statement"]
                or body.get("preamble") != manifest["preamble"]):
            raise ValueError("Server target differs in identity, statement, preamble, environment, or visibility")
        return body

    save()
    parent_server_gate(request, record, save)
    if not record.get("theorem_id") and not record.get("publication_intent") and not record.get("job_id"):
        matches, offset = [], 0
        while True:
            status, body = request("GET", "/theorems?theorem_name=" + quote(manifest["theorem_name"])
                                   + f"&env={ENV}&limit=100&offset={offset}")
            if status != 200 or not isinstance(body.get("theorems"), list):
                raise ValueError("Exact theorem-name lookup failed; nothing posted")
            page = body["theorems"]
            matches.extend(row for row in page if row.get("theorem_name") == manifest["theorem_name"])
            total = body.get("total")
            if not isinstance(total, int) or total < 0:
                raise ValueError("Theorem lookup omitted a reliable total")
            offset += len(page)
            if offset >= total:
                break
            if not page:
                raise ValueError("Theorem lookup pagination ended early")
        if matches:
            if len(matches) != 1 or not matches[0].get("theorem_id"):
                raise ValueError("Ambiguous exact-name theorem already exists")
            target = readback(matches[0]["theorem_id"])
            record["theorem_id"] = target["theorem_id"]
            record["reused_exact_existing_target"] = True
            save()
        else:
            status, envs = request("GET", "/environments")
            if status != 200 or not any(row.get("mathlib_rev") == ENV and row.get("toolchain") == TOOLCHAIN
                                        for row in envs.get("environments", [])):
                raise ValueError("Pinned public environment unavailable; no submission sent")
            record["publication_intent"] = {
                "at_utc": datetime.now(timezone.utc).isoformat(), "endpoint": "/submit-problem",
                "payload_sha256": pins["payload_sha256"]["publish-payload.json"],
                "theorem_name": manifest["theorem_name"], "environment": ENV, "visibility": "public",
            }
            save()
            raw = (publication_dir / "publish-payload.json").read_bytes()
            if sha_bytes(raw) != pins["payload_sha256"]["publish-payload.json"] or raw != payloads["publish-payload.json"]:
                raise ValueError("Published problem payload changed after durable intent")
            status, body = request("POST", "/submit-problem", raw_body=raw, ctype="application/json")
            record["publication_response"] = {"http_status": status, "body": body}
            jobs = body.get("jobs", [])
            if (status == 202 and not body.get("errors") and len(jobs) == 1
                    and jobs[0].get("name") == manifest["theorem_name"] and jobs[0].get("job_id")):
                record["job_id"] = jobs[0]["job_id"]
            save()
            return

    if not record.get("theorem_id"):
        if record.get("publication_intent") and not record.get("job_id"):
            raise ValueError("Uncertain theorem POST is recorded without a job id; inspect manually, never retry")
        status, body = request("GET", "/publish-jobs/" + quote(record["job_id"], safe=""))
        record["last_publish_verdict"] = {"http_status": status, "body": body}
        if (status == 200 and body.get("status") == "PUBLISHED"
                and body.get("theorem_name", manifest["theorem_name"]) == manifest["theorem_name"]
                and body.get("mathlib_rev", ENV) == ENV):
            record["theorem_id"] = body.get("theorem_id")
        save()
        if not record.get("theorem_id"):
            return

    target = readback(record["theorem_id"])
    if target.get("status") == "Proved" and not record.get("submission_id"):
        record["confirmed_proved"] = True
        record["existing_proved_reused"] = True
        save()
        return
    if not record.get("submission_id"):
        if record.get("accepted"):
            record["accepted_waiting_for_proved_readback"] = True
            save()
            return
        if record.get("verification_intent"):
            raise ValueError("Uncertain verification POST is recorded; inspect manually, never retry")
        descriptor = read(publication_dir / "verification-payload.json")
        solution_utf8 = descriptor["file"]["utf8"].encode("utf-8")
        if sha_bytes(solution_utf8) != descriptor["file"]["sha256"]:
            raise ValueError("Exact solution bytes differ from the prepared verification descriptor")
        multipart, ctype = api._multipart(
            {"theorem_id": record["theorem_id"], "proof_type": descriptor["proof_type"],
             "explanation": descriptor["explanation"]},
            {"file": (descriptor["file"]["filename"], solution_utf8)})
        record["verification_intent"] = {
            "at_utc": datetime.now(timezone.utc).isoformat(), "endpoint": "/verify",
            "theorem_id": record["theorem_id"], "multipart_sha256": sha_bytes(multipart),
            "content_type": ctype, "solution_sha256": descriptor["file"]["sha256"],
            "descriptor_sha256": pins["payload_sha256"]["verification-payload.json"],
        }
        save()
        status, body = request("POST", "/verify", raw_body=multipart, ctype=ctype)
        record["verification_response"] = {"http_status": status, "body": body}
        record["last_verify_verdict"] = {"http_status": status, "body": body}
        if status in (200, 202) and body.get("status") in {"PENDING", "COMPILING"}:
            submission_id = body.get("submission_id") or body.get("id")
            if isinstance(submission_id, str) and submission_id:
                record["submission_id"] = submission_id
        elif status == 200 and body.get("status") == "ACCEPTED":
            record["accepted"] = True
            submission_id = body.get("submission_id") or body.get("id")
            if isinstance(submission_id, str) and submission_id:
                record["submission_id"] = submission_id
        save()
        if status == 200 and body.get("status") == "ACCEPTED":
            record["confirmed_proved"] = readback(record["theorem_id"]).get("status") == "Proved"
            save()
        return

    status, body = request("GET", "/verify?submission_id=" + quote(record["submission_id"], safe=""))
    record["last_verify_verdict"] = {"http_status": status, "body": body}
    save()
    if status == 200 and (body.get("theorem_id") != record["theorem_id"]
                          or (body.get("submission_id") or body.get("id")) != record["submission_id"]):
        raise ValueError("Verification response belongs to another theorem or own submission")
    if status == 200 and body.get("status") == "ACCEPTED":
        record["accepted"] = True
        record["confirmed_proved"] = readback(record["theorem_id"]).get("status") == "Proved"
        save()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", default=str(DEFAULT_STAGE.relative_to(TASK)))
    parser.add_argument("--metadata-file", default=None)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--prepare-only", action="store_true", help="Default: prepare reviewed UTF-8 payloads offline")
    mode.add_argument("--advance", action="store_true", help="Explicitly use the platform API")
    mode.add_argument("--prepare-and-advance", action="store_true",
                      help="Explicit API mode: one readonly review, exact offline preparation, then one advance")
    args = parser.parse_args()
    stage = stage_path(args.stage)
    metadata_file = confined_file(args.metadata_file or "platform/formal-log-node-metadata/formalLog_packets_surjective_iff_truncated.json", base=TASK)
    if args.advance:
        result = prepare(stage, metadata_file, write=False)
    else:
        result = prepare(stage, metadata_file, write=True)
    stage, publication_dir, evidence, manifest, metadata, pins, payloads = result
    if args.advance or args.prepare_and_advance:
        advance(stage, publication_dir, evidence, manifest, metadata, pins, payloads)
    else:
        print(json.dumps({"prepared_offline": True, "network_used": False,
                          "theorem_name": manifest["theorem_name"],
                          "payload_sha256": pins["payload_sha256"],
                          "proposal_status": "Draft", "submission_ready": False,
                          "full_tree_ready": False}, ensure_ascii=False))


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, ValueError, TypeError, json.JSONDecodeError, StopIteration) as error:
        raise SystemExit("FormalLog proof-node publisher refused to proceed: " + str(error))
