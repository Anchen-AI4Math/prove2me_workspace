"""Prepare and explicitly publish one certified FormalLog proof node.

The default path is offline. ``--advance`` is the only path that reads API
credentials or makes requests. Each publication and verification POST is
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

import validate_formal_log_successor_node as checker
import validate_formal_log_f3_complete_node_repaired as f3checker
import publish_formal_log_proof_node as frozenpublisher
import formal_log_successor_security_pins as securitypins

TASK, ROOT = checker.TASK, checker.ROOT
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
NODE_ROOT = TASK / "verification/flp3"
DEFAULT_STAGE = NODE_ROOT / "f2"
DEFAULT_METADATA = TASK / "platform/formal-log-node-metadata/logTail_mem_rationalWeightedIdeal.json"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SECURITY_HELPER_SHA256 = "198dc1620322fd0ec87db635f4dd761f0aedc8f77b3947ceb8b107679b32ff57"
BASELINE_CHECKER_SHA256 = "20f761f0d169c7af296faea379bb7547909abd56f79d0bdba03a207d7617bfb4"
F3_CHECKER_SHA256 = "e59db91b0c19026106294683e737c4f1060439d9aaccb9addd5502aa9e158a7a"
FROZEN_PUBLISHER_SHA256 = "dee52d38432a461d5520e7df2103640b72ea1ffe6bf2288a75891b7a45217913"
PARENT_ID = "6a63ca41-070c-4b8a-86e1-dc41228ab921"
PARENT_SUBMISSION = "fdd3e549-4921-432a-80a9-53b1e4fb46c1"


def parent_server_gate(request, record, save):
    """Fresh Accepted own-submission plus exact public Proved parent readback.

    This is deliberately a publication-only dependency. Offline certificates
    do not infer any remote status from the locally compiled child module.
    """
    path = TASK / "verification/flp3/f1/publication/publication.json"
    before = sha(path); parent = read(path)
    m = read(TASK / "verification/flp3/f1/manifest.json")
    accepted = parent.get("last_verify_verdict", {})
    if (parent.get("theorem_id") != PARENT_ID or parent.get("submission_id") != PARENT_SUBMISSION
            or parent.get("accepted") is not True or parent.get("confirmed_proved") is not True
            or accepted.get("http_status") != 200 or accepted.get("body", {}).get("status") != "ACCEPTED"
            or accepted.get("body", {}).get("theorem_id") != PARENT_ID
            or (accepted.get("body", {}).get("submission_id") or accepted.get("body", {}).get("id")) != PARENT_SUBMISSION
            or parent.get("preparation", {}).get("certificate_sha256") != sha(TASK / "verification/flp3/f1/formal-node-validation.json")
            or parent.get("target_binding", {}).get("manifest_sha256") != sha(TASK / "verification/flp3/f1/manifest.json")):
        raise ValueError("Parent lacks exact own Accepted record and certified target binding")
    status, body = request("GET", "/verify?submission_id=" + quote(PARENT_SUBMISSION, safe=""))
    record["parent_submission_readback"] = {"http_status": status, "body": body}
    save()
    if (status != 200 or body.get("status") != "ACCEPTED" or body.get("theorem_id") != PARENT_ID
            or (body.get("submission_id") or body.get("id")) != PARENT_SUBMISSION):
        raise ValueError("Fresh own parent submission is not Accepted for the exact parent")
    status, target = request("GET", "/theorems/" + quote(PARENT_ID, safe=""))
    record["parent_target_readback"] = {"http_status": status, "body": target}
    save()
    if (status != 200 or target.get("theorem_id") != PARENT_ID or target.get("status") != "Proved"
            or target.get("theorem_name") != m["theorem_name"] or target.get("mathlib_rev") != ENV
            or target.get("visibility") != "public" or target.get("deprecated_at") is not None
            or target.get("formal_statement") != m["formal_statement"] or target.get("preamble") != m["preamble"]
            or sha(path) != before):
        raise ValueError("Fresh exact parent readback or stable own Accepted record differs")
    record["parent_server_gate"] = {"validated": True, "own_accepted": True, "fresh_exact_proved": True,
        "theorem_id": PARENT_ID, "submission_id": PARENT_SUBMISSION, "publication_record_sha256": before,
        "checked_at_utc": datetime.now(timezone.utc).isoformat()}
    save()


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
    if path not in [(NODE_ROOT / n).resolve() for n in ["f2", "f3"]] or not path.is_dir():
        raise ValueError("Expected one FormalLog proof-node stage directly under verification/flp3")
    return path


def source_witness(manifest, evidence):
    """Bind the checker's separate raw source/port command spans without equating them."""
    if manifest.get("source_commit") != COMMIT or len(manifest.get("source_components", [])) != 1:
        raise ValueError("Expected the pinned single-component OpenAI FormalLog node")
    component = manifest["source_components"][0]
    if component.get("source_module") != "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation":
        raise ValueError("Unexpected FormalLog source component")
    original_path = confined_file(component["original_source"], base=ROOT)
    port_path = confined_file(component["source"], base=ROOT)
    facts_path = confined_file(component["facts"], base=ROOT)
    if (sha(original_path) != component["original_source_sha256"]
            or sha(port_path) != component["source_sha256"]
            or sha(facts_path) != component["facts_sha256"]):
        raise ValueError("Original, ported, or extraction-facts source bytes changed")
    source = evidence.get("source_command_witness")
    if not isinstance(source, dict):
        raise ValueError("Current formal certificate omits its source-command witness")
    if (source.get("source_module") != component["source_module"]
            or source.get("source_graph_name") != manifest["source_graph_name"]
            or source.get("original_source") != component["original_source"]
            or source.get("original_source_sha256") != component["original_source_sha256"]
            or source.get("port_source") != component["source"]
            or source.get("port_source_sha256") != component["source_sha256"]):
        raise ValueError("Certificate source-command witness differs from the pinned component")
    original_bytes, port_bytes = original_path.read_bytes(), port_path.read_bytes()
    original_range, port_range = source.get("original_command_range"), source.get("port_command_range")
    if (not isinstance(original_range, dict) or not isinstance(port_range, dict)
            or type(original_range.get("start")) is not int or type(original_range.get("end")) is not int
            or type(port_range.get("start")) is not int or type(port_range.get("end")) is not int):
        raise ValueError("Certificate source-command coordinates are malformed")
    oa, ob = original_range["start"], original_range["end"]
    pa, pb = port_range["start"], port_range["end"]
    if not (0 <= oa < ob <= len(original_bytes) and 0 <= pa < pb <= len(port_bytes)):
        raise ValueError("Certificate source-command coordinates exceed current source files")
    if (sha_bytes(original_bytes[oa:ob]) != source.get("original_command_sha256")
            or sha_bytes(port_bytes[pa:pb]) != source.get("port_command_sha256")
            or (original_bytes[oa:ob] == port_bytes[pa:pb]) != source.get("port_and_original_command_bytes_equal")):
        raise ValueError("Certificate raw source-command hashes do not replay against current source files")
    if (source.get("port_kernel_type_actual_source_snapshot_verified") is not True
            or source.get("original_command_boundaries_from_full_file_equal_line_correspondence") is not True):
        raise ValueError("Certificate source lineage lacks actual source typing or exact boundary evidence")
    line_offsets = [0]
    for line in original_bytes.splitlines(keepends=True):
        line_offsets.append(line_offsets[-1] + len(line))
    first = bisect_right(line_offsets, oa) 
    last = bisect_right(line_offsets, ob - 1)
    if first < 1 or last < first:
        raise ValueError("Certificate original source-command span has invalid line coordinates")
    source_url = ("https://github.com/openai/math/blob/" + COMMIT + "/lean/"
                  + component["source_module"].replace(".", "/") + f".lean#L{first}-L{last}")
    result = {
        "commit": COMMIT,
        "source_url": source_url,
        "source_command_witness": source,
        "facts": component["facts"],
        "facts_sha256": component["facts_sha256"],
        "inline_support_witnesses": [],
    }
    if manifest["public_inline_ci_requests"]:
        old_lines = original_bytes.splitlines(keepends=True); new_lines = port_bytes.splitlines(keepends=True)
        def offsets(lines):
            out = [0]
            for line in lines: out.append(out[-1] + len(line))
            return out
        old_offsets, new_offsets = offsets(old_lines), offsets(new_lines)
        old_contents = [line.rstrip(b"\r\n") for line in old_lines]
        new_contents = [line.rstrip(b"\r\n") for line in new_lines]
        matching = SequenceMatcher(None, old_contents, new_contents, autojunk=False).get_matching_blocks()
        def original_boundary(position):
            line = bisect_right(new_offsets, position) - 1
            for match in matching:
                if match.b <= line < match.b + match.size:
                    delta = position - new_offsets[line]
                    if delta > len(new_contents[line]): raise ValueError("Inline boundary inside line ending")
                    return old_offsets[match.a + line - match.b] + delta
            raise ValueError("Inline boundary lacks exact original line correspondence")
        result["inline_support_witnesses"] = []
        for row in manifest["public_inline_ci_requests"]:
            pa, pb = [row["source_command_range"][k]["offset"] for k in ["start", "end"]]
            oa, ob = original_boundary(pa), original_boundary(pb)
            first, last = bisect_right(old_offsets, oa), bisect_right(old_offsets, ob - 1)
            result["inline_support_witnesses"].append({
                "source_graph_name": row["source_graph_name"], "source_module": row["source_module"],
                "source_url": "https://github.com/openai/math/blob/" + COMMIT + "/lean/" + row["source_module"].replace(".", "/") + f".lean#L{first}-L{last}",
                "port_source": component["source"], "port_source_sha256": component["source_sha256"],
                "port_command_range": {"start": pa, "end": pb}, "port_command_sha256": sha_bytes(port_bytes[pa:pb]),
                "original_source": component["original_source"], "original_source_sha256": component["original_source_sha256"],
                "original_command_range": {"start": oa, "end": ob}, "original_command_sha256": sha_bytes(original_bytes[oa:ob]),
                "port_and_original_command_bytes_equal": port_bytes[pa:pb] == original_bytes[oa:ob],
                "purpose": "Referenced by the source proof of shiftMap_truncatedFormalJet to rewrite shiftMap applied to the lifted logarithm series."})
    return result


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


def check_certificate(evidence, stage):
    if evidence.get("validated") is not True or evidence.get("submission_ready") is not False:
        raise ValueError("Read-only formal node validation is missing or claims submission readiness")
    if evidence["stage"].resolve() != stage.resolve():
        raise ValueError("Current certificate belongs to a different stage")
    cert_path = confined_file(evidence["certificate"]["path"], base=TASK)
    if cert_path != (stage / ("successor-node-validation.json" if stage.name == "f2" else "complete-node-validation.json")).resolve():
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
    if sha(Path(checker.__file__)) != BASELINE_CHECKER_SHA256 or sha(Path(frozenpublisher.__file__)) != FROZEN_PUBLISHER_SHA256:
        raise ValueError("Frozen baseline checker/payload utility changed")
    if stage.name == "f3" and sha(Path(f3checker.__file__)) != F3_CHECKER_SHA256:
        raise ValueError("Frozen complete f3 checker changed")
    evidence = checker.validate_formal_successor_node(stage) if stage.name == "f2" else f3checker.validate_formal_f3_node(stage)
    cert_path, cert = check_certificate(evidence, stage)
    manifest = evidence["manifest_data"]
    if manifest.get("source_commit") != COMMIT or manifest.get("formal_statement") is None:
        raise ValueError("Missing exact source commit or formal statement")
    if manifest.get("node_generated_names") or len(manifest.get("child_nodes", {})) != 1 or len(cert.get("child_certificates", [])) != 1:
        raise ValueError("Successor requires one exact actual-certified proved f1 child without aliases")
    metadata_path = confined_file(metadata_value, base=TASK)
    metadata = read(metadata_path)
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
        "complete_checker_sha256": sha(Path(f3checker.__file__).resolve()) if stage.name == "f3" else None,
        "frozen_publisher_sha256": FROZEN_PUBLISHER_SHA256,
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
                or sha(Path(frozenpublisher.__file__).resolve()) != pins["frozen_publisher_sha256"]
                or stage.name == "f3" and sha(Path(f3checker.__file__).resolve()) != pins["complete_checker_sha256"]
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
    if status == 200 and body.get("theorem_id") != record["theorem_id"]:
        raise ValueError("Verification response belongs to another theorem")
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
    metadata_file = confined_file(args.metadata_file or ("platform/formal-log-node-metadata/" + ("logTail_mem_rationalWeightedIdeal.json" if stage.name == "f2" else "shiftMap_truncatedFormalJet.json")), base=TASK)
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
