"""Prepare and explicitly publish one certified FormalLog proof node.

The default path is offline. ``--advance`` is the only path that reads API
credentials or makes requests. Each publication and verification POST is
preceded by a durable intent and is never retried after an uncertain result.
"""
from __future__ import annotations

import argparse
from bisect import bisect_right
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import validate_formal_log_node as checker
import formal_log_node_security_pins as securitypins

TASK, ROOT = checker.TASK, checker.ROOT
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
NODE_ROOT = TASK / "verification/flp3"
DEFAULT_STAGE = NODE_ROOT / "f1"
DEFAULT_METADATA = TASK / "platform/formal-log-node-metadata/liftSeries_eq_toMvPowerSeries.json"
COMMIT = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SECURITY_HELPER_SHA256 = "8adf3e87f2dc8f7b219cfd55364e3cca391307ffacd46fc6e8d3b12773da7a4f"


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
    if path.parent != NODE_ROOT.resolve() or not path.is_dir():
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
    return {
        "commit": COMMIT,
        "source_url": source_url,
        "source_command_witness": source,
        "facts": component["facts"],
        "facts_sha256": component["facts_sha256"],
    }


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
    if cert_path != (stage / "formal-node-validation.json").resolve():
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
    evidence = checker.validate_formal_node(stage)
    cert_path, cert = check_certificate(evidence, stage)
    manifest = evidence["manifest_data"]
    if manifest.get("source_commit") != COMMIT or manifest.get("formal_statement") is None:
        raise ValueError("Missing exact source commit or formal statement")
    if manifest.get("child_nodes") or manifest.get("node_generated_names"):
        raise ValueError("This publisher only accepts source-name nodes without unproved children or aliases")
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
        raise ValueError("Durable publication record does not bind the exact reviewed f1 target")

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
                or sha(stage / "formal-node-validation.json") != pins["certificate_sha256"]
                or sha(Path(__file__).resolve()) != pins["publisher_sha256"]
                or sha(Path(checker.__file__).resolve()) != pins["checker_sha256"]
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
    if not record.get("theorem_id") and not record.get("publication_intent"):
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
    if target.get("status") == "Proved":
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
    parser.add_argument("--metadata-file", default=str(DEFAULT_METADATA.relative_to(TASK)))
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--prepare-only", action="store_true", help="Default: prepare reviewed UTF-8 payloads offline")
    mode.add_argument("--advance", action="store_true", help="Explicitly use the platform API")
    args = parser.parse_args()
    stage = stage_path(args.stage)
    metadata_file = confined_file(args.metadata_file, base=TASK)
    if args.advance:
        result = prepare(stage, metadata_file, write=False)
    else:
        result = prepare(stage, metadata_file, write=True)
    stage, publication_dir, evidence, manifest, metadata, pins, payloads = result
    if args.advance:
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
