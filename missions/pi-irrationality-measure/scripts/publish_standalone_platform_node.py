"""Prepare exact standalone-node payloads offline; --advance explicitly uses the API.

Each advance performs one publishing/verifying step or polls its durable job.
An uncertain POST intent is never retried automatically. Proposals stay Draft.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import validate_standalone_platform_node as validator

TASK, ROOT, DEST = validator.TASK, validator.ROOT, validator.DEST
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
TOOLCHAIN = "leanprover/lean4:v4.33.1"


def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def check_certificate(stage, manifest):
    closure, filenames = validator.check_stage(stage, manifest)
    path = (ROOT / manifest.get("validation", "")).resolve()
    if (not manifest.get("validated") or not manifest.get("local_standalone_validated")
            or path != stage / "validation.json" or validator.sha(path) != manifest.get("validation_sha256")):
        raise ValueError("This exact standalone node has no current local validation certificate")
    certificate = validator.read(path)
    if (not certificate.get("validated") or not certificate.get("local_standalone_validated")
            or not certificate.get("kernel_types_equal") or not certificate.get("standard_axioms_only")
            or certificate.get("submission_ready") is not False or certificate.get("full_tree_ready") is not False
            or certificate.get("closure") != closure
            or certificate.get("implementation_sha256") != validator.implementation_pins()):
        raise ValueError("Standalone validation certificate is stale or incomplete")
    lineage = certificate.get("recertification")
    if certificate.get("certification_mode") == "existing-compilation":
        if not isinstance(lineage, dict):
            raise ValueError("Reused compilation has no preserved certification lineage")
        prior_path = (ROOT / lineage["attempt"]).resolve()
        if prior_path.parent != stage or validator.sha(prior_path) != lineage["attempt_sha256"]:
            raise ValueError("Preserved prior compilation attempt changed")
        prior = validator.read(prior_path)
        current_pins = certificate["implementation_sha256"]
        old_pins = lineage["compiled_implementation_sha256"]
        if (prior["implementation_sha256"] != old_pins or set(old_pins) != set(current_pins)
                or lineage["recertification_implementation_sha256"] != current_pins
                or lineage["recertification_parser_sha256"] != current_pins["validate_standalone_platform_node.py"]
                or not lineage["compilation_reused"] or lineage["new_Lean_compilation_run"] is not False
                or any(old_pins[key] != current_pins[key] for key in current_pins
                       if key != "validate_standalone_platform_node.py")
                or prior["preflights"] != certificate["preflights"]
                or prior["type_json_sha256"] != {"original-type.json": certificate["original_type_sha256"],
                                               "generated-type.json": certificate["generated_type_sha256"]}):
            raise ValueError("Re-certification differs from the preserved successful compilation")
        if old_pins["validate_standalone_platform_node.py"] != current_pins["validate_standalone_platform_node.py"]:
            backup = (ROOT / prior["prior_validator_source"]).resolve()
            if (prior.get("capture_scope") != "post-compilation-before-parser-repair"
                    or backup.parent != stage
                    or validator.sha(backup) != old_pins["validate_standalone_platform_node.py"]
                    or prior["prior_validator_source_sha256"] != validator.sha(backup)):
                raise ValueError("Changed parser has no exact preserved source witness")
    elif certificate.get("certification_mode") != "new-compilation" or lineage is not None:
        raise ValueError("Unknown local certification mode")
    for field in ("input_hashes", "source_components", "source_graph_sha256", "runtime_sha256",
                  "generator_sha256", "statement_sha256", "solution_sha256", "snapshot_sha256",
                  "snapshot_core_sha256", "provisional"):
        if certificate.get(field) != manifest[field]:
            raise ValueError("Certificate binds a different stage: " + field)
    for filename, field in (("original-type.json", "original_type_sha256"),
                            ("generated-type.json", "generated_type_sha256")):
        if validator.sha(stage / filename) != certificate[field]:
            raise ValueError("Certified kernel JSON changed: " + filename)
    records = certificate["preflights"]
    if set(records) != set(filenames):
        raise ValueError("Certificate must contain exactly four preflights")
    for filename, record in records.items():
        log = (ROOT / record["log"]).resolve()
        if (record["exit_code"] or record["original_exit_code"] or record["timed_out"]
                or not record["source_unchanged"] or record["mode"] != "verification"
                or record["timeout_seconds"] != 300 or not 0 < record["seconds"] <= 300
                or record["runtime_sha256"] != manifest["runtime_sha256"]
                or (ROOT / record["source"]).resolve() != stage / filename
                or validator.sha(stage / filename) != record["source_sha256"]
                or not log.is_relative_to(DEST.resolve()) or validator.sha(log) != record["log_sha256"]
                or validator.read(stage / (filename + ".preflight.json")) != record):
            raise ValueError("Stale/failed strict preflight evidence: " + filename)
    original = validator.read(stage / "original-type.json")
    generated = validator.read(stage / "generated-type.json")
    name = manifest["source_graph_name"]
    if (len(original) != 1 or original[0]["name"] != name or len(generated) != 2
            or {row["name"] for row in generated} != {name, "solution"}):
        raise ValueError("Unexpected kernel snapshot declarations")
    for row in generated:
        if (len(row["levelParams"]) != len(original[0]["levelParams"])
                or validator.normalize_type(row) != validator.normalize_type(original[0])):
            raise ValueError("Source/target/solution kernel types differ")
    graph = {json.loads(line)["name"] for line in (DEST / "decl_graph.jsonl").read_bytes().splitlines()}
    solution = next(row for row in generated if row["name"] == "solution")
    refs = validator.snapshot_project_constants(solution["type"], graph)
    refs |= validator.snapshot_project_constants(solution["value"], graph)
    if not refs <= set(closure["inline_declarations"]):
        raise ValueError("Solution imports a missing project declaration or its target stub")
    axioms = {
        "source": validator.audit_axioms(ROOT / records["SnapshotOriginal.lean"]["log"], name),
        "snapshot_solution": validator.audit_axioms(ROOT / records["SnapshotGenerated.lean"]["log"], "solution"),
        "exact_solution": validator.audit_axioms(ROOT / records[Path(manifest["solution"]).name]["log"], "solution")}
    if axioms != certificate["axioms"]:
        raise ValueError("Recorded axiom audit differs from exact logs")
    return certificate


def source_witness(manifest):
    generator = validator.nodegen.NodeGenerator(bool(manifest["provisional"]))
    unit = generator.g.units[manifest["node"]]
    origin = manifest["source_components"][0]
    first, last = unit["start"]["line"], unit["end"]["line"]
    original = (ROOT / origin["original_source"]).read_bytes().splitlines(keepends=True)
    original_command = b"".join(original[first-1:last]).decode("utf-8").replace("\r\n", "\n").rstrip("\n")
    port = (ROOT / origin["source"]).read_bytes()
    port_command = port[unit["start"]["offset"]:unit["end"]["offset"]].decode("utf-8").replace("\r\n", "\n").rstrip("\n")
    if original_command != port_command:
        raise ValueError("Source line witness differs from the authoritative port declaration command")
    relative = origin["source_module"].replace(".", "/") + ".lean"
    url = "https://github.com/openai/math/blob/" + manifest["source_commit"] + "/lean/" + relative + f"#L{first}-L{last}"
    return {"commit": manifest["source_commit"], "source_url": url,
            "source_module": origin["source_module"], "source_range": {"start": unit["start"], "end": unit["end"]},
            "original_source": origin["original_source"], "original_source_sha256": origin["original_source_sha256"],
            "port_source": origin["source"], "port_source_sha256": origin["source_sha256"],
            "facts": origin["facts"], "facts_sha256": origin["facts_sha256"]}


def check_metadata(metadata, manifest):
    expected_fields = {"theorem_name", "theorem_title", "natural_language_statement", "tags", "explanation", "source_witness"}
    if set(metadata) != expected_fields or metadata["theorem_name"] != manifest["theorem_name"]:
        raise ValueError("Metadata keys/target identity differ")
    for field in ("theorem_title", "natural_language_statement", "explanation"):
        if not isinstance(metadata[field], str) or not metadata[field].strip():
            raise ValueError("Missing metadata text: " + field)
    tags = metadata["tags"]
    if (not isinstance(tags, list) or not tags or any(not isinstance(tag, str) or not tag.strip() for tag in tags)
            or len(tags) != len(set(tags))):
        raise ValueError("Metadata needs a nonempty unique list of tags")
    if metadata["source_witness"] != source_witness(manifest):
        raise ValueError("Metadata source commit, AST range or source witness changed")


def payloads(stage, manifest, metadata):
    problem = {"theorem_name": manifest["theorem_name"], "preamble": manifest["preamble"],
               "formal_statement": manifest["formal_statement"], "source": metadata["source_witness"]["source_url"],
               **{field: metadata[field] for field in ("theorem_title", "natural_language_statement", "tags")}}
    publish = {"problems": [problem], "env": ENV, "private": False}
    # /verify consumes multipart, not this JSON descriptor. Only theorem_id is
    # late-bound after an exact server readback; all proof bytes are fixed here.
    verify = {"target_theorem_name": manifest["theorem_name"], "env": ENV, "theorem_id": None,
              "theorem_id_binding": "exact public theorem name/environment/preamble/formal_statement readback",
              "proof_type": "prove", "explanation": metadata["explanation"],
              "file": {"filename": Path(manifest["solution"]).name,
                       "source": manifest["solution"], "sha256": manifest["solution_sha256"],
                       "utf8": (ROOT / manifest["solution"]).read_bytes().decode("utf-8")}}
    return {"publish-payload.json": encode(publish), "verification-payload.json": encode(verify)}


def prepare(stage, manifest, write=True):
    check_certificate(stage, manifest)
    metadata_path = stage / "metadata.json"
    metadata = validator.read(metadata_path)
    check_metadata(metadata, manifest)
    prepared = payloads(stage, manifest, metadata)
    pins = {"theorem_name": manifest["theorem_name"], "environment": ENV, "proposal_status": "Draft",
            "manifest_sha256": validator.sha(stage / "manifest.json"),
            "validation_sha256": manifest["validation_sha256"], "metadata_sha256": validator.sha(metadata_path),
            "publisher_sha256": validator.sha(Path(__file__)),
            "api_client_sha256": validator.sha(ROOT / "scripts/p2m_api.py"),
            "payload_sha256": {filename: sha_bytes(data) for filename, data in prepared.items()},
            "local_node_validated": True, "submission_ready": False, "full_tree_ready": False,
            "verification_payload_is_offline_descriptor": True,
            "verification_theorem_id_late_bound_only": True}
    record_path = stage / "publication.json"
    if record_path.exists():
        record = validator.read(record_path)
        if record.get("preparation") != pins:
            raise ValueError("Prepared metadata/certificate/payload changed after a publication record was created")
    validator.strict_inputs(manifest)
    if not write:
        preparation_path = stage / "preparation.json"
        if not preparation_path.exists() or preparation_path.read_bytes() != encode(pins):
            raise ValueError("Run offline --prepare-only and review the current payloads before --advance")
        for filename, data in prepared.items():
            if not (stage / filename).exists() or (stage / filename).read_bytes() != data:
                raise ValueError("Reviewed payload changed; no network action taken: " + filename)
        return metadata, pins, prepared
    for filename, data in prepared.items():
        path = stage / filename
        if not path.exists() or path.read_bytes() != data:
            path.write_bytes(data)
    (stage / "preparation.json").write_bytes(encode(pins))
    return metadata, pins, prepared


def advance(stage, manifest, metadata, pins, prepared):
    # Importing the API helper and obtaining credentials occur only in this
    # explicit branch. Default preparation never performs GET, POST or refresh.
    spec = importlib.util.spec_from_file_location("standalone_p2m", ROOT / "scripts/p2m_api.py")
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    record_path = stage / "publication.json"
    record = validator.read(record_path) if record_path.exists() else {
        "theorem_name": manifest["theorem_name"], "preparation": pins,
        "advance_requested_at_utc": datetime.now(timezone.utc).isoformat(), "proposal_status": "Draft"}

    def save():
        record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
        record_path.write_bytes(encode(record))

    def guard():
        validator.strict_inputs(manifest)
        if (validator.sha(stage / "manifest.json") != pins["manifest_sha256"]
                or validator.sha(stage / "validation.json") != pins["validation_sha256"]
                or validator.sha(stage / "metadata.json") != pins["metadata_sha256"]
                or validator.sha(Path(__file__)) != pins["publisher_sha256"]
                or validator.sha(ROOT / "scripts/p2m_api.py") != pins["api_client_sha256"]):
            raise ValueError("Reviewed publication evidence changed")
        for filename, expected in pins["payload_sha256"].items():
            if validator.sha(stage / filename) != expected:
                raise ValueError("Reviewed exact payload changed")

    def request(method, path, **kwargs):
        guard()
        status, body = api._request(method, path, token=api.get_token(), **kwargs)
        guard()
        return status, json.loads(body)

    def readback(theorem_id):
        status, existing = request("GET", "/theorems/" + theorem_id)
        record["target_readback"] = {"http_status": status, "body": existing}
        save()
        if (status != 200 or existing.get("theorem_id") != theorem_id
                or existing.get("theorem_name") != manifest["theorem_name"]
                or existing.get("mathlib_rev") != ENV or existing.get("visibility") != "public"
                or existing.get("deprecated_at") is not None
                or existing.get("formal_statement") != manifest["formal_statement"]
                or existing.get("preamble") != manifest["preamble"]):
            raise ValueError("Existing target identity/text/environment/visibility differs")
        return existing

    save()
    if not record.get("theorem_id") and not record.get("publish_intent"):
        matches, offset = [], 0
        while True:
            status, body = request("GET", "/theorems?theorem_name=" + quote(manifest["theorem_name"]) +
                                   f"&env={ENV}&limit=100&offset={offset}")
            if status != 200:
                raise ValueError("Exact-name lookup failed; nothing posted")
            page = body["theorems"]
            matches.extend(item for item in page if item["theorem_name"] == manifest["theorem_name"])
            offset += len(page)
            if offset >= body["total"]:
                break
            if not page:
                raise ValueError("Incomplete exact-name pagination; nothing posted")
        if matches:
            if len(matches) != 1:
                raise ValueError("Ambiguous existing target; nothing posted")
            existing = readback(matches[0]["theorem_id"])
            record["theorem_id"] = existing["theorem_id"]
            save()
        else:
            status, environments = request("GET", "/environments")
            if status != 200 or not any(item.get("mathlib_rev") == ENV and item.get("toolchain") == TOOLCHAIN
                                        for item in environments.get("environments", [])):
                raise ValueError("Pinned platform environment unavailable; nothing posted")
            record["publish_intent"] = {"at_utc": datetime.now(timezone.utc).isoformat(),
                                        "payload_sha256": pins["payload_sha256"]["publish-payload.json"]}
            save()
            status, body = request("POST", "/submit-problem", raw_body=prepared["publish-payload.json"])
            record["publish_response"] = {"http_status": status, "body": body}
            jobs = body.get("jobs", [])
            if (status == 202 and not body.get("errors") and len(jobs) == 1
                    and jobs[0].get("name") == manifest["theorem_name"] and jobs[0].get("job_id")):
                record["job_id"] = jobs[0]["job_id"]
            save()
            print(json.dumps(record["publish_response"], ensure_ascii=False))
            return
    if not record.get("theorem_id"):
        if not record.get("job_id"):
            raise ValueError("Uncertain publication POST recorded; inspect it before another POST")
        status, body = request("GET", "/publish-jobs/" + record["job_id"])
        record["last_publish_verdict"] = {"http_status": status, "body": body}
        if status == 200 and body.get("status") == "PUBLISHED":
            record["theorem_id"] = body["theorem_id"]
        save()
        if not record.get("theorem_id"):
            print(json.dumps(record["last_publish_verdict"], ensure_ascii=False))
            return
    if not record.get("submission_id"):
        existing = readback(record["theorem_id"])
        if existing.get("status") == "Proved":
            record["confirmed_proved"] = True
            record["existing_proved_reused"] = True
            save()
            print(json.dumps({"theorem_id": record["theorem_id"], "status": "Proved", "reused": True}))
            return
        if record.get("verify_intent"):
            raise ValueError("Uncertain verification POST recorded; inspect it before another POST")
        descriptor = json.loads(prepared["verification-payload.json"])
        payload, ctype = api._multipart(
            {"theorem_id": record["theorem_id"], "proof_type": descriptor["proof_type"],
             "explanation": descriptor["explanation"]},
            {"file": (descriptor["file"]["filename"], descriptor["file"]["utf8"].encode("utf-8"))})
        multipart_path = stage / "verification-request.multipart"
        multipart_path.write_bytes(payload)
        record["verify_intent"] = {"at_utc": datetime.now(timezone.utc).isoformat(),
                                   "theorem_id": record["theorem_id"], "multipart_sha256": sha_bytes(payload),
                                   "content_type": ctype, "solution_sha256": manifest["solution_sha256"],
                                   "descriptor_sha256": pins["payload_sha256"]["verification-payload.json"]}
        save()
        status, body = request("POST", "/verify", raw_body=payload, ctype=ctype)
        record["verify_response"] = {"http_status": status, "body": body}
        if status in (200, 202) and body.get("status") in {"PENDING", "COMPILING"}:
            record["submission_id"] = body.get("submission_id") or body.get("id")
        save()
        print(json.dumps(record["verify_response"], ensure_ascii=False))
    else:
        status, body = request("GET", "/verify?submission_id=" + record["submission_id"])
        record["last_verify_verdict"] = {"http_status": status, "body": body}
        save()
        if status == 200 and body.get("theorem_id") != record["theorem_id"]:
            raise ValueError("Verification response belongs to a different theorem")
        if status == 200 and body.get("status") == "ACCEPTED":
            record["confirmed_proved"] = readback(record["theorem_id"]).get("status") == "Proved"
            save()
        print(json.dumps(record["last_verify_verdict"], ensure_ascii=False))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", help="Standalone node slug or node directory")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--prepare-only", action="store_true", help="Default: prepare/review exact payloads without networking")
    mode.add_argument("--advance", action="store_true", help="Explicitly advance the durable public publication workflow")
    args = parser.parse_args()
    stage = validator.stage_path(args.stage)
    manifest = validator.read(stage / "manifest.json")
    metadata, pins, prepared = prepare(stage, manifest, write=not args.advance)
    if args.advance:
        advance(stage, manifest, metadata, pins, prepared)
    else:
        print(json.dumps({"theorem_name": manifest["theorem_name"], "prepared": True,
                          "network_used": False, "payload_sha256": pins["payload_sha256"],
                          "submission_ready": False, "proposal_status": "Draft",
                          "verification_theorem_id_late_bound_only": True}))


if __name__ == "__main__":
    main()
