"""Freeze the minimal ap5/n3 publication payloads without network access."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import publish_standalone_platform_node as publisher
import stage_normalized_successive_approximations_n3 as inputs
import validate_normalized_successive_approximations_n3 as validation

TASK, ROOT, STAGE = inputs.TASK, inputs.ROOT, inputs.STAGE
DEST = STAGE / "publication-draft"
CERT = validation.CERT
SELF = Path(__file__).resolve()


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encode(value) -> bytes:
    return publisher.encode(value)


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def exact(path: Path, raw: bytes) -> None:
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen n3 publication artifact differs; preserve it first: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def static_artifacts():
    inputs.check()
    stage_manifest = read(STAGE / "manifest.json")
    academic = read(STAGE / "academic-metadata.json")
    require(set(academic) == {"theorem_title", "natural_language_statement", "explanation",
                              "tags", "source_commit", "source_url"},
            "Academic metadata must project to exactly six platform fields")
    require(academic["source_commit"] == inputs.SOURCE_COMMIT
            and academic["source_url"] == inputs.SOURCE_URL,
            "Academic source provenance differs")
    statement = ROOT / stage_manifest["statement"]
    assembled = (stage_manifest["wire_preamble"] + stage_manifest["formal_statement"]).encode("utf-8")
    require(statement.read_bytes() == assembled
            and hashlib.sha256(assembled).hexdigest() == stage_manifest["assembled_wire_theorem_sha256"],
            "Wire statement is not the exact staged modecheck source")
    metadata = {
        "theorem_name": stage_manifest["theorem_name"],
        "theorem_title": academic["theorem_title"],
        "natural_language_statement": academic["natural_language_statement"],
        "explanation": academic["explanation"],
        "tags": academic["tags"],
        "source_witness": {
            "source_commit": inputs.SOURCE_COMMIT,
            "source_url": inputs.SOURCE_URL,
            "source_module": inputs.SOURCE_MODULE,
            "source_unit": stage_manifest["source_unit"],
            "source_command": stage_manifest["source_command"],
            "source_command_sha256": stage_manifest["source_command_sha256"],
            "source_components": stage_manifest["source_components"],
            "mathematical_role": stage_manifest["mathematical_role"],
        },
    }
    publication_manifest = dict(stage_manifest)
    publication_manifest["preamble"] = publication_manifest["wire_preamble"]
    payloads = publisher.payloads(DEST, publication_manifest, metadata)
    publish = json.loads(payloads["publish-payload.json"])
    problem = publish["problems"][0]
    require((problem["preamble"] + problem["formal_statement"]).encode("utf-8") == statement.read_bytes(),
            "Frozen publish payload does not carry the exact compiled statement bytes")
    verify = json.loads(payloads["verification-payload.json"])
    solution = ROOT / stage_manifest["solution"]
    require(verify["file"]["sha256"] == sha(solution)
            and verify["file"]["utf8"].encode("utf-8") == solution.read_bytes(),
            "Frozen verification payload does not carry the literal solution bytes")
    return stage_manifest, publication_manifest, metadata, payloads, assembled


def pending():
    manifest, _, metadata, payloads, assembled = static_artifacts()
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    pins = {
        "schema_version": 1,
        "artifact_kind": "ap5-n3-pending-offline-publication",
        "theorem_name": inputs.NAME,
        "environment": publisher.ENV,
        "proposal_status": "Draft",
        "stage_manifest_sha256_at_pending_freeze": sha(STAGE / "manifest.json"),
        "wire_theorem_sha256": hashlib.sha256(assembled).hexdigest(),
        "solution_sha256": manifest["solution_sha256"],
        "metadata_sha256": sha(DEST / "metadata.json"),
        "payload_sha256": {name: hashlib.sha256(raw).hexdigest() for name, raw in payloads.items()},
        "strict_validation_pending": True,
        "network_used": False,
        "API_used": False,
        "submission_ready": False,
    }
    exact(DEST / "pending-preparation.json", encode(pins))
    return {"prepared": True, "pending_validation": True, "network_used": False,
            "payload_sha256": pins["payload_sha256"], "proposal_status": "Draft"}


def verify_certificate(stage_manifest: dict, cert: dict) -> list[dict]:
    require(cert.get("validated") is True and cert.get("submission_ready") is False
            and cert.get("API_used") is False and cert.get("Lean_started_by_validator") is False,
            "n3 certificate is not a strict offline validation")
    require(cert.get("node") == inputs.KEY and cert.get("theorem_name") == inputs.NAME,
            "n3 certificate identity differs")
    require(cert.get("manifest_sha256") == sha(STAGE / "manifest.json")
            and cert.get("preparation_sha256") == sha(STAGE / "preparation.json")
            and cert.get("academic_metadata_sha256") == sha(STAGE / "academic-metadata.json"),
            "n3 certificate is stale against the stage")
    require(cert.get("formal_types_equal") is True and cert.get("proof_axioms") == "Std3"
            and cert.get("project_proof_references") == sorted(
                child["theorem_name"] for child in cert["child_certificates"]),
            "n3 type/Std3/proof-reference gates differ")
    statement = cert.get("statement_placeholder_audit", {})
    require(statement.get("exact_wire_bytes_equal") is True
            and statement.get("successful_actual_modecheck") is True
            and statement.get("placeholder_proof") == "sorryAx"
            and statement.get("explicit_sorry_count") == 1
            and statement.get("additional_axiom_or_opaque_declarations") == 0
            and statement.get("olean_emitted") is False
            and statement.get("imported_by_proof_artifact") is False,
            "n3 statement placeholder/wire gate differs")
    require(cert.get("publication_assembly_guard", {}).get("satisfied") is True,
            "n3 compiled-statement publication assembly gate is not satisfied")
    for relative, expected in cert["implementation_hashes"].items():
        require(sha(TASK / relative) == expected, "n3 validation implementation changed: " + relative)
    for relative, expected in cert["output_json_sha256"].items():
        require(sha(TASK / relative) == expected, "n3 output JSON changed: " + relative)
    for child in cert["child_certificates"]:
        require(child["ready"] is True and child["validated"] is True
                and sha(TASK / child["certificate"]) == child["certificate_sha256"]
                and sha(TASK / child["output_olean"]) == child["output_olean_sha256"],
                "n3 actual proved-child binding changed")
    ordered = cert["preflights"][
        "Theorems/Thm_OAI_PiExponent_exists_normalized_successive_approximations.lean"]["data"][
            "dependency_oleans"]
    gate, seen = [], set()
    for row in ordered:
        require(row["module"] not in seen and row["stable_during_compile"] is True
                and row["sha256_before"] == row["sha256_after"],
                "n3 ordered import OLean gate differs")
        seen.add(row["module"])
        path = Path(row["path"])
        require(path.is_file() and sha(path) == row["sha256_before"],
                "n3 ordered imported OLean changed: " + row["module"])
        gate.append({"module": row["module"], "path": row["path"],
                     "sha256": row["sha256_before"], "stable_during_compile": True})
    by_module = {row["module"]: row for row in gate}
    for child in cert["child_certificates"]:
        require(by_module.get(child["module"], {}).get("sha256") == child["output_olean_sha256"],
                "n3 statement compile omitted exact child OLean: " + child["module"])
    return gate


def artifacts():
    stage_manifest, publication_manifest, metadata, payloads, assembled = static_artifacts()
    require(CERT.is_file(), "Run the five bounded preflights and strict n3 validator first")
    cert = read(CERT)
    ordered = verify_certificate(stage_manifest, cert)
    pins = {
        "theorem_name": inputs.NAME,
        "environment": publisher.ENV,
        "proposal_status": "Draft",
        "validation_certificate": rel(CERT),
        "validation_sha256": sha(CERT),
        "stage_manifest_sha256": sha(STAGE / "manifest.json"),
        "publication_manifest_sha256": hashlib.sha256(encode(publication_manifest)).hexdigest(),
        "metadata_sha256": hashlib.sha256(encode(metadata)).hexdigest(),
        "offline_wrapper_sha256": sha(SELF),
        "publisher_sha256": sha(Path(publisher.__file__)),
        "wire_theorem_sha256": hashlib.sha256(assembled).hexdigest(),
        "ordered_import_olean_gate": ordered,
        "payload_sha256": {name: hashlib.sha256(raw).hexdigest() for name, raw in payloads.items()},
        "local_node_validated": True,
        "compiled_wire_exact": True,
        "submission_ready": False,
        "full_tree_ready": False,
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "api_used": False,
    }
    return publication_manifest, cert, metadata, payloads, pins, assembled


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def prepare():
    manifest, cert, metadata, payloads, pins, assembled = artifacts()
    require((DEST / "pending-preparation.json").is_file(),
            "Run --prepare-pending before child-bound validation")
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    sidecars = {name: {"record": row["record"], "record_sha256": row["record_sha256"],
                       "log": row["data"]["log"], "log_sha256": row["data"]["log_sha256"],
                       "seconds": row["data"]["seconds"],
                       "timeout_seconds": row["data"]["timeout_seconds"]}
                for name, row in cert["preflights"].items()}
    exact(DEST / "compiler-sidecar.json", encode(sidecars))
    exact(DEST / "assembly-certificate.json", encode(cert["statement_placeholder_audit"]))
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": pins["payload_sha256"], "submission_ready": False}


def check():
    manifest, cert, metadata, payloads, pins, assembled = artifacts()
    require((DEST / "manifest.json").read_bytes() == encode(manifest)
            and (DEST / "validation.json").read_bytes() == CERT.read_bytes()
            and (DEST / "metadata.json").read_bytes() == encode(metadata)
            and (DEST / "wire-theorem-source.lean").read_bytes() == assembled
            and read(DEST / "preparation.json") == pins,
            "Frozen n3 publication evidence differs")
    for name, raw in payloads.items():
        require((DEST / name).read_bytes() == raw, "Frozen n3 payload differs: " + name)
    return {"checked": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": pins["payload_sha256"], "submission_ready": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare-pending", action="store_true")
    group.add_argument("--prepare-only", action="store_true")
    group.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if args.prepare_pending:
        result = pending()
    elif args.prepare_only:
        result = prepare()
    else:
        result = check()
    print(json.dumps(result, ensure_ascii=False, indent=2))
