"""Freeze the strict offline Draft payload for the certified Parameters p1 node."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import prepare_pi_parameters_p1j as inputs
import certify_pi_parameters_p1j_existing as validation
import publish_standalone_platform_node as publisher

TASK, ROOT, STAGE = inputs.TASK, inputs.ROOT, inputs.STAGE
CERT = validation.CERT
DEST = STAGE / "publication-draft"
SELF = Path(__file__).resolve()


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encode(value) -> bytes:
    return publisher.encode(value)


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def exact(path: Path, data: bytes) -> None:
    if path.exists():
        if path.read_bytes() != data:
            raise ValueError("Frozen publication artifact differs; preserve it before replacement: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def artifacts():
    inputs.check_outputs(inputs.stage_files())
    manifest = read(STAGE / "manifest.json")
    cert = read(CERT)
    require(cert.get("validated") is True and cert.get("submission_ready") is False
            and cert.get("API_used") is False and cert.get("Lean_started_by_consumer") is False,
            "p1 strict certificate is not an offline validated Draft certificate")
    require(cert.get("theorem_name") == inputs.NAME and cert.get("node") == manifest.get("node"),
            "p1 certificate target identity differs")
    require(cert.get("stage_manifest_sha256") == sha(STAGE / "manifest.json")
            and cert.get("preparation_sha256") == sha(STAGE / "preparation.json")
            and manifest.get("academic_metadata_sha256") == sha(STAGE / "academic-metadata.json"),
            "p1 certificate is stale against exact stage inputs")
    statement = STAGE / "Theorems/Thm_OAI_PiExponent_exists_parameters.lean"
    assembled = (manifest["preamble"] + manifest["formal_statement"]).encode("utf-8")
    require(statement.read_bytes() == assembled,
            "Exact compiled theorem bytes differ from manifest.preamble + manifest.formal_statement")
    require(cert["compiled_Thm_exact_assembly"]["byte_equal"] is True
            and hashlib.sha256(assembled).hexdigest() == cert["compiled_Thm_exact_assembly"]["compiled_file_sha256"],
            "Compiled statement assembly digest differs from strict certificate")
    for relative, expected in cert["implementation_hashes"].items():
        require(sha(TASK / relative) == expected, "Certificate implementation changed: " + relative)
    for relative, expected in cert["output_json_sha256"].items():
        require(sha(TASK / relative) == expected, "Kernel output changed: " + relative)
    require(all(row["equal"] is True for row in cert["type_equalities"])
            and set(cert["solution_axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
            and cert["max_file_seconds"] <= 300,
            "Actual type, axiom or compiler budget gate changed")
    academic = read(STAGE / "academic-metadata.json")
    metadata = {
        "theorem_name": manifest["theorem_name"],
        "theorem_title": academic["theorem_title"],
        "natural_language_statement": academic["natural_language_statement"],
        "explanation": academic["explanation"],
        "tags": academic["tags"],
        "source_witness": {
            "source_commit": manifest["source_commit"],
            "source_url": academic["source_url"],
            "target_source_module": manifest["source_module"],
            "target_source_graph_name": manifest["theorem_name"],
            "target_original_lines": next(
                row["range"] for row in read(STAGE / "source-ast-witness.json")["commands"]
                if row["name"] == manifest["theorem_name"]
            ),
            "command_witness": read(STAGE / "source-ast-witness.json"),
        },
    }
    payloads = publisher.payloads(DEST, manifest, metadata)
    metadata_bytes = encode(metadata)
    pins = {
        "theorem_name": manifest["theorem_name"],
        "environment": publisher.ENV,
        "proposal_status": "Draft",
        "validation_certificate": validation.rel(CERT),
        "validation_sha256": sha(CERT),
        "manifest_sha256": sha(STAGE / "manifest.json"),
        "metadata_sha256": hashlib.sha256(metadata_bytes).hexdigest(),
        "publisher_sha256": sha(Path(publisher.__file__)),
        "wrapper_sha256": sha(SELF),
        "preparer_sha256": sha(Path(inputs.__file__)),
        "strict_consumer_sha256": sha(Path(validation.__file__)),
        "compiled_statement_sha256": hashlib.sha256(assembled).hexdigest(),
        "payload_sha256": {name: hashlib.sha256(data).hexdigest() for name, data in payloads.items()},
        "local_node_validated": True,
        "submission_ready": False,
        "full_tree_ready": False,
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "api_used": False,
    }
    return manifest, cert, metadata_bytes, payloads, pins


def prepare():
    manifest, cert, metadata, payloads, pins = artifacts()
    exact(DEST / "manifest.json", (STAGE / "manifest.json").read_bytes())
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", metadata)
    for name, data in payloads.items():
        exact(DEST / name, data)
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": pins["payload_sha256"], "submission_ready": False}


def check():
    _, _, metadata, payloads, pins = artifacts()
    require(read(DEST / "preparation.json") == pins, "Frozen p1 publication pin record differs")
    require((DEST / "manifest.json").read_bytes() == (STAGE / "manifest.json").read_bytes()
            and (DEST / "validation.json").read_bytes() == CERT.read_bytes()
            and (DEST / "metadata.json").read_bytes() == metadata,
            "Frozen p1 publication evidence or metadata changed")
    for name, data in payloads.items():
        require((DEST / name).read_bytes() == data, "Frozen p1 publication payload changed: " + name)
    return {"checked": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": pins["payload_sha256"], "submission_ready": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare_only else check(), ensure_ascii=False, indent=2))
