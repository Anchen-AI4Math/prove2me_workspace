"""Freeze exact offline Prove2Me payloads for the certified n1 theorem.

This helper does not contact the platform. The root agent remains the sole
owner of any later API action.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import prepare_successive_approximations_n1 as inputs
import publish_standalone_platform_node as publisher
import validate_successive_approximations_n1 as validation

TASK, ROOT = inputs.TASK, inputs.ROOT
STAGE = inputs.STAGE
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


def verify_saved_evidence(manifest, cert):
    require(cert.get("validated") is True and cert.get("submission_ready") is False
            and cert.get("API_used") is False and cert.get("Lean_started_by_validator") is False,
            "n1 strict kernel certificate is not an offline validated certificate")
    require(cert.get("theorem_name") == inputs.NAME and cert.get("node") == inputs.KEY,
            "n1 certificate target identity differs")
    require(cert.get("stage_manifest_sha256") == sha(STAGE / "manifest.json")
            and cert.get("preparation_sha256") == sha(STAGE / "preparation.json")
            and cert.get("academic_metadata_sha256") == sha(STAGE / "academic-metadata.json"),
            "n1 certificate is stale against exact stage inputs")
    require(cert.get("child_certificate") == inputs.child_binding(),
            "n1 imported child certificate/OLean pin changed")
    for relative, expected in cert["implementation_hashes"].items():
        require(sha(TASK / relative) == expected, "n1 certificate implementation pin changed: " + relative)
    for relative, expected in cert["output_json_sha256"].items():
        require(sha(TASK / relative) == expected, "n1 kernel/proof-reference JSON pin changed: " + relative)
    for name, row in cert["preflights"].items():
        require(row["data"]["mode"] == "modecheck" and row["data"]["exit_code"] == 0
                and row["data"]["source_unchanged"] is True
                and 0 < row["data"]["seconds"] <= 300,
                "n1 preflight record is not a successful bounded modecheck: " + name)
        require(sha(TASK / row["record"]) == row["record_sha256"],
                "n1 preflight sidecar changed: " + name)
        require(sha(TASK / row["data"]["log"]) == row["data"]["log_sha256"],
                "n1 compiler log changed: " + name)
    # The c1 target compile's dependency sequence is the ordered import gate.
    c1 = cert["preflights"][Path(manifest["statement"]).name]["data"]
    ordered = [{"module": row["module"], "olean": row["path"],
                "sha256": row["sha256_before"], "stable_during_compile": row["stable_during_compile"]}
               for row in c1["dependency_oleans"]]
    child = cert["child_certificate"]
    matches = [row for row in ordered if row["module"] == child["module"]]
    require(len(matches) == 1 and matches[0]["sha256"] == child["output_olean_sha256"]
            and matches[0]["stable_during_compile"] is True,
            "ordered n1 import gate does not include the exact certified child OLean")
    require(cert["types_equal"] is True and cert["proof_axioms"] == "Std3"
            and cert["project_proof_references"] == [inputs.CHILD_NAME],
            "n1 kernel/reference/axiom gates changed")
    return ordered


def artifacts():
    inputs.check()
    manifest = read(STAGE / "manifest.json")
    cert = read(CERT)
    ordered_imports = verify_saved_evidence(manifest, cert)
    academic = read(STAGE / "academic-metadata.json")
    witness = cert["source_command_witness"]
    metadata = {
        "theorem_name": manifest["theorem_name"],
        "theorem_title": academic["theorem_title"],
        "natural_language_statement": academic["natural_language_statement"],
        "explanation": academic["explanation"],
        "tags": academic["tags"],
        "source_witness": {
            "source_commit": manifest["source_commit"],
            "source_url": academic["source_url"],
            "target_source_module": witness["source_module"],
            "target_source_graph_name": witness["source_graph_name"],
            "target_original_lines": witness["original_command_range"],
            "source_components": manifest["source_components"],
            "command_witness": witness,
        },
    }
    payloads = publisher.payloads(DEST, manifest, metadata)
    publish_meta = encode(metadata)
    pins = {
        "theorem_name": manifest["theorem_name"],
        "environment": publisher.ENV,
        "proposal_status": "Draft",
        "validation_certificate": validation.rel(CERT),
        "validation_sha256": sha(CERT),
        "manifest_sha256": sha(STAGE / "manifest.json"),
        "metadata_sha256": hashlib.sha256(publish_meta).hexdigest(),
        "publisher_sha256": sha(Path(publisher.__file__)),
        "wrapper_sha256": sha(SELF),
        "preparer_sha256": sha(Path(inputs.__file__)),
        "ordered_import_olean_gate": ordered_imports,
        "payload_sha256": {name: hashlib.sha256(data).hexdigest() for name, data in payloads.items()},
        "local_node_validated": True,
        "submission_ready": False,
        "full_tree_ready": False,
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "api_used": False,
    }
    return manifest, cert, metadata, publish_meta, payloads, pins


def prepare():
    manifest, cert, metadata, meta_bytes, payloads, pins = artifacts()
    exact(DEST / "manifest.json", (STAGE / "manifest.json").read_bytes())
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", meta_bytes)
    for name, data in payloads.items():
        exact(DEST / name, data)
    exact(DEST / "preparation.json", encode(pins))
    # Preserve the exact compiler logs and sidecars referenced by the certificate.
    sidecar = {name: {"record": row["record"], "record_sha256": row["record_sha256"],
                      "log": row["data"]["log"], "log_sha256": row["data"]["log_sha256"],
                      "seconds": row["data"]["seconds"], "timeout_seconds": row["data"]["timeout_seconds"]}
               for name, row in cert["preflights"].items()}
    exact(DEST / "compiler-sidecar.json", encode(sidecar))
    return {"prepared": True, "network_used": False, "stage": validation.rel(DEST),
            "payload_sha256": pins["payload_sha256"], "ordered_import_count": len(pins["ordered_import_olean_gate"]),
            "proposal_status": "Draft", "submission_ready": False}


def check():
    manifest, cert, metadata, meta_bytes, payloads, pins = artifacts()
    require(read(DEST / "preparation.json") == pins, "Offline publication pin record differs")
    require((DEST / "manifest.json").read_bytes() == (STAGE / "manifest.json").read_bytes()
            and (DEST / "validation.json").read_bytes() == CERT.read_bytes()
            and (DEST / "metadata.json").read_bytes() == meta_bytes,
            "Frozen publication evidence/metadata changed")
    for name, data in payloads.items():
        require((DEST / name).read_bytes() == data, "Frozen publication payload changed: " + name)
    return {"checked": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": pins["payload_sha256"], "submission_ready": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare_only else check(), ensure_ascii=False, indent=2))
