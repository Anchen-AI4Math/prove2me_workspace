"""Freeze offline publication payloads for the strict n2z node certificate."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import prepare_successive_approximations_n2z as inputs
import publish_standalone_platform_node as publisher
import validate_successive_approximations_n2z as validation

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
            raise ValueError("Frozen n2z publication artifact differs; preserve before replacement: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def verify_saved(manifest, cert):
    require(cert.get("validated") is True and cert.get("submission_ready") is False
            and cert.get("API_used") is False and cert.get("Lean_started_by_validator") is False,
            "n2z strict certificate is not locally validated and offline")
    require(cert.get("theorem_name") == inputs.NAME and cert.get("node") == inputs.KEY,
            "n2z certificate identity differs")
    require(cert.get("stage_manifest_sha256") == sha(STAGE / "manifest.json")
            and cert.get("preparation_sha256") == sha(STAGE / "preparation.json")
            and cert.get("metadata_sha256") == sha(STAGE / "academic-metadata.json"),
            "n2z certificate is stale against exact stage inputs")
    definition = cert["definition"]
    require(definition["validated"] is True and definition["output_olean_sha256"] ==
            "3ce01f74da4f3a71452f192d4b243e79ee6fa6df53d81d94c756db5afff45fba",
            "n2z published Definition OLean/certificate pin changed")
    for relative, expected in cert["implementation_hashes"].items():
        require(sha(TASK / relative) == expected, "n2z certificate implementation changed: " + relative)
    for relative, expected in cert["output_json_sha256"].items():
        require(sha(TASK / relative) == expected, "n2z kernel/helper/reference JSON changed: " + relative)
    for name, row in cert["preflights"].items():
        data = row["data"]
        require(data["mode"] == "modecheck" and data["exit_code"] == 0 and data["source_unchanged"] is True
                and 0 < data["seconds"] <= 300,
                "n2z bounded compiler record failed: " + name)
        require(sha(TASK / row["record"]) == row["record_sha256"]
                and sha(TASK / data["log"]) == data["log_sha256"],
                "n2z preflight sidecar/compiler log changed: " + name)
    statement_file = Path(manifest["statement"]).name
    ordered = cert["preflights"][statement_file]["data"]["dependency_oleans"]
    seen = set()
    ordered_gate = []
    for item in ordered:
        require(item["stable_during_compile"] is True and item["module"] not in seen,
                "n2z dependency OLean ordering/stability gate failed")
        seen.add(item["module"])
        olean_path = Path(item["path"])
        require(olean_path.is_file() and sha(olean_path) == item["sha256_before"]
                and item["sha256_before"] == item["sha256_after"],
                "n2z imported OLean is stale: " + item["module"])
        ordered_gate.append({"module": item["module"], "path": item["path"],
                             "sha256": item["sha256_before"], "stable_during_compile": True})
    module = inputs.PLATFORM
    drows = [item for item in ordered_gate if item["module"] == module]
    require(len(drows) == 1 and drows[0]["sha256"] == definition["output_olean_sha256"],
            "ordered n2z imports omit the exact published Definition OLean")
    require(cert["types_equal"] is True and len(cert["source_generated_inline_helper_types_equal"]) == 3
            and cert["proof_axioms"] == "Std3" and cert["proof_reference_axioms"] == "Std3",
            "n2z kernel/helper/Std3 certificate gates changed")
    return ordered_gate


def artifacts():
    inputs.check()
    manifest, cert = read(STAGE / "manifest.json"), read(CERT)
    ordered_gate = verify_saved(manifest, cert)
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
            "source_module": cert["source_command_witness"]["source_module"],
            "target_command": cert["source_command_witness"],
            "source_components": manifest["source_components"],
            "inline_helper_ast_witness": cert["zero_helper_ast_witness"],
            "source_generated_helper_names": cert["source_generated_inline_helper_types_equal"],
        },
    }
    payloads = publisher.payloads(DEST, manifest, metadata)
    metadata_bytes = encode(metadata)
    pins = {
        "theorem_name": manifest["theorem_name"], "environment": publisher.ENV,
        "proposal_status": "Draft", "validation_certificate": validation.rel(CERT),
        "validation_sha256": sha(CERT), "manifest_sha256": sha(STAGE / "manifest.json"),
        "metadata_sha256": hashlib.sha256(metadata_bytes).hexdigest(),
        "publisher_sha256": sha(Path(publisher.__file__)), "wrapper_sha256": sha(SELF),
        "preparer_sha256": sha(Path(inputs.__file__)),
        "ordered_import_olean_gate": ordered_gate,
        "definition": cert["definition"],
        "inline_helper_names": cert["source_generated_inline_helper_types_equal"],
        "payload_sha256": {name: hashlib.sha256(data).hexdigest() for name, data in payloads.items()},
        "local_node_validated": True, "submission_ready": False, "full_tree_ready": False,
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True, "api_used": False,
    }
    return manifest, cert, metadata_bytes, payloads, pins


def prepare():
    manifest, cert, metadata_bytes, payloads, pins = artifacts()
    exact(DEST / "manifest.json", (STAGE / "manifest.json").read_bytes())
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", metadata_bytes)
    for name, data in payloads.items(): exact(DEST / name, data)
    sidecar = {name: {"record": row["record"], "record_sha256": row["record_sha256"],
                      "log": row["data"]["log"], "log_sha256": row["data"]["log_sha256"],
                      "seconds": row["data"]["seconds"], "timeout_seconds": row["data"]["timeout_seconds"]}
               for name, row in cert["preflights"].items()}
    exact(DEST / "compiler-sidecar.json", encode(sidecar))
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "stage": validation.rel(DEST),
            "payload_sha256": pins["payload_sha256"], "ordered_import_count": len(pins["ordered_import_olean_gate"]),
            "inline_helpers": pins["inline_helper_names"], "proposal_status": "Draft", "submission_ready": False}


def check():
    manifest, cert, metadata_bytes, payloads, pins = artifacts()
    require(read(DEST / "preparation.json") == pins, "n2z immutable payload pins differ")
    require((DEST / "manifest.json").read_bytes() == (STAGE / "manifest.json").read_bytes()
            and (DEST / "validation.json").read_bytes() == CERT.read_bytes()
            and (DEST / "metadata.json").read_bytes() == metadata_bytes,
            "n2z saved publication evidence or metadata changed")
    for name, data in payloads.items():
        require((DEST / name).read_bytes() == data, "n2z saved payload changed: " + name)
    return {"checked": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": pins["payload_sha256"], "submission_ready": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare_only else check(), ensure_ascii=False, indent=2))
