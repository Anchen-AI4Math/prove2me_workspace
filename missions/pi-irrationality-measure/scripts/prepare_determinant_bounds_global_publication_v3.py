"""Freeze the determinant-bounds theorem publication bundle without networking.

The pending mode is pure staging.  Final preparation additionally replays the
frozen existing-evidence consumer and binds its actual certificate byte-for-byte.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_determinant_bounds_node_existing_v2 as consumer
import prepare_determinant_bounds_global_node as stage
import publish_standalone_platform_node as publisher


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v3"
CERT = consumer.CERT
SELF = Path(__file__).resolve()

CERT_FIELDS = {
    "schema_version", "artifact_kind", "validated", "source_name", "solution_name",
    "source_module", "solution_module", "source_commit", "source_sha256",
    "source_ast_unit_sha256", "stage_manifest_sha256", "stage_preparation_sha256",
    "wire_theorem_sha256", "source_type_equals_solution_type",
    "source_proof_value_equals_renamed_solution",
    "typed_snapshots_include_actual_proof_values", "source_owner", "generated_owner",
    "source_axioms", "generated_axioms", "Std3_only",
    "automatic_inline_helper_pairs", "project_reference_closure", "solution_olean",
    "solution_olean_sha256", "preflights", "output_json_sha256",
    "implementation_hashes", "consumer_provenance", "max_file_seconds",
    "top_level_global_theorem_solution", "preserved_namespaced_stage",
    "submission_ready", "proposal_status", "Lean_started_by_consumer", "API_used",
}
ACADEMIC_FIELDS = {"title", "statement", "explanation", "tags", "source_commit", "source_url"}
EXPECTED_IMPORTS = ["Mathlib.Tactic.Linarith", "Mathlib.Topology.Instances.Real.Lemmas"]


def sha_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def encode(value) -> bytes:
    return publisher.encode(value)


def rel(path: Path) -> str:
    return path.resolve().relative_to(TASK.resolve()).as_posix()


def root_rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def exact(path: Path, raw: bytes) -> None:
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen determinant-bounds global-v3 publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def static_artifacts():
    stage.check_only()
    prep = read(STAGE / "manifest.json")
    academic = read(STAGE / "academic-metadata.json")
    need(set(academic) == ACADEMIC_FIELDS, "Determinant-bounds academic metadata shape differs")
    need(academic == prep["academic_metadata"], "Academic metadata differs from staged manifest")
    need(academic["source_commit"] == stage.SOURCE_COMMIT
         and academic["source_url"] == stage.SOURCE_URL,
         "Academic source provenance differs")
    need(stage.NAME == "OAI.PiExponent.determinant_bounds_inconsistent",
         "Fully qualified publication theorem name changed")
    need(prep["declared_dependencies"] == {"type": [], "value": [], "inline_helpers": []}
         and prep["decl_graph_row"]["typeDeps"] == []
         and prep["decl_graph_row"]["valueDeps"] == [],
         "Self-contained source dependency contract changed")

    statement = STAGE / stage.SOURCE_OUTPUT
    solution = STAGE / stage.SOLUTION_OUTPUT
    assembled = (prep["preamble"] + prep["formal_statement"]).encode("utf-8")
    need(statement.read_bytes() == assembled
         and (STAGE / "wire-theorem-source.lean").read_bytes() == assembled
         and sha_bytes(assembled) == prep["compiled_statement_assembly_sha256"],
         "Compiled Thm differs from exact preamble + formal_statement bytes")
    need(prep["preamble"].endswith("namespace OAI\nnamespace PiExponent\nopen Filter Topology\n\n")
         and prep["formal_statement"].endswith("\n\nend PiExponent\nend OAI\n"),
         "Namespace framing moved outside the exact wire assembly")
    need(prep["files"][stage.SOURCE_OUTPUT]["imports"] == EXPECTED_IMPORTS
         and prep["files"][stage.SOLUTION_OUTPUT]["imports"] == EXPECTED_IMPORTS,
         "The self-contained theorem imports changed")
    need(prep["files"][stage.SOURCE_OUTPUT]["mode"] == "modecheck"
         and prep["files"][stage.SOURCE_OUTPUT]["emit_olean"] is False
         and prep["files"][stage.SOLUTION_OUTPUT]["mode"] == "emit-olean"
         and prep["files"][stage.SOLUTION_OUTPUT]["emit_olean"] is True,
         "Target/solution compile modes changed")
    solution_bytes = solution.read_bytes()
    need(prep["solution_binding"].startswith("Global top-level theorem solution")
         and solution_bytes.count(b"theorem solution") == 1
         and b"namespace OAI" not in solution_bytes
         and b"namespace PiExponent" not in solution_bytes,
         "Verification solution is not the required single global top-level theorem")

    publication_manifest = {
        "schema_version": 1,
        "artifact_kind": "ap7-determinant-bounds-publication-manifest",
        "theorem_name": stage.NAME,
        "preamble": prep["preamble"],
        "formal_statement": prep["formal_statement"],
        "statement": root_rel(statement),
        "statement_sha256": sha(statement),
        "solution": root_rel(solution),
        "solution_sha256": sha(solution),
        "source_commit": stage.SOURCE_COMMIT,
        "source_url": stage.SOURCE_URL,
        "source_module": stage.MODULE,
        "proposal_status": "Draft",
        "validated": CERT.is_file(),
        "submission_ready": False,
    }
    metadata = {
        "theorem_name": stage.NAME,
        "theorem_title": academic["title"],
        "natural_language_statement": academic["statement"],
        "explanation": academic["explanation"],
        "tags": academic["tags"],
        "source_witness": {
            "source_commit": stage.SOURCE_COMMIT,
            "source_url": stage.SOURCE_URL,
            "source_module": stage.MODULE,
            "source_path": prep["source_path"],
            "source_sha256": prep["source_sha256"],
            "source_byte_range": prep["source_byte_range"],
            "source_line_range": prep["source_line_range"],
            "source_unit_sha256": prep["source_unit_sha256"],
            "mathematical_role": academic["explanation"],
        },
    }
    payloads = publisher.payloads(DEST, publication_manifest, metadata)
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    verify = json.loads(payloads["verification-payload.json"])
    need(problem["theorem_name"] == stage.NAME
         and (problem["preamble"] + problem["formal_statement"]).encode("utf-8") == assembled,
         "Publish payload changes the exact compiled theorem bytes")
    need(verify["target_theorem_name"] == stage.NAME
         and verify["file"]["sha256"] == sha(solution)
         and verify["file"]["utf8"].encode("utf-8") == solution.read_bytes(),
         "Verification payload changes the literal source solution")
    return prep, publication_manifest, metadata, payloads, assembled


def replay_certificate(cert: dict, prep: dict) -> None:
    need(set(cert) == CERT_FIELDS, "Actual determinant-bounds consumer report schema differs")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap7-determinant-bounds-strict-actual-node-v2-validation"
         and cert["validated"] is True and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False,
         "Determinant-bounds certificate state differs")
    need(cert["top_level_global_theorem_solution"] is True
         and cert["preserved_namespaced_stage"] == prep["preserved_namespaced_stage"],
         "Global solution binding or preserved failed-stage lineage differs")
    need(cert["source_name"] == stage.NAME and cert["solution_name"] == "solution"
         and cert["source_module"] == stage.MODULE
         and cert["solution_module"] == consumer.SOLUTION_MODULE
         and cert["source_commit"] == stage.SOURCE_COMMIT
         and cert["source_sha256"] == prep["source_sha256"]
         and cert["source_ast_unit_sha256"] == prep["source_unit_sha256"],
         "Determinant-bounds certificate identity/source pins differ")
    need(cert["source_type_equals_solution_type"] is True
         and cert["source_proof_value_equals_renamed_solution"] is True
         and cert["typed_snapshots_include_actual_proof_values"] is True
         and cert["Std3_only"] is True
         and set(cert["source_axioms"]) <= consumer.STD3
         and cert["source_axioms"] == cert["generated_axioms"],
         "Type, full proof-CI, or Std3 certificate gate differs")
    need(cert["stage_manifest_sha256"] == sha(STAGE / "manifest.json")
         and cert["stage_preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["wire_theorem_sha256"] == sha(STAGE / "wire-theorem-source.lean"),
         "Determinant-bounds v2 stage pins differ")
    need(cert["source_owner"]["kind"] == "ImportedModule"
         and cert["source_owner"]["module"] == stage.MODULE
         and type(cert["source_owner"]["moduleIndex"]) is int
         and cert["source_owner"]["moduleIndex"] >= 0
         and cert["generated_owner"]["kind"] == "ImportedModule"
         and cert["generated_owner"]["module"] == consumer.SOLUTION_MODULE
         and type(cert["generated_owner"]["moduleIndex"]) is int
         and cert["generated_owner"]["moduleIndex"] >= 0,
         "Actual source/generated imported-module owners differ")
    need(cert["project_reference_closure"] == "only uniquely paired actual inline helper CIs",
         "Self-contained project reference closure differs")
    for path, expected in cert["output_json_sha256"].items():
        need(sha(TASK / path) == expected, "Certified full-CI output changed: " + path)
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "Certified implementation changed: " + path)
    olean = TASK / cert["solution_olean"]
    need(olean.is_file() and sha(olean) == cert["solution_olean_sha256"],
         "Certified solution OLean changed")
    provenance = cert["consumer_provenance"]
    need(provenance == {
        "active_consumer": rel(Path(consumer.__file__)),
        "active_consumer_sha256": sha(Path(consumer.__file__)),
        "original_consumer": rel(consumer.OLD_CONSUMER),
        "original_consumer_sha256": sha(consumer.OLD_CONSUMER),
    }, "V2/original consumer provenance differs")
    source_ci = read(STAGE / "source-proof-references.json")["theorem"]
    generated_ci = read(STAGE / "generated-proof-references.json")["theorem"]
    for label, row in (("source", source_ci), ("generated", generated_ci)):
        need(row.get("closedType") is True and row.get("closedValue") is True
             and row.get("value") is not None and isinstance(row.get("valueRefs"), list),
             label + " theorem proof CI is absent or not closed")
    need(consumer.validate(write=False) == cert,
         "Certificate differs from a full replay of the frozen strict consumer")


def artifacts():
    prep, manifest, metadata, payloads, assembled = static_artifacts()
    need(CERT.is_file(), "Actual determinant-bounds validation certificate is pending")
    cert = read(CERT)
    replay_certificate(cert, prep)
    return prep, manifest, metadata, payloads, assembled, cert


def pins(prep, manifest, metadata, payloads):
    return {
        "theorem_name": stage.NAME,
        "environment": publisher.ENV,
        "proposal_status": "Draft",
        "manifest_sha256": sha_bytes(encode(manifest)),
        "validation_sha256": sha(CERT),
        "stage_manifest_sha256": sha(STAGE / "manifest.json"),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "publisher_sha256": sha(Path(publisher.__file__)),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "offline_wrapper_sha256": sha(SELF),
        "wire_theorem_sha256": prep["compiled_statement_assembly_sha256"],
        "solution_sha256": manifest["solution_sha256"],
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "local_node_validated": True,
        "submission_ready": False,
        "full_tree_ready": False,
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "api_used": False,
    }


def pending():
    prep, manifest, metadata, payloads, assembled = static_artifacts()
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    record = {
        "schema_version": 1,
        "artifact_kind": "ap7-determinant-bounds-global-v3-pending-publication",
        "theorem_name": stage.NAME,
        "stage_manifest_sha256": sha(STAGE / "manifest.json"),
        "publication_manifest_sha256": sha_bytes(encode(manifest)),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "wire_theorem_sha256": sha_bytes(assembled),
        "solution_sha256": manifest["solution_sha256"],
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "strict_validation_pending": not CERT.is_file(),
        "network_used": False,
        "API_used": False,
        "submission_ready": False,
        "proposal_status": "Draft",
    }
    exact(DEST / "pending-preparation.json", encode(record))
    return {"prepared": True, "validation_pending": not CERT.is_file(),
            "network_used": False, "proposal_status": "Draft",
            "payload_sha256": record["payload_sha256"]}


def prepare():
    prep, manifest, metadata, payloads, assembled, _ = artifacts()
    frozen = pins(prep, manifest, metadata, payloads)
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    exact(DEST / "preparation.json", encode(frozen))
    return {"prepared": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": frozen["payload_sha256"]}


def check():
    prep, manifest, metadata, payloads, assembled, _ = artifacts()
    frozen = pins(prep, manifest, metadata, payloads)
    need((DEST / "manifest.json").read_bytes() == encode(manifest)
         and (DEST / "validation.json").read_bytes() == CERT.read_bytes()
         and (DEST / "metadata.json").read_bytes() == encode(metadata)
         and (DEST / "wire-theorem-source.lean").read_bytes() == assembled
         and (DEST / "preparation.json").read_bytes() == encode(frozen),
         "Frozen determinant-bounds publication evidence differs")
    for name, raw in payloads.items():
        need((DEST / name).read_bytes() == raw,
             "Frozen determinant-bounds payload differs: " + name)
    return {"checked": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": frozen["payload_sha256"]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-pending", action="store_true")
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = pending() if args.prepare_pending else prepare() if args.prepare_only else check()
    print(json.dumps(result, ensure_ascii=False, indent=2))
