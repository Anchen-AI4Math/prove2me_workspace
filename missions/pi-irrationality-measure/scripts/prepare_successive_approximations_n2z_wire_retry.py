"""Build an offline n2z wire payload whose preamble is proven exact to c1.

No network requests are made here. The failed earlier job and all of its
evidence stay immutable in publication-draft/.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import prepare_successive_approximations_n2z as inputs
import publish_standalone_platform_node as publisher
import validate_successive_approximations_n2z as validation

TASK, ROOT, STAGE = inputs.TASK, inputs.ROOT, inputs.STAGE
OLD = STAGE / "publication-draft"
DEST = STAGE / "publication-wire-1"
CERT = validation.CERT
SELF = Path(__file__).resolve()
THEOREM_FILE = STAGE / "Theorems/Thm_OAI_PiExponent_exists_normalized_selection_of_selector.lean"
THEOREM_BASENAME = THEOREM_FILE.name
ZERO = "OAI.PiExponent.normalizedLogWeights_zero"


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def encode(value) -> bytes:
    return publisher.encode(value)


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def exact(path: Path, data: bytes) -> None:
    if path.exists():
        if path.read_bytes() != data:
            raise ValueError("Wire retry artifact differs; preserve this attempt before changing: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def assembly(manifest, cert, failed):
    require = failed.get("last_publish_verdict", {}).get("body", {})
    need(failed.get("job_id") == "20caafb9-8460-4916-952f-913540eea6c2"
         and require.get("status") == "FAILED"
         and require.get("theorem_name") == inputs.NAME
         and "normalizedLogWeights q 0" in require.get("error_message", ""),
         "Preserved failed server job does not match the known exact missing-zero-helper failure")
    failed_payload = read(OLD / "publish-payload.json")
    old_problem = failed_payload["problems"][0]
    need(old_problem["theorem_name"] == inputs.NAME
         and old_problem["formal_statement"] == manifest["formal_statement"],
         "Old failed attempt formal statement differs from the current frozen theorem statement")
    target = THEOREM_FILE.read_bytes()
    need(sha(THEOREM_FILE) == cert["preflights"][THEOREM_BASENAME]["data"]["source_sha256_before"],
         "Compiled theorem source differs from n2z actual c1 source bytes")
    formal = manifest["formal_statement"].encode("utf-8")
    need(target.count(formal) == 1, "Exact theorem formal_statement is not a unique source suffix")
    at = target.find(formal)
    preamble = target[:at]
    need(target == preamble + formal, "Wire preamble + unchanged formal statement do not reproduce c1 bytes")
    need(old_problem["formal_statement"].encode("utf-8") == formal,
         "Repair would alter the failed job's formal statement")
    need(old_problem["preamble"].encode("utf-8") != preamble,
         "Preserved failed payload unexpectedly already contains the exact compiled preamble")
    zero = cert["zero_helper_ast_witness"]
    raw_zero = zero["raw_command_utf8"].encode("utf-8")
    normalized_zero = raw_zero.replace(b"\r\n", b"\n").rstrip(b"\n")
    need(zero["source_graph_name"] == ZERO and zero["source_unit"].endswith(":3545")
         and zero["generated_companion"] is False and zero["raw_proof_suffix_utf8"] == ":= rfl"
         and sha_bytes(raw_zero) == zero["raw_command_sha256"],
         "Frozen zero-helper AST/raw source witness differs")
    need(preamble.count(normalized_zero) == 1,
         "Exact zero-helper AST command is not present exactly once in compiled theorem preamble")
    zero_at = preamble.find(normalized_zero)
    oai_at, pi_at = preamble.find(b"namespace OAI"), preamble.find(b"namespace PiExponent")
    close_pi = preamble.find(b"end PiExponent")
    succ_at = preamble.find(b"@[simp] theorem normalizedLogWeights_succ")
    reverse_at = preamble.find(b"theorem reverse_logWeights_prod")
    need(0 <= oai_at < pi_at < zero_at < succ_at < reverse_at < close_pi,
         "Zero helper no longer appears in the exact compiled OAI.PiExponent section before its dependent helpers")
    return preamble, {
        "schema_version": 1,
        "artifact_kind": "successive-approximations-n2z-exact-wire-assembly-certificate",
        "validated": True,
        "theorem_name": inputs.NAME,
        "failed_attempt_record": "verification/ap4/n2z/publication-draft/publication.json",
        "failed_attempt_record_sha256": sha(OLD / "publication.json"),
        "failed_job_id": failed["job_id"],
        "failed_status": require["status"],
        "failed_error_message": require["error_message"],
        "old_publish_payload_sha256": sha(OLD / "publish-payload.json"),
        "old_preamble_sha256": sha_bytes(old_problem["preamble"].encode("utf-8")),
        "source_theorem_file": validation.rel(THEOREM_FILE),
        "source_theorem_file_sha256": sha_bytes(target),
        "c1_preflight_record": cert["preflights"][THEOREM_BASENAME]["record"],
        "c1_preflight_record_sha256": cert["preflights"][THEOREM_BASENAME]["record_sha256"],
        "c1_log": cert["preflights"][THEOREM_BASENAME]["data"]["log"],
        "c1_log_sha256": cert["preflights"][THEOREM_BASENAME]["data"]["log_sha256"],
        "unchanged_formal_statement_sha256": sha_bytes(formal),
        "wire_preamble_sha256": sha_bytes(preamble),
        "assembled_wire_theorem_sha256": sha_bytes(preamble + formal),
        "compiled_theorem_source_sha256": cert["preflights"][THEOREM_BASENAME]["data"]["source_sha256_before"],
        "assembled_equals_compiled_theorem_source": preamble + formal == target,
        "zero_helper_ast_witness": zero,
        "zero_helper_raw_source_command_sha256": sha_bytes(raw_zero),
        "zero_helper_occurrences_in_wire_preamble": 1,
        "zero_helper_scope": "OAI.PiExponent, before normalizedLogWeights_succ and reverse_logWeights_prod",
        "n2z_kernel_certificate_sha256": sha(CERT),
        "validated_node_certificate_retained": True,
        "Lean_started": False,
        "API_used": False,
        "submission_ready": False,
    }


def artifacts():
    inputs.check()
    manifest = read(STAGE / "manifest.json")
    cert = read(CERT)
    failed = read(OLD / "publication.json")
    preamble, assemble_cert = assembly(manifest, cert, failed)
    wire_manifest = dict(manifest)
    wire_manifest["preamble"] = preamble.decode("utf-8")
    academic = read(STAGE / "academic-metadata.json")
    metadata = read(OLD / "metadata.json")
    need(metadata["theorem_name"] == inputs.NAME
         and metadata["natural_language_statement"] == academic["natural_language_statement"]
         and metadata["theorem_title"] == academic["theorem_title"],
         "Metadata drift from exact source statement")
    payloads = publisher.payloads(DEST, wire_manifest, metadata)
    payload_problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    need(payload_problem["preamble"].encode("utf-8") + payload_problem["formal_statement"].encode("utf-8")
         == THEOREM_FILE.read_bytes(),
         "Actual publication payload does not assemble to the exact c1-compiled theorem module")
    need(payload_problem["formal_statement"] == old_problem_statement(failed),
         "Wire repair changed the theorem formal statement")
    pins = {
        "theorem_name": inputs.NAME,
        "environment": publisher.ENV,
        "proposal_status": "Draft",
        "assembly_certificate_sha256": sha_bytes(encode(assemble_cert)),
        "validation_certificate_sha256": sha(CERT),
        "manifest_sha256": sha(STAGE / "manifest.json"),
        "old_failed_attempt_sha256": sha(OLD / "publication.json"),
        "publisher_sha256": sha(Path(publisher.__file__)),
        "wrapper_sha256": sha(SELF),
        "preparer_sha256": sha(Path(inputs.__file__)),
        "payload_sha256": {name: sha_bytes(data) for name, data in payloads.items()},
        "assembled_wire_equals_compiled_source": True,
        "formal_statement_unchanged": True,
        "submission_ready": False,
        "full_tree_ready": False,
        "api_used": False,
    }
    return assemble_cert, metadata, payloads, pins


def old_problem_statement(failed):
    response = failed.get("last_publish_verdict", {}).get("body", {})
    return response.get("formal_statement")


def prepare():
    assemble_cert, metadata, payloads, pins = artifacts()
    exact(DEST / "assembly-certificate.json", encode(assemble_cert))
    exact(DEST / "failed-attempt-record.json", (OLD / "publication.json").read_bytes())
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", encode(metadata))
    for name, data in payloads.items(): exact(DEST / name, data)
    exact(DEST / "online-preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "stage": validation.rel(DEST),
            "assembly_certificate_sha256": pins["assembly_certificate_sha256"],
            "payload_sha256": pins["payload_sha256"], "submission_ready": False,
            "proposal_status": "Draft"}


def check():
    assemble_cert, metadata, payloads, pins = artifacts()
    need(read(DEST / "assembly-certificate.json") == assemble_cert,
         "Saved wire-assembly certificate changed")
    need(read(DEST / "online-preparation.json") == pins,
         "Saved wire payload pins changed")
    need((DEST / "failed-attempt-record.json").read_bytes() == (OLD / "publication.json").read_bytes()
         and (DEST / "validation.json").read_bytes() == CERT.read_bytes()
         and (DEST / "metadata.json").read_bytes() == encode(metadata),
         "Saved failed-attempt, validation, or metadata evidence changed")
    for name, data in payloads.items():
        need((DEST / name).read_bytes() == data, "Saved exact wire payload changed: " + name)
    return {"checked": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": pins["payload_sha256"], "submission_ready": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare_only else check(), ensure_ascii=False, indent=2))
