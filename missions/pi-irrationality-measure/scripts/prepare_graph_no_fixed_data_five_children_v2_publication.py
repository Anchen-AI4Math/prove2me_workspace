"""Pure publication-v3 preparation for the source-helper NoFixedData sketch.

This successor keeps the v1 failed compile and publication-v2 pending records
as preimages. Final preparation requires the three new strict preflights.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

import certify_graph_no_fixed_data_five_children_v2 as consumer
import prepare_graph_no_fixed_data_five_children_publication as old_publication
import stage_graph_no_fixed_data_five_children_v2 as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v3"
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_graph_no_fixed_data_five_children_v2.py"
CERT = consumer.CERT
API = old_publication.API
REUSED_DRIVER = TASK / "scripts/publish_graph_no_fixed_data_five_children.py"
ENV = old_publication.ENV
PRIOR = old_publication.PRIOR
MEAN_RECORD = old_publication.MEAN_RECORD
OLD_PENDING = old_publication.DEST / "pending-preparation.json"
ARITH_WIRE = stage.old.STAGE / "arithmetic-source017-open-wire.lean"
NFD_WIRE = stage.old.STAGE / stage.old.NFD_FILE


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def sha(path):
    return sha_bytes(Path(path).read_bytes())


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(doc):
    return (json.dumps(doc, ensure_ascii=False, indent=2) + "\n").encode()


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def exact(path, raw):
    path = Path(path)
    if path.is_file():
        need(path.read_bytes() == raw, "Frozen successor publication-v3 artifact differs: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def explanation():
    return (
        "The original contradiction proof combines analytic convergence with the "
        "proved collision-rate limit. At large interpolation scales, surjectivity "
        "yields a nonzero full-row minor. The selected minor's arithmetic lower "
        "bound, the actual mean-weight bounds, and the analytic upper estimate "
        "then contradict the proved determinant-bounds comparison. Five short "
        "AdmissibleParameters lemmas used internally are copied with their exact "
        "source statements and proofs into this solution. The collision limit, "
        "full-row minor, mean bounds, and determinant comparison children are "
        "proved on the platform; the arithmetic lower-bound child remains Open. "
        "This submission records the original dependency graph as a sketch, not "
        "a closed proof."
    )


def static(final=False):
    stage.check()
    prep = read(STAGE / "preparation.json")
    need(prep["original_41_line_NoFixedData_proof_only_two_name_replacements"] is True and
         len(prep["five_original_helper_commands"]) == 5 and
         prep["original_NoFixedData_comparator_sha256"] == sha(NFD_WIRE) and
         prep["original_arithmetic_Open_wire_sha256"] == sha(ARITH_WIRE) and
         OLD_PENDING.is_file(), "Original v1 stage/pending preimage differs")
    old_pending = read(OLD_PENDING)
    need(old_pending["NoFixedData_name"] == stage.old.NFD and
         old_pending["arithmetic_source017_name"] == stage.old.ARITH and
         old_pending["closed_proof"] is False and
         old_pending["strict_validation_pending"] is True,
         "Original publication-v2 pending preimage differs")
    arith_payload = (old_publication.DEST / "arithmetic-publish-payload.json").read_bytes()
    arith_problem = json.loads(arith_payload)["problems"][0]
    wire = ARITH_WIRE.read_bytes()
    need(arith_problem["theorem_name"] == stage.old.ARITH and
         (arith_problem["preamble"] + arith_problem["formal_statement"]).encode() == wire and
         sha_bytes(arith_payload) == old_pending["payload_sha256"]["arithmetic-publish-payload.json"],
         "Source017 arithmetic Open payload differs from frozen original wire")
    prior = read(PRIOR) if PRIOR.is_file() else {}
    nfd_id = prior.get("NoFixedData_theorem_id")
    need(nfd_id is None or (isinstance(nfd_id, str) and nfd_id),
         "Existing NoFixedData id malformed")
    if nfd_id:
        local_readback = PRIOR.parent / "pre-verify-readbacks/NoFixedData.json"
        need(local_readback.is_file(), "Actual saved NoFixedData public GET is missing")
        body = read(local_readback)
        raw = NFD_WIRE.read_bytes()
        nfd_preamble = raw.split(b"theorem ", 1)[0]
        need(body["theorem_id"] == nfd_id and body["theorem_name"] == stage.old.NFD and
             body["status"] == "Open" and body["mathlib_rev"] == ENV and
             (body["preamble"] + body["formal_statement"]).encode() == raw and
             body["visibility"] == "public",
             "Saved actual NoFixedData target GET differs from original comparator")
    public = read(stage.old.STAGE / "preparation.json")["public_children_at_staging"]
    mean = read(MEAN_RECORD)
    mean_body = mean.get("target_readback", {}).get("body", {})
    mean_proved = (mean.get("confirmed_proved") is True and
                   mean.get("last_verify_verdict", {}).get("body", {}).get("status") == "ACCEPTED" and
                   mean_body.get("theorem_id") == public["mean"]["theorem_id"] and
                   mean_body.get("status") == "Proved" and
                   (mean_body.get("preamble", "") + mean_body.get("formal_statement", "")).encode() ==
                       (stage.old.STAGE / "saved-public-wire/mean.lean").read_bytes())
    need(mean_proved, "Actual mean theorem is not Accepted/Proved")
    cert = None
    if final:
        need(nfd_id, "Public NoFixedData Open target id is pending")
        need(CERT.is_file(), "Three-new-preflight source-helper certificate is pending")
        cert = read(CERT)
        need(cert == consumer.validate(write=False) and CERT.read_bytes() == consumer.encode(cert) and
             cert["validated_interface"] is True and cert["validated_closed_proof"] is False and
             cert["five_original_helpers_closed_Std3"] is True and
             cert["source_to_generated_twelve_kernel_types_equal"] is True and
             cert["five_child_graph_sketch_only"] is True and
             len(cert["three_new_preflights"]) == 3 and
             len(cert["five_reused_child_preflights"]) == 5,
             "Strict source-helper/interface certificate differs")
    solution = STAGE / stage.SOL_FILE
    solution_raw = solution.read_bytes()
    need(sha(solution) == prep["new_solution_sha256"] and
         solution_raw.count(b"theorem solution") == 1 and b"sorry" not in solution_raw and
         all(solution_raw.count(("theorem " + n).encode()) == 1 for n in stage.NAMES),
         "New global solution/five exact helper proof file differs")
    descriptor = {"theorem_id": nfd_id, "proof_type": "prove", "explanation": explanation(),
                  "file": {"filename": Path(stage.SOL_FILE).name,
                           "source": rel(solution), "sha256": sha(solution),
                           "utf8": solution_raw.decode()}}
    payloads = {"arithmetic-publish-payload.json": arith_payload,
                "verification-payload.json": encode(descriptor)}
    ctype = None
    if nfd_id:
        spec = importlib.util.spec_from_file_location("p2m_api_offline", API)
        api = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(api)
        multipart, ctype = api._multipart(
            {"theorem_id": nfd_id, "proof_type": "prove", "explanation": descriptor["explanation"]},
            {"file": (descriptor["file"]["filename"], solution_raw)})
        payloads["verification-request.multipart"] = multipart
    pins = {"schema_version": 1,
            "artifact_kind": "NoFixedData-five-child-original-helper-publication-v3-preparation",
            "environment": ENV, "proposal_status": "Draft", "submission_ready": False,
            "NoFixedData_theorem_id": nfd_id, "NoFixedData_name": stage.old.NFD,
            "arithmetic_source017_name": stage.old.ARITH,
            "child_theorem_ids": {k: row["theorem_id"] for k, row in public.items()},
            "mean_platform_Proved": mean_proved,
            "NoFixedData_wire_sha256": sha(NFD_WIRE),
            "arithmetic_Open_wire_sha256": sha(ARITH_WIRE),
            "solution_sha256": sha(solution),
            "source_helper_original_AST_sha256": {row["name"]: row["original_command_sha256"]
                                                  for row in prep["five_original_helper_commands"]},
            "stage_preparation_sha256": sha(STAGE / "preparation.json"),
            "strict_certificate_sha256": sha(CERT) if cert else None,
            "old_publication_pending_sha256": sha(OLD_PENDING),
            "old_failed_c6_sidecar_sha256": prep["old_failed_solution_preimage"]["sidecar_sha256"],
            "offline_wrapper_sha256": sha(SELF), "online_wrapper_sha256": sha(ONLINE),
            "strict_consumer_sha256": sha(Path(consumer.__file__)),
            "stage_producer_sha256": sha(Path(stage.__file__)),
            "api_client_sha256": sha(API),
            "reused_durable_graph_driver_sha256": sha(REUSED_DRIVER),
            "three_manifest_sha256": {name: sha(STAGE / name)
                                      for name in prep["three_compiler_manifests"]},
            "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
            "multipart_content_type": ctype,
            "expected_verify_status": "SKETCH_ACCEPTED", "closed_proof": False,
            "arithmetic_child_Open": True,
            "durable_policy": "write intent before POST; never repeat recorded intent; poll only known ids",
            "API_used": False}
    return prep, arith_problem, descriptor, payloads, pins, cert


def prepare_pending():
    prep, problem, descriptor, payloads, pins, cert = static(final=False)
    exact(DEST / "arithmetic-publish-payload.json", payloads["arithmetic-publish-payload.json"])
    exact(DEST / "arithmetic-open-wire.lean", ARITH_WIRE.read_bytes())
    exact(DEST / "verification-payload.pending.json", payloads["verification-payload.json"])
    pending = dict(pins)
    pending.update({"artifact_kind": "NoFixedData-five-child-source-helper-pending-publication-v3",
                    "strict_validation_pending": True, "network_used": False})
    pending_path = DEST / "pending-preparation.json"
    if pending_path.is_file() and pending_path.read_bytes() != encode(pending):
        pending_path = DEST / "pending-preparation-v2.json"
    exact(pending_path, encode(pending))
    return {"prepared": True, "final_ready": False, "strict_certificate_pending": True,
            "NoFixedData_theorem_id": pins["NoFixedData_theorem_id"], "network_used": False}


def prepare_final():
    prep, problem, descriptor, payloads, pins, cert = static(final=True)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    exact(DEST / "arithmetic-open-wire.lean", ARITH_WIRE.read_bytes())
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "final_ready": True, "closed_proof": False,
            "NoFixedData_theorem_id": pins["NoFixedData_theorem_id"], "network_used": False}


def check():
    prep, problem, descriptor, payloads, pins, cert = static(final=True)
    need((DEST / "preparation.json").read_bytes() == encode(pins) and
         (DEST / "validation.json").read_bytes() == CERT.read_bytes() and
         (DEST / "arithmetic-open-wire.lean").read_bytes() == ARITH_WIRE.read_bytes(),
         "Frozen successor publication-v3 preparation differs")
    for name, raw in payloads.items():
        need((DEST / name).read_bytes() == raw, "Frozen successor payload differs: " + name)
    return prep, problem, descriptor, payloads, pins, cert


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-pending", action="store_true")
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if args.prepare_pending:
        result = prepare_pending()
    elif args.prepare_only:
        result = prepare_final()
    else:
        check()
        result = {"checked": True, "final_ready": True, "network_used": False,
                  "closed_proof": False}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
