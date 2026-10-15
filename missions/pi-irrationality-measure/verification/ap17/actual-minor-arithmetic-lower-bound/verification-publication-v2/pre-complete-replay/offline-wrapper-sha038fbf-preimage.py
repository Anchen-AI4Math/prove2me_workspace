"""Prepare the AP17 proof for one exact existing Open theorem, offline only."""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path

import certify_actual_minor_arithmetic_lower_bound_source017_node as consumer
import publish_standalone_platform_node as publisher
import stage_actual_minor_arithmetic_lower_bound_source017_node as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "verification-publication-v2"
CERT = STAGE / stage.CERTIFICATE
FRESH = STAGE / "fresh-existing-target-readback.json"
FRESH_RUNNER = TASK / "scripts/check_actual_minor_arithmetic_lower_bound_source017_existing_target.py"
CANDIDATE = STAGE / "candidate"
CANDIDATE_SPEC = STAGE / "candidate-spec.json"
ROUTE_PREPARATION = STAGE / "route-preparation.json"
SELF = Path(__file__).resolve()
FAST = TASK / "scripts/verify_actual_minor_arithmetic_lower_bound_source017_fast.py"
FAST_HELPER = TASK / "scripts/prepare_actual_minor_arithmetic_lower_bound_source017_fast_descriptor.py"
API = ROOT / "scripts/p2m_api.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
API_REVIEW_MANIFEST = API_REVIEW / "manifest.json"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value): return publisher.encode(value)
def need(ok, message):
    if not ok: raise ValueError(message)
def rel(path): return Path(path).resolve().relative_to(TASK.resolve()).as_posix()
def root_rel(path): return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen AP17 verification artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def api_review_pins():
    review = read(API_REVIEW_MANIFEST)
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and docs["references/contribute.md"] == sha(API_REVIEW / "references/contribute.md")
         and docs["references/prove.md"] == sha(API_REVIEW / "references/prove.md"),
         "Reviewed official API documents differ")
    return {"official_tag": review["official_tag"],
            "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW_MANIFEST),
            "contribute_sha256": docs["references/contribute.md"],
            "prove_sha256": docs["references/prove.md"]}


def fresh_target(required):
    if not FRESH.is_file():
        need(not required, "Fresh AP17 exact existing-target GET is pending")
        return {"pending": True, "runner": rel(FRESH_RUNNER),
                "runner_sha256": sha(FRESH_RUNNER)}
    doc = read(FRESH)
    raw = doc.get("raw_body_utf8")
    body = doc.get("parsed_body", {})
    saved = stage.route.saved_public_target()
    need(doc.get("artifact_kind") ==
             "ap17-source017-existing-target-read-only-fresh-readback"
         and doc.get("read_only") is True and doc.get("request_methods") == ["GET"]
         and doc.get("credentials_or_tokens_recorded") is False
         and doc.get("environment") == ENV and doc.get("http_status") == 200
         and isinstance(raw, str)
         and doc.get("raw_body_sha256") == sha_bytes(raw.encode("utf-8"))
         and json.loads(raw) == body
         and body.get("theorem_id") == stage.TARGET_ID
         and body.get("theorem_name") == stage.PLATFORM_NAME
         and body.get("mathlib_rev") == ENV and body.get("status") == "Open"
         and body.get("preamble") == saved["preamble"]
         and body.get("formal_statement") == saved["formal_statement"]
         and (body["preamble"] + body["formal_statement"]).encode("utf-8") ==
             stage.route.OPEN_WIRE.read_bytes(),
         "Fresh AP17 target is not the exact reviewed Open theorem")
    return {"pending": False, "readback": rel(FRESH), "readback_sha256": sha(FRESH),
            "runner": rel(FRESH_RUNNER), "runner_sha256": sha(FRESH_RUNNER),
            "theorem_id": body["theorem_id"], "theorem_name": body["theorem_name"],
            "status": body["status"], "wire_sha256": sha(stage.route.OPEN_WIRE)}


def explanation():
    return (
        "The two original fixed-data interface lemmas identify the finite "
        "denominator lower bounds and the logarithmic row weights.  With these "
        "identities, the claimed normalized determinant estimate is exactly the "
        "already proved generic selected-minor arithmetic lower bound, applied "
        "to the source's actual row and column domains."
    )


def bundle(prep, statement, solution):
    wire = statement.read_bytes()
    source = solution.read_bytes()
    need(wire == (prep["preamble"] + prep["formal_statement"]).encode("utf-8")
         and wire == stage.route.OPEN_WIRE.read_bytes()
         and source.count(b"theorem solution ") == 1
         and b"sorry" not in source and b"FixedDeterminantFamily" not in source,
         "AP17 exact existing wire or source-faithful global proof differs")
    descriptor = {"theorem_id": stage.TARGET_ID,
                  "target_theorem_name": stage.PLATFORM_NAME,
                  "proof_type": "prove", "explanation": explanation(),
                  "file": {"filename": Path(stage.SOLUTION_OUTPUT).name,
                           "source": root_rel(STAGE / stage.SOLUTION_OUTPUT),
                           "sha256": sha(solution),
                           "utf8": source.decode("utf-8")}}
    spec = importlib.util.spec_from_file_location("p2m_api_ap17_offline", API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    multipart, ctype = api._multipart(
        {"theorem_id": stage.TARGET_ID, "proof_type": "prove",
         "explanation": descriptor["explanation"]},
        {"file": (descriptor["file"]["filename"], source)})
    return descriptor, multipart, ctype, wire


def candidate_static():
    stage.check_candidate()
    prep = read(CANDIDATE_SPEC)
    need(prep["artifact_kind"] == "ap17-source017-minor-arithmetic-candidate"
         and prep["platform_theorem_id"] == stage.TARGET_ID
         and prep["platform_name"] == stage.PLATFORM_NAME
         and prep["original_proof_AST_units"] == 3
         and prep["original_source_lines"] == 17
         and prep["only_target_binding_name_changed"] is True
         and prep["all_original_proof_suffixes_unchanged"] is True
         and prep["existing_port_adaptations"] == [],
         "AP17 candidate identity/provenance differs")
    statement = CANDIDATE / (stage.TARGET_OUTPUT + ".txt")
    solution = CANDIDATE / (stage.SOLUTION_OUTPUT + ".txt")
    descriptor, multipart, ctype, wire = bundle(prep, statement, solution)
    return prep, descriptor, multipart, ctype, wire, statement, solution


def static():
    stage.check_only()
    prep = read(STAGE / "preparation.json")
    need(prep["artifact_kind"] == "ap17-source017-minor-arithmetic-node-preparation"
         and prep["platform_theorem_id"] == stage.TARGET_ID
         and prep["platform_name"] == stage.PLATFORM_NAME
         and prep["compiler_manifests_finalized"] is True
         and prep["generic_lower_actual_kernel_certificate_pending"] is False
         and prep["generic_lower_real_Accepted_Proved_pending"] is False
         and prep["generic_lower_closed_private_mirror_certificate_pending"] is False,
         "AP17 final preparation/boundary differs")
    statement, solution = STAGE / stage.TARGET_OUTPUT, STAGE / stage.SOLUTION_OUTPUT
    descriptor, multipart, ctype, wire = bundle(prep, statement, solution)
    for name in stage.FILES:
        candidate = CANDIDATE / (name + ".txt")
        need(candidate.read_bytes() == (STAGE / name).read_bytes(),
             "AP17 final proof/probe differs from candidate: " + name)
    return prep, descriptor, multipart, ctype, wire, statement, solution


def replay(cert, prep):
    need(consumer.validate() == cert, "AP17 certificate differs from strict replay")
    need(cert["artifact_kind"] ==
             "ap17-actual-minor-arithmetic-lower-bound-source017-validation"
         and cert["validated"] is True and cert["Std3_only"] is True
         and cert["submission_ready"] is False and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False
         and cert["platform_theorem_id"] == stage.TARGET_ID
         and cert["platform_name"] == stage.PLATFORM_NAME
         and cert["exact_existing_Open_wire_unchanged"] is True
         and cert["target_wire_sha256"] == sha(STAGE / stage.TARGET_OUTPUT)
         and cert["preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["original_proof_AST_units"] == 3
         and cert["original_source_lines"] == 17
         and cert["only_target_binding_name_changed"] is True
         and cert["all_original_proof_suffixes_unchanged"] is True
         and cert["existing_port_adaptations"] == []
         and cert["no_private_generic_helper_leakage"] is True
         and cert["source_and_generated_types_equal"] is True
         and cert["source_and_generated_theorem_values_null"] is True
         and cert["source_and_generated_actual_proof_references_equal"] is True
         and set(cert["preflights"]) == set(stage.FILES)
         and 0 < cert["max_file_seconds"] <= 300,
         "AP17 strict actual proof gates differ")
    for rows in cert["axioms"].values():
        for axioms in rows.values(): need(set(axioms) <= STD3, "AP17 nonstandard axiom")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP17 implementation changed: " + path)
    for filename, expected in cert["json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP17 kernel/proof JSON changed: " + filename)
    need(sha(TASK / cert["solution_olean"]) == cert["solution_olean_sha256"],
         "AP17 solution OLean changed")


def evidence_hashes(cert):
    found = {}
    for row in cert["preflights"].values():
        record = row.get("record")
        expected_record_sha = row.get("record_sha256")
        need(record and expected_record_sha
             and sha(consumer.context.file(record)) == expected_record_sha,
             "AP17 actual preflight sidecar differs")
        found[record] = expected_record_sha
        for key in ("source", "manifest", "log"):
            value = row["data"].get(key)
            if value: found[value] = sha(consumer.context.file(value))
    return dict(sorted(found.items()))


def dependency_oleans(cert):
    found = {}
    for row in cert["preflights"].values():
        for dep in row["data"]["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"],
                 "AP17 dependency OLean changed during compilation")
            found[dep["module"] + "|" + dep["path"]] = dep["sha256_before"]
    return dict(sorted(found.items()))


def install_one_process_child_cache():
    """Run the fixed mirror replay once, then hash-gate every in-process reuse."""
    child = consumer.child_consumer
    cert_path = stage.MIRROR_STAGE / stage.mirror.CERTIFICATE
    need(cert_path.is_file(), "AP17 genuine private-mirror certificate is pending")
    recorded = read(cert_path)
    pins = {str(cert_path): sha(cert_path),
            str(Path(child.__file__)): sha(Path(child.__file__))}
    manifest = read(stage.MIRROR_STAGE / "c2.json")
    for path, expected in manifest["input_hashes"].items():
        pins[str(TASK / path)] = expected
    for path, expected in recorded["implementation_hashes"].items():
        pins[str(TASK / path)] = expected
    for filename, expected in recorded["generated_json_sha256"].items():
        pins[str(stage.MIRROR_STAGE / filename)] = expected
    pins[str(stage.MIRROR_STAGE / "preparation.json")] = recorded["preparation_sha256"]
    pins[str(TASK / recorded["provider_olean"])] = recorded["provider_olean_sha256"]
    for row in recorded["preflights"].values():
        pins[str(TASK / row["record"])] = row["record_sha256"]
        for key in ("source", "manifest", "log"):
            path = child.context.file(row["data"][key])
            pins[str(path)] = sha(path)

    def gate():
        for path, expected in pins.items():
            need(sha(Path(path)) == expected,
                 "AP17 cached child replay input changed: " + path)

    original = child.validate
    gate()
    cached = original()
    need(encode(cached) == cert_path.read_bytes(),
         "AP17 first full child replay differs from its actual certificate")
    gate()
    stats = {"full_child_mathematical_replays": 1,
             "same_process_child_reuses": 0,
             "all_child_inputs_rehashed_before_and_after_each_reuse": True,
             "first_full_child_replay_not_skipped": True,
             "child_certificate": rel(cert_path),
             "child_certificate_sha256": sha(cert_path),
             "child_consumer": rel(Path(child.__file__)),
             "child_consumer_sha256": sha(Path(child.__file__))}

    def replay_cached():
        gate()
        stats["same_process_child_reuses"] += 1
        result = copy.deepcopy(cached)
        gate()
        return result

    child.validate = replay_cached
    return child, original, gate, stats


def pending():
    prep, descriptor, multipart, ctype, wire, _, solution = candidate_static()
    exact(DEST / "verification-payload.json", encode(descriptor))
    exact(DEST / "verification-request.multipart", multipart)
    exact(DEST / "metadata.json", (CANDIDATE / "academic-metadata.json.txt").read_bytes())
    exact(DEST / "wire-theorem-source.lean", wire)
    record = {"schema_version": 1,
        "artifact_kind": "ap17-existing-open-proof-pending-preparation",
        "target_theorem_id": stage.TARGET_ID, "target_theorem_name": stage.PLATFORM_NAME,
        "candidate_spec_sha256": sha(CANDIDATE_SPEC),
        "route_preparation_sha256": sha(ROUTE_PREPARATION),
        "saved_open_wire_sha256": sha(stage.route.OPEN_WIRE),
        "fresh_target": fresh_target(False),
        "solution_sha256": sha(solution), "descriptor_sha256": sha_bytes(encode(descriptor)),
        "multipart_sha256": sha_bytes(multipart), "multipart_content_type": ctype,
        "strict_validation_pending": not CERT.is_file(),
        "final_stage_pending": not (STAGE / "preparation.json").is_file(),
        "exact_existing_target_only": True, "creates_theorem_or_proposal": False,
        "network_used": False, "API_used": False, "submission_ready": False,
        "proposal_status": "Draft"}
    exact(DEST / "pending-preparation.json", encode(record))
    return {"prepared": True, "validation_pending": record["strict_validation_pending"],
            "final_stage_pending": record["final_stage_pending"], "network_used": False,
            "creates_theorem_or_proposal": False,
            "descriptor_sha256": record["descriptor_sha256"],
            "multipart_sha256": record["multipart_sha256"]}


def prepare():
    need(CERT.is_file() and (STAGE / "preparation.json").is_file(),
         "AP17 strict actual certificate/final preparation is pending")
    child, original_child_validate, child_gate, child_replay = \
        install_one_process_child_cache()
    try:
        prep, descriptor, multipart, ctype, wire, _, solution = static()
        target = fresh_target(True)
        cert = read(CERT)
        replay(cert, prep)
    finally:
        child.validate = original_child_validate
    need(child_replay["full_child_mathematical_replays"] == 1
         and child_replay["same_process_child_reuses"] >= 1,
         "AP17 child replay cache was not exercised exactly as reviewed")
    child_gate()
    pins = {"schema_version": 1,
        "artifact_kind": "ap17-existing-open-proof-verification-preparation",
        "target_theorem_id": stage.TARGET_ID, "target_theorem_name": stage.PLATFORM_NAME,
        "environment": ENV, "validation_sha256": sha(CERT),
        "fresh_target": target,
        "saved_open_record_sha256": sha(stage.route.OPEN_RECORD),
        "saved_open_wire_sha256": sha(stage.route.OPEN_WIRE),
        "saved_open_publication_sha256": sha(stage.route.PUBLICATION),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "stage_input_hashes": prep["input_hashes"],
        "compiler_manifest_sha256": {prep["files"][name]["manifest"]:
             sha(STAGE / prep["files"][name]["manifest"]) for name in stage.FILES},
        "preflight_artifact_sha256": evidence_hashes(cert),
        "dependency_olean_sha256": dependency_oleans(cert),
        "output_json_sha256": cert["json_sha256"],
        "solution_olean": cert["solution_olean"],
        "solution_olean_sha256": cert["solution_olean_sha256"],
        "generic_lower_actual_Accepted_theorem_id":
            cert["generic_lower_actual_Accepted_theorem_id"],
        "generic_lower_actual_Accepted_proof_id": cert["generic_lower_actual_Accepted_proof_id"],
        "generic_lower_mirror_certificate_sha256":
            cert["generic_lower_mirror_certificate_sha256"],
        "generic_lower_mirror_olean_sha256": cert["generic_lower_mirror_olean_sha256"],
        "one_process_child_replay": child_replay,
        "offline_wrapper_sha256": sha(SELF), "fast_wrapper_sha256": sha(FAST),
        "fast_descriptor_helper_sha256": sha(FAST_HELPER),
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "implementation_hashes": cert["implementation_hashes"],
        "api_client_sha256": sha(API), "official_api_review": api_review_pins(),
        "wire_sha256": sha_bytes(wire), "solution_sha256": sha(solution),
        "metadata_sha256": sha(CANDIDATE / "academic-metadata.json.txt"),
        "descriptor_sha256": sha_bytes(encode(descriptor)),
        "multipart_sha256": sha_bytes(multipart), "multipart_content_type": ctype,
        "route": "/verify", "exact_existing_target_only": True,
        "creates_theorem_or_proposal": False,
        "durable_post_policy": "write verify_intent before POST; never repeat an existing intent",
        "expected_success_status": "ACCEPTED", "local_node_validated": True,
        "submission_ready": False, "proposal_status": "Draft", "API_used": False}
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "verification-payload.json", encode(descriptor))
    exact(DEST / "verification-request.multipart", multipart)
    exact(DEST / "metadata.json", (CANDIDATE / "academic-metadata.json.txt").read_bytes())
    exact(DEST / "wire-theorem-source.lean", wire)
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False,
            "creates_theorem_or_proposal": False,
            "descriptor_sha256": pins["descriptor_sha256"],
            "multipart_sha256": pins["multipart_sha256"]}


def hash_gate(frozen):
    child_replay = frozen["one_process_child_replay"]
    need(child_replay["full_child_mathematical_replays"] == 1
         and child_replay["same_process_child_reuses"] >= 1
         and child_replay["all_child_inputs_rehashed_before_and_after_each_reuse"] is True
         and child_replay["first_full_child_replay_not_skipped"] is True
         and sha(TASK / child_replay["child_certificate"]) ==
             child_replay["child_certificate_sha256"]
         and sha(TASK / child_replay["child_consumer"]) ==
             child_replay["child_consumer_sha256"],
         "AP17 one-process child replay evidence changed")
    direct = {CERT: frozen["validation_sha256"],
              FRESH: frozen["fresh_target"]["readback_sha256"],
              FRESH_RUNNER: frozen["fresh_target"]["runner_sha256"],
              stage.route.OPEN_RECORD: frozen["saved_open_record_sha256"],
              stage.route.OPEN_WIRE: frozen["saved_open_wire_sha256"],
              stage.route.PUBLICATION: frozen["saved_open_publication_sha256"],
              STAGE / "preparation.json": frozen["stage_preparation_sha256"],
              SELF: frozen["offline_wrapper_sha256"], FAST: frozen["fast_wrapper_sha256"],
              FAST_HELPER: frozen["fast_descriptor_helper_sha256"],
              Path(stage.__file__): frozen["stage_producer_sha256"],
              Path(consumer.__file__): frozen["strict_consumer_sha256"],
              API: frozen["api_client_sha256"]}
    for path, expected in direct.items():
        need(sha(path) == expected, "AP17 frozen implementation/evidence changed: " + str(path))
    for path, expected in frozen["stage_input_hashes"].items():
        need(sha(TASK / path) == expected, "AP17 frozen stage input changed: " + path)
    for path, expected in frozen["implementation_hashes"].items():
        need(sha(TASK / path) == expected,
             "AP17 frozen certificate implementation changed: " + path)
    for filename, expected in frozen["compiler_manifest_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP17 compiler manifest changed: " + filename)
    for value, expected in frozen["preflight_artifact_sha256"].items():
        need(sha(consumer.context.file(value)) == expected,
             "AP17 preflight artifact changed: " + value)
    for key, expected in frozen["dependency_olean_sha256"].items():
        need(sha(Path(key.split("|", 1)[1])) == expected,
             "AP17 dependency OLean changed: " + key)
    for filename, expected in frozen["output_json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP17 kernel/proof JSON changed: " + filename)
    need(sha(TASK / frozen["solution_olean"]) == frozen["solution_olean_sha256"],
         "AP17 solution OLean changed")
    need(sha(DEST / "validation.json") == frozen["validation_sha256"]
         and sha(DEST / "wire-theorem-source.lean") == frozen["wire_sha256"]
         and sha(DEST / "metadata.json") == frozen["metadata_sha256"]
         and sha(DEST / "verification-payload.json") == frozen["descriptor_sha256"]
         and sha(DEST / "verification-request.multipart") == frozen["multipart_sha256"],
         "AP17 frozen verification artifacts changed")
    need(api_review_pins() == frozen["official_api_review"],
         "AP17 reviewed API documents changed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-pending", action="store_true")
    modes.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(pending() if args.prepare_pending else prepare(),
                     ensure_ascii=False, indent=2))
