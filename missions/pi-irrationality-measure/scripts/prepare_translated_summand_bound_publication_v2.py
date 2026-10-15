"""Prepare the corrected AP18 translated-summand publication offline.

Final preparation requires the genuine four-context node certificate and the
saved read-only exact-name lookup.  It performs one complete strict replay in
this process, then freezes every certificate-bound input for hash-only HTTP
guards.  This module never imports the API client or performs networking.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_translated_summand_bound_node_v2 as consumer
import publish_standalone_platform_node as payload_builder
import stage_translated_summand_bound_node_v2 as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v2"
CERT = STAGE / stage.CERTIFICATE
LOOKUP = STAGE / "exact-name-lookup.json"
LOOKUP_RUNNER = TASK / "scripts/check_translated_summand_bound_platform_name.py"
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_translated_summand_bound_node_v2.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
API_REVIEW_MANIFEST = API_REVIEW / "manifest.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value): return payload_builder.encode(value)
def need(ok, message):
    if not ok: raise ValueError(message)


def task_rel(path): return Path(path).resolve().relative_to(TASK.resolve()).as_posix()
def root_rel(path): return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen AP18 translated-summand artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def resolve_task_or_absolute(value):
    path = Path(value)
    return path if path.is_absolute() else TASK / path


def metadata(prep):
    source = read(STAGE / "academic-metadata.json")
    need(set(source) == {"title", "statement", "explanation", "source_commit",
                         "source_url", "tags"}
         and source["source_commit"] == stage.COMMIT,
         "AP18 academic metadata schema/source commit differs")
    return {
        "theorem_name": stage.PLATFORM_NAME,
        "theorem_title": source["title"],
        "natural_language_statement": source["statement"],
        "explanation": source["explanation"],
        "tags": source["tags"],
        "source_witness": {
            "commit": stage.COMMIT,
            "source_url": source["source_url"],
            "source_module": stage.TARGET_MODULE,
            "source_name": stage.TARGET,
            "source_byte_range": [4397, 5770],
            "original_proof_AST_units": 6,
            "original_source_lines": 110,
            "target_source_command_sha256": prep["inline_exact_source_units"][-1]["command_sha256"],
            "target_proof_suffix_sha256": prep["inline_exact_source_units"][-1]["proof_suffix_sha256"],
            "port_source": prep["inline_exact_source_units"][-1]["source"],
            "port_source_sha256": prep["inline_exact_source_units"][-1]["source_sha256"],
            "original_source": prep["inline_exact_source_units"][-1]["original"],
            "original_source_sha256": prep["inline_exact_source_units"][-1]["original_sha256"],
            "mathematical_role": (
                "Combines a collision-occupancy alternative with the scalar and "
                "determinant exponential estimates for one translated summand."
            ),
        },
    }


def static():
    need((STAGE / "preparation.json").is_file(), "AP18 corrected node preparation is pending")
    prep = read(STAGE / "preparation.json")
    need(prep["artifact_kind"] == "ap18-translated-summand-node-preparation"
         and prep["source_name"] == stage.TARGET
         and prep["platform_name"] == stage.PLATFORM_NAME
         and prep["source_module"] == stage.TARGET_MODULE
         and prep["source_commit"] == stage.COMMIT
         and prep["solution_module"] == stage.SOLUTION_MODULE
         and prep["original_proof_AST_units"] == 6
         and prep["original_source_lines"] == 110
         and len(prep["inline_exact_source_units"]) == 6
         and len(prep["inline_helper_names"]) == 5
         and len(prep["graph_closure_names"]) == 8
         and len(prep["provider_subtracted_names"]) == 2
         and prep["all_original_proof_suffixes_unchanged"] is True
         and prep["only_target_binding_name_changed"] is True
         and prep["existing_port_adaptations"] == []
         and prep["comparator_namespace_open_only_imported_OAI_PiExponent"] is True
         and prep["sum_weight_closed_child_module"] ==
             "Theorems.Thm_OAI_PiExponent_Collision_sum_weight_ge_of_low_count_le"
         and prep["multiplicity_Published_and_fullDef_certificate_pending"] is False
         and prep["sum_weight_Accepted_closed_child_pending"] is False
         and prep["compiler_manifests_finalized"] is True
         and prep["compiled"] is False and prep["validated"] is False
         and prep["submission_ready"] is False and prep["proposal_status"] == "Draft",
         "AP18 corrected source/provenance/final compiler contract differs")
    need(prep["preamble"].endswith("open OAI.PiExponent\n\n")
         and "open OAI.PiExponent.DeterminantAnalyticBound" not in prep["preamble"],
         "AP18 comparator opens a namespace not created by its actual imports")
    rows = prep["inline_exact_source_units"]
    need(prep["source_type_only_names"] == [row["name"] for row in rows]
         and prep["generated_type_only_names"] ==
             [row["name"] for row in rows[:-1]] + ["solution"],
         "AP18 complete six-theorem TypeOnly domain differs")

    statement = STAGE / stage.TARGET_OUTPUT
    solution = STAGE / stage.SOLUTION_OUTPUT
    assembled = (prep["preamble"] + prep["formal_statement"]).encode("utf-8")
    need(statement.read_bytes() == assembled
         and (STAGE / "wire-theorem-source.lean").read_bytes() == assembled,
         "AP18 exact preamble/formal comparator bytes differ")
    raw_solution = solution.read_bytes()
    predecessor_solution = stage.SOURCE_ROUTE_STAGE / "Solutions/Sol_translated_summand_bound_ap18.lean"
    need(raw_solution == predecessor_solution.read_bytes()
         and raw_solution.count(b"theorem solution") == 1
         and b"sorry" not in raw_solution,
         "AP18 corrected node changed the literal source proof solution")
    need(list(prep["files"]) == stage.FILES
         and [prep["files"][name]["mode"] for name in stage.FILES] == stage.MODES,
         "AP18 four-context file/mode order differs")

    academic = metadata(prep)
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap18-translated-summand-bound-publication-manifest-v2",
        "theorem_name": stage.PLATFORM_NAME,
        "preamble": prep["preamble"],
        "formal_statement": prep["formal_statement"],
        "statement": root_rel(statement),
        "statement_sha256": sha(statement),
        "platform_statement_assembly_sha256": sha_bytes(assembled),
        "comparator_namespace_suffix_sha256": sha_bytes(b""),
        "solution": root_rel(solution),
        "solution_sha256": sha(solution),
        "source_commit": stage.COMMIT,
        "source_url": academic["source_witness"]["source_url"],
        "source_module": stage.TARGET_MODULE,
        "original_proof_AST_units": 6,
        "original_source_lines": 110,
        "inline_exact_source_command_count": 5,
        "graph_closure_count": 8,
        "provider_subtracted_count": 2,
        "existing_port_adaptation_count": 0,
        "proposal_status": "Draft",
        "validated": CERT.is_file(),
        "local_standalone_validated": CERT.is_file(),
        "submission_ready": False,
        "full_tree_ready": False,
    }
    payloads = payload_builder.payloads(DEST, manifest, academic)
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    verify = json.loads(payloads["verification-payload.json"])
    need((problem["preamble"] + problem["formal_statement"]).encode("utf-8") == assembled
         and problem["theorem_name"] == stage.PLATFORM_NAME
         and verify["theorem_id"] is None
         and verify["target_theorem_name"] == stage.PLATFORM_NAME
         and verify["file"]["utf8"].encode("utf-8") == raw_solution,
         "AP18 publication payload changes exact theorem or solution bytes")
    return prep, manifest, academic, payloads, assembled


def lookup_guard(manifest):
    need(LOOKUP.is_file(), "AP18 authoritative exact-name lookup is pending")
    doc = read(LOOKUP)
    need(doc.get("artifact_kind") ==
             "ap18-translated-summand-read-only-exact-name-lookup"
         and doc.get("read_only") is True
         and doc.get("environment") == payload_builder.ENV
         and doc.get("theorem_name") == stage.PLATFORM_NAME
         and doc.get("request_methods") == ["GET"]
         and doc.get("credentials_or_tokens_recorded") is False
         and isinstance(doc.get("pages"), list) and doc["pages"]
         and isinstance(doc.get("matches"), list) and len(doc["matches"]) <= 1
         and isinstance(doc.get("readbacks"), list)
         and len(doc["readbacks"]) == len(doc["matches"]),
         "AP18 exact-name lookup schema/scope differs")
    for row in doc["pages"] + doc["readbacks"]:
        raw = row.get("raw_body_utf8")
        need(row.get("http_status") == 200 and isinstance(raw, str)
             and row.get("raw_body_sha256") == sha_bytes(raw.encode("utf-8"))
             and json.loads(raw) == row.get("parsed_body"),
             "AP18 saved exact-name GET bytes differ")
    for row in doc["readbacks"]:
        body = row["parsed_body"]
        need(body.get("theorem_name") == stage.PLATFORM_NAME
             and body.get("mathlib_rev") == payload_builder.ENV
             and body.get("visibility") == "public"
             and body.get("deprecated_at") is None
             and body.get("preamble") == manifest["preamble"]
             and body.get("formal_statement") == manifest["formal_statement"],
             "AP18 existing exact-name target has different public wire")
    return len(doc["matches"])


def replay(cert, prep):
    actual = consumer.validate()
    need(stage.encode(actual) == CERT.read_bytes() and actual == cert,
         "AP18 node certificate differs from its one complete strict replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap18-translated-summand-bound-node-validation"
         and cert["validated"] is True and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False
         and cert["source_name"] == stage.TARGET
         and cert["platform_name"] == stage.PLATFORM_NAME
         and cert["source_module"] == stage.TARGET_MODULE
         and cert["source_byte_range"] == [4397, 5770]
         and cert["solution_module"] == stage.SOLUTION_MODULE
         and cert["preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["target_wire_sha256"] == sha(STAGE / stage.TARGET_OUTPUT)
         and cert["solution_source_sha256"] == sha(STAGE / stage.SOLUTION_OUTPUT)
         and cert["original_proof_AST_units"] == 6
         and cert["original_source_lines"] == 110
         and cert["all_original_proof_suffixes_unchanged"] is True
         and cert["only_target_binding_name_changed"] is True
         and cert["existing_port_adaptations"] == []
         and cert["source_and_generated_types_equal"] is True
         and cert["source_and_generated_theorem_values_null"] is True
         and cert["source_and_generated_actual_proof_references_equal"] is True
         and cert["no_private_sum_weight_helper_leakage"] is True
         and cert["sum_weight_actual_Accepted_theorem_id"] ==
             "84999320-3725-4c17-b1cb-428d9f92f6cc"
         and cert["sum_weight_actual_Accepted_proof_id"] ==
             "78ad72fd-0fdd-44e6-93c7-f0e607baa6fa"
         and cert["sum_weight_mirror_certificate_sha256"] ==
             sha(stage.CHILD_CERTIFICATE)
         and cert["multiplicity_actual_Published_definition_id"] ==
             stage.MULTIPLICITY_ID
         and cert["multiplicity_Published_record_sha256"] ==
             stage.MULTIPLICITY_RECORD_SHA
         and cert["same_process_fixed_boundary_replay_cache"] is True
         and cert["first_full_boundary_mathematical_replays_required"] is True
         and cert["Std3_only"] is True
         and set(cert["preflights"]) == set(stage.FILES)
         and 0 < cert["max_file_seconds"] <= 300,
         "AP18 strict type/reference/parent/Std3 certificate gates differ")
    for rows in cert["axioms"].values():
        for axioms in rows.values():
            need(set(axioms) <= STD3, "AP18 nonstandard axiom")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP18 implementation changed: " + path)
    for filename, expected in cert["json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP18 kernel/proof JSON changed: " + filename)
    need(sha(TASK / cert["solution_olean"]) == cert["solution_olean_sha256"],
         "AP18 solution OLean changed")
    need(prep["boundary_certificates"]["sum_weight"]["sha256"] ==
             cert["sum_weight_mirror_certificate_sha256"]
         and prep["boundary_certificates"]["multiplicity"]["sha256"] ==
             cert["multiplicity_fullDef_certificate_sha256"],
         "AP18 preparation and strict certificate bind different parents")


def evidence_hashes(cert):
    found = {}
    for row in cert["preflights"].values():
        found[row["record"]] = row["record_sha256"]
        for key in ("source", "manifest", "log"):
            value = row["data"].get(key)
            if value:
                path = Path(value) if Path(value).is_absolute() else consumer.context.file(value)
                found[value] = sha(path)
    return dict(sorted(found.items()))


def dependency_oleans(cert):
    found = {}
    for row in cert["preflights"].values():
        for dep in row["data"]["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"],
                 "AP18 dependency OLean changed during compilation")
            found[dep["module"] + "|" + dep["path"]] = dep["sha256_before"]
    return dict(sorted(found.items()))


def api_review_pins():
    review = read(API_REVIEW_MANIFEST)
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and all(sha(API_REVIEW / name) == expected for name, expected in docs.items()),
         "Reviewed official API documents differ")
    return {"official_tag": review["official_tag"],
            "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW_MANIFEST),
            "documents": docs}


def prepare():
    prep, manifest, academic, payloads, assembled = static()
    prior_matches = lookup_guard(manifest)
    need(CERT.is_file(), "AP18 genuine four-context strict certificate is pending")
    cert = read(CERT)
    replay(cert, prep)  # the one complete mathematical replay in this process
    pins = {
        "schema_version": 1,
        "artifact_kind": "ap18-translated-summand-bound-publication-preparation-v2",
        "theorem_name": stage.PLATFORM_NAME,
        "environment": payload_builder.ENV,
        "manifest_sha256": sha_bytes(encode(manifest)),
        "validation_sha256": sha(CERT),
        "exact_name_lookup_sha256": sha(LOOKUP),
        "exact_name_lookup_runner_sha256": sha(LOOKUP_RUNNER),
        "authoritative_prior_exact_match_count": prior_matches,
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "offline_wrapper_sha256": sha(SELF),
        "online_wrapper_sha256": sha(ONLINE),
        "payload_builder_sha256": sha(Path(payload_builder.__file__)),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "metadata_sha256": sha_bytes(encode(academic)),
        "wire_theorem_sha256": sha_bytes(assembled),
        "compiled_comparator_sha256": manifest["statement_sha256"],
        "solution_sha256": manifest["solution_sha256"],
        "runtime_sha256": sha(stage.RUNTIME),
        "ordered_imports": {name: prep["files"][name]["imports"] for name in stage.FILES},
        "compiler_manifest_sha256": {
            prep["files"][name]["manifest"]: sha(STAGE / prep["files"][name]["manifest"])
            for name in stage.FILES},
        "stage_input_hashes": prep["input_hashes"],
        "boundary_dependency_olean_sha256": prep["boundary_dependency_olean_sha256"],
        "preflight_artifact_sha256": evidence_hashes(cert),
        "dependency_olean_sha256": dependency_oleans(cert),
        "output_json_sha256": cert["json_sha256"],
        "implementation_hashes": cert["implementation_hashes"],
        "fixed_boundary_input_hashes": cert["fixed_boundary_input_hashes"],
        "solution_olean": cert["solution_olean"],
        "solution_olean_sha256": cert["solution_olean_sha256"],
        "sum_weight_actual_Accepted_theorem_id":
            cert["sum_weight_actual_Accepted_theorem_id"],
        "sum_weight_actual_Accepted_proof_id": cert["sum_weight_actual_Accepted_proof_id"],
        "sum_weight_mirror_certificate_sha256":
            cert["sum_weight_mirror_certificate_sha256"],
        "multiplicity_actual_Published_definition_id":
            cert["multiplicity_actual_Published_definition_id"],
        "multiplicity_Published_record_sha256":
            cert["multiplicity_Published_record_sha256"],
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "official_api_review": api_review_pins(),
        "one_complete_strict_replay_performed": True,
        "subsequent_HTTP_guards_are_hash_only": True,
        "local_node_validated": True,
        "submission_ready": False,
        "proposal_status": "Draft",
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "durable_post_policy": "intent saved before each POST; never repeat an uncertain POST",
        "API_used": False,
    }
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", encode(academic))
    exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items(): exact(DEST / name, raw)
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False,
            "one_complete_strict_replay_performed": True,
            "proposal_status": "Draft", "payload_sha256": pins["payload_sha256"]}


def hash_gate(manifest, frozen):
    need(manifest == read(DEST / "manifest.json")
         and sha_bytes(encode(manifest)) == frozen["manifest_sha256"],
         "AP18 frozen publication manifest differs")
    direct = {
        CERT: frozen["validation_sha256"],
        LOOKUP: frozen["exact_name_lookup_sha256"],
        LOOKUP_RUNNER: frozen["exact_name_lookup_runner_sha256"],
        STAGE / "preparation.json": frozen["stage_preparation_sha256"],
        SELF: frozen["offline_wrapper_sha256"],
        ONLINE: frozen["online_wrapper_sha256"],
        Path(payload_builder.__file__): frozen["payload_builder_sha256"],
        ROOT / "scripts/p2m_api.py": frozen["api_client_sha256"],
        Path(stage.__file__): frozen["stage_producer_sha256"],
        Path(consumer.__file__): frozen["strict_consumer_sha256"],
    }
    for path, expected in direct.items():
        need(sha(path) == expected, "AP18 frozen implementation/evidence changed: " + str(path))
    for path, expected in frozen["stage_input_hashes"].items():
        need(sha(TASK / path) == expected, "AP18 frozen stage input changed: " + path)
    for path, expected in frozen["boundary_dependency_olean_sha256"].items():
        need(sha(Path(path)) == expected, "AP18 frozen boundary OLean changed: " + path)
    for path, expected in frozen["fixed_boundary_input_hashes"].items():
        need(sha(resolve_task_or_absolute(path)) == expected,
             "AP18 frozen complete parent replay input changed: " + path)
    for path, expected in frozen["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP18 frozen strict implementation changed: " + path)
    for filename, expected in frozen["compiler_manifest_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP18 frozen compiler manifest changed: " + filename)
    for value, expected in frozen["preflight_artifact_sha256"].items():
        path = Path(value) if Path(value).is_absolute() else consumer.context.file(value)
        need(sha(path) == expected, "AP18 frozen preflight artifact changed: " + value)
    for key, expected in frozen["dependency_olean_sha256"].items():
        need(sha(Path(key.split("|", 1)[1])) == expected,
             "AP18 frozen imported OLean changed: " + key)
    for filename, expected in frozen["output_json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP18 frozen kernel/proof JSON changed: " + filename)
    need(sha(TASK / frozen["solution_olean"]) == frozen["solution_olean_sha256"],
         "AP18 frozen solution OLean changed")
    need((DEST / "validation.json").read_bytes() == CERT.read_bytes()
         and sha(DEST / "metadata.json") == frozen["metadata_sha256"]
         and sha(DEST / "wire-theorem-source.lean") == frozen["wire_theorem_sha256"],
         "AP18 frozen publication evidence copies differ")
    for name, expected in frozen["payload_sha256"].items():
        need(sha(DEST / name) == expected, "AP18 frozen payload changed: " + name)
    need(api_review_pins() == frozen["official_api_review"],
         "AP18 reviewed official API documents changed")


def frozen():
    pins = read(DEST / "preparation.json")
    manifest = read(DEST / "manifest.json")
    hash_gate(manifest, pins)
    metadata_value = read(DEST / "metadata.json")
    payloads = {}
    for name in pins["payload_sha256"]:
        payloads[name] = (DEST / name).read_bytes()
    return manifest, metadata_value, payloads, pins


def check():
    result = prepare()
    frozen()
    return {"checked": True, **{k: v for k, v in result.items() if k != "prepared"}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(prepare() if args.prepare_only else check(),
                     ensure_ascii=False, indent=2))
