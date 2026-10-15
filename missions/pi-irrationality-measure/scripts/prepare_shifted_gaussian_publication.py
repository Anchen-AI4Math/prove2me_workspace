"""Prepare the AP13 shifted-Gaussian theorem payload without Lean or networking.

Pending preparation is available before compilation.  Final modes additionally
require the strict node certificate and an authoritative zero-match lookup saved
as ``verification/ap13/shifted-gaussian/exact-name-lookup.json``.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_shifted_gaussian_node as consumer
import publish_standalone_platform_node as publisher
import stage_shifted_gaussian_node as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v2"
CERT = STAGE / stage.CERTIFICATE
LOOKUP = STAGE / "exact-name-lookup.json"
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_shifted_gaussian_node.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
API_REVIEW_MANIFEST = API_REVIEW / "manifest.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value): return publisher.encode(value)
def need(ok, message):
    if not ok: raise ValueError(message)


def task_rel(path): return Path(path).resolve().relative_to(TASK.resolve()).as_posix()
def root_rel(path): return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen AP13 shifted-Gaussian artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(raw)


def metadata(prep):
    source = prep["metadata"]
    witness = {
        "source_commit": stage.COMMIT,
        "source_url": source["source_url"],
        "source_module": stage.TARGET_MODULE,
        "source_path": task_rel(stage.source_path()),
        "source_sha256": sha(stage.source_path()),
        "original_source_path": task_rel(stage.source_path("source")),
        "original_source_sha256": sha(stage.source_path("source")),
        "target_ast": prep["target_ast"],
        "target_source_command_sha256": prep["target_source_command_sha256"],
        "target_proof_suffix_sha256": prep["target_proof_suffix_sha256"],
        "source_total_AST_units": 9,
        "inline_helper_count": 8,
        "existing_port_adaptations": prep["existing_port_adaptations"],
        "mathematical_role": (
            "Clears all truncated-logarithm denominators and places the shifted "
            "product coefficient in the Gaussian-integer lattice used by the "
            "interpolation-matrix arithmetic bounds."
        ),
    }
    return {
        "theorem_name": stage.PLATFORM_NAME,
        "theorem_title": source["title"],
        "natural_language_statement": source["statement"],
        "explanation": source["explanation"],
        "tags": source["tags"],
        "source_witness": witness,
    }


def static():
    stage.check_only()
    prep = read(STAGE / "preparation.json")
    need(prep["source_name"] == stage.TARGET
         and prep["platform_name"] == stage.PLATFORM_NAME
         and prep["source_module"] == stage.TARGET_MODULE
         and prep["source_commit"] == stage.COMMIT
         and prep["source_total_AST_units"] == 9
         and prep["source_total_lines"] == 89
         and len(prep["graph_closure_names"]) == 9
         and len(prep["inline_helper_names"]) == 8
         and len(prep["inline_exact_source_units"]) == 8,
         "AP13 source identity/full closure differs")
    need(prep["global_solution_preserves_literal_port_proof"] is True
         and prep["all_helper_proofs_copied_from_immutable_port"] is True
         and prep["all_helper_proofs_literal_original"] is False,
         "AP13 literal target/helper provenance differs")
    adaptations = read(STAGE / "port-adaptation.json")
    need(prep["existing_port_adaptations"] == adaptations and len(adaptations) == 1
         and adaptations[0]["name"] ==
             "OAI.PiExponent.Arithmetic.lcm_mul_log_coeff_gaussian"
         and adaptations[0]["original_proof_step"] ==
             "rw [PowerSeries.coeff_log, ite_eq_right hk0, hm]"
         and adaptations[0]["ported_proof_step"] ==
             "rw [PowerSeries.coeff_log, if_neg hk0, hm]"
         and adaptations[0]["statement_unchanged"] is True
         and adaptations[0]["existing_port_not_modified"] is True,
         "AP13 unique existing if_neg compatibility edit differs")
    rows = prep["inline_exact_source_units"] + [prep["target_exact_source_unit"]]
    need([row["name"] for row in rows] == prep["source_type_only_names"]
         and sum(not row["original_port_command_equal_modulo_line_endings"] for row in rows) == 1
         and next(row for row in rows if not row["original_port_command_equal_modulo_line_endings"])["name"] ==
             adaptations[0]["name"],
         "AP13 full source declaration/type domain or adaptation domain differs")
    need(list(prep["files"]) == stage.FILES
         and [prep["files"][x]["mode"] for x in stage.FILES] == stage.MODES
         and [prep["files"][x]["imports"] for x in stage.FILES] ==
             [stage.IMPORTS, stage.IMPORTS,
              ["Lean", stage.TARGET_MODULE], ["Lean", stage.SOLUTION_MODULE]],
         "AP13 ordered compiler contract differs")

    statement = STAGE / stage.TARGET_OUTPUT
    assembled = (prep["preamble"] + prep["formal_statement"]).encode()
    need(statement.read_bytes() == assembled
         and (STAGE / "wire-theorem-source.lean").read_bytes() == assembled,
         "AP13 preamble/formal statement is not the complete comparator")
    command = (STAGE / "original-target-command.lean.txt").read_bytes()
    unit = prep["target_ast"]
    ns = unit["nameRange"]["start"]["offset"] - unit["start"]["offset"]
    ne = unit["nameRange"]["end"]["offset"] - unit["start"]["offset"]
    renamed = command[:ns] + b"solution" + command[ne:]
    solution = STAGE / stage.SOLUTION_OUTPUT
    raw = solution.read_bytes()
    need(raw.endswith(renamed + b"\n")
         and renamed[renamed.find(b":= by"):] ==
             command[unit["valueStart"]["offset"] - unit["start"]["offset"]:]
         and b"sorry" not in raw,
         "AP13 global solution does not preserve the literal target port proof")
    before = raw[:-len(renamed) - 1]
    need(b"theorem solution" not in before
         and before.rstrip().endswith(b"open OAI.PiExponent.Arithmetic"),
         "AP13 solution is not the unique final global theorem")

    academic = metadata(prep)
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap13-shifted-gaussian-publication-manifest",
        "theorem_name": stage.PLATFORM_NAME,
        "preamble": prep["preamble"], "formal_statement": prep["formal_statement"],
        "statement": root_rel(statement), "statement_sha256": sha(statement),
        "platform_statement_assembly_sha256": sha_bytes(assembled),
        "comparator_namespace_suffix_sha256": sha_bytes(b""),
        "solution": root_rel(solution), "solution_sha256": sha(solution),
        "source_commit": stage.COMMIT, "source_url": prep["metadata"]["source_url"],
        "source_module": stage.TARGET_MODULE,
        "source_ast_unit_sha256": prep["target_source_command_sha256"],
        "inline_exact_source_command_count": 8, "graph_closure_count": 9,
        "existing_port_adaptation_count": 1,
        "proposal_status": "Draft", "validated": CERT.is_file(),
        "local_standalone_validated": CERT.is_file(),
        "submission_ready": False, "full_tree_ready": False,
    }
    payloads = publisher.payloads(DEST, manifest, academic)
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    verify = json.loads(payloads["verification-payload.json"])
    need((problem["preamble"] + problem["formal_statement"]).encode() == assembled
         and problem["theorem_name"] == stage.PLATFORM_NAME
         and verify["theorem_id"] is None
         and verify["target_theorem_name"] == stage.PLATFORM_NAME
         and verify["file"]["utf8"].encode() == raw,
         "AP13 payload changes exact statement or solution bytes")
    return prep, manifest, academic, payloads, assembled


def lookup_guard():
    need(LOOKUP.is_file(), "AP13 authoritative exact-name lookup is pending")
    doc = read(LOOKUP)
    rows = [row for row in doc.get("records", [])
            if row.get("theorem_name") == stage.PLATFORM_NAME]
    need(doc.get("read_only") is True and doc.get("environment") == publisher.ENV
         and len(rows) == 1 and rows[0].get("http_status") == 200
         and rows[0].get("matches") == [],
         "AP13 exact-name lookup does not certify zero matches")


def replay(cert, prep):
    need(consumer.validate() == cert, "AP13 certificate differs from strict replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap13-shifted-gaussian-node-validation"
         and cert["validated"] is True and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False
         and cert["source_name"] == stage.TARGET
         and cert["platform_name"] == stage.PLATFORM_NAME
         and cert["source_module"] == stage.TARGET_MODULE
         and cert["source_byte_range"] == [12720, 13370]
         and cert["solution_module"] == stage.SOLUTION_MODULE,
         "AP13 certificate identity/state differs")
    need(cert["preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["target_wire_sha256"] == sha(STAGE / stage.TARGET_OUTPUT)
         and cert["solution_source_sha256"] == sha(STAGE / stage.SOLUTION_OUTPUT)
         and cert["existing_port_adaptations"] == prep["existing_port_adaptations"]
         and cert["literal_target_port_proof_preserved"] is True
         and cert["all_helpers_literal_original"] is False
         and cert["source_and_generated_types_equal"] is True
         and cert["source_and_generated_theorem_values_null"] is True
         and cert["source_and_generated_actual_proof_references_paired"] is True
         and cert["Std3_only"] is True,
         "AP13 exact type/proof/adaptation gates differ")
    need(set(cert["preflights"]) == set(stage.FILES)
         and 0 < cert["max_file_seconds"] <= 300
         and set(cert["actual_provider_bindings"]) == {"arithmetic"},
         "AP13 preflight/provider domain differs")
    for rows in cert["axioms"].values():
        for axioms in rows.values(): need(set(axioms) <= STD3, "AP13 nonstandard axiom")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP13 implementation changed: " + path)
    for filename, expected in cert["json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP13 kernel/proof JSON changed: " + filename)
    need(sha(TASK / cert["solution_olean"]) == cert["solution_olean_sha256"],
         "AP13 solution OLean changed")


def evidence_hashes(cert):
    found = {}
    for row in cert["preflights"].values():
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
                 "AP13 dependency OLean changed during compilation")
            found[dep["module"] + "|" + dep["path"]] = dep["sha256_before"]
    return dict(sorted(found.items()))


def api_review_pins():
    review = read(API_REVIEW_MANIFEST)
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and docs["references/contribute.md"] == sha(API_REVIEW / "references/contribute.md")
         and docs["references/prove.md"] == sha(API_REVIEW / "references/prove.md"),
         "Reviewed official API docs differ")
    return {"official_tag": review["official_tag"], "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW_MANIFEST),
            "contribute_sha256": docs["references/contribute.md"],
            "prove_sha256": docs["references/prove.md"]}


def pending():
    prep, manifest, academic, payloads, assembled = static()
    exact(DEST / "metadata.json", encode(academic))
    exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items(): exact(DEST / name, raw)
    record = {"schema_version": 1,
        "artifact_kind": "ap13-shifted-gaussian-pending-publication",
        "theorem_name": stage.PLATFORM_NAME,
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "publication_manifest_sha256": sha_bytes(encode(manifest)),
        "metadata_sha256": sha_bytes(encode(academic)),
        "wire_theorem_sha256": sha_bytes(assembled),
        "solution_sha256": manifest["solution_sha256"],
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "strict_validation_pending": not CERT.is_file(),
        "exact_name_lookup_pending": not LOOKUP.is_file(),
        "network_used": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft"}
    exact(DEST / "pending-preparation.json", encode(record))
    return {"prepared": True, "validation_pending": not CERT.is_file(),
            "exact_name_lookup_pending": not LOOKUP.is_file(), "network_used": False,
            "proposal_status": "Draft", "payload_sha256": record["payload_sha256"]}


def prepare():
    prep, manifest, academic, payloads, assembled = static()
    lookup_guard()
    need(CERT.is_file(), "AP13 strict actual certificate is pending")
    cert = read(CERT); replay(cert, prep)
    pins = {"schema_version": 1,
        "artifact_kind": "ap13-shifted-gaussian-publication-preparation",
        "theorem_name": stage.PLATFORM_NAME, "environment": publisher.ENV,
        "manifest_sha256": sha_bytes(encode(manifest)), "validation_sha256": sha(CERT),
        "exact_name_lookup_sha256": sha(LOOKUP),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "offline_wrapper_sha256": sha(SELF),
        "online_wrapper_sha256": sha(ONLINE),
        "publisher_sha256": sha(Path(publisher.__file__)),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "metadata_sha256": sha_bytes(encode(academic)),
        "wire_theorem_sha256": manifest["platform_statement_assembly_sha256"],
        "compiled_comparator_sha256": manifest["statement_sha256"],
        "solution_sha256": manifest["solution_sha256"],
        "target_source_command_sha256": prep["target_source_command_sha256"],
        "target_proof_suffix_sha256": prep["target_proof_suffix_sha256"],
        "existing_port_adaptations_sha256": sha_bytes(encode(prep["existing_port_adaptations"])),
        "runtime_sha256": sha(stage.RUNTIME),
        "ordered_imports": {name: prep["files"][name]["imports"] for name in stage.FILES},
        "compiler_manifest_sha256": {prep["files"][name]["manifest"]:
                                      sha(STAGE / prep["files"][name]["manifest"])
                                      for name in stage.FILES},
        "stage_input_hashes": prep["input_hashes"],
        "preflight_artifact_sha256": evidence_hashes(cert),
        "dependency_olean_sha256": dependency_oleans(cert),
        "output_json_sha256": cert["json_sha256"],
        "solution_olean": cert["solution_olean"],
        "solution_olean_sha256": cert["solution_olean_sha256"],
        "actual_provider_bindings": cert["actual_provider_bindings"],
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "official_api_review": api_review_pins(),
        "local_node_validated": True, "submission_ready": False,
        "full_tree_ready": False, "proposal_status": "Draft",
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "durable_post_policy": "saved publish_intent before POST; never repeat a recorded intent",
        "API_used": False}
    exact(DEST / "manifest.json", encode(manifest)); exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", encode(academic)); exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items(): exact(DEST / name, raw)
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": pins["payload_sha256"]}


def check():
    result = prepare()
    frozen = read(DEST / "preparation.json")
    manifest = read(DEST / "manifest.json")
    hash_gate(manifest, frozen)
    return {"checked": True, **{k: v for k, v in result.items() if k != "prepared"}}


def hash_gate(current_manifest, frozen):
    need(current_manifest == read(DEST / "manifest.json")
         and sha_bytes(encode(current_manifest)) == frozen["manifest_sha256"],
         "AP13 frozen manifest differs")
    direct = {CERT: frozen["validation_sha256"], LOOKUP: frozen["exact_name_lookup_sha256"],
              STAGE / "preparation.json": frozen["stage_preparation_sha256"],
              SELF: frozen["offline_wrapper_sha256"], ONLINE: frozen["online_wrapper_sha256"],
              Path(publisher.__file__): frozen["publisher_sha256"],
              ROOT / "scripts/p2m_api.py": frozen["api_client_sha256"],
              Path(stage.__file__): frozen["stage_producer_sha256"],
              Path(consumer.__file__): frozen["strict_consumer_sha256"]}
    for path, expected in direct.items():
        need(sha(path) == expected, "AP13 frozen implementation/evidence changed: " + str(path))
    for path, expected in frozen["stage_input_hashes"].items():
        need(sha(TASK / path) == expected, "AP13 frozen stage input changed: " + path)
    for filename, expected in frozen["compiler_manifest_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP13 frozen compiler manifest changed: " + filename)
    for value, expected in frozen["preflight_artifact_sha256"].items():
        need(sha(consumer.context.file(value)) == expected, "AP13 frozen preflight changed: " + value)
    for key, expected in frozen["dependency_olean_sha256"].items():
        need(sha(Path(key.split("|", 1)[1])) == expected, "AP13 frozen dependency changed: " + key)
    for filename, expected in frozen["output_json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP13 frozen kernel/proof JSON changed: " + filename)
    need(sha(TASK / frozen["solution_olean"]) == frozen["solution_olean_sha256"],
         "AP13 frozen solution OLean changed")
    need(api_review_pins() == frozen["official_api_review"], "AP13 reviewed API docs changed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-pending", action="store_true")
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(pending() if args.prepare_pending else prepare() if args.prepare_only else check(),
                     ensure_ascii=False, indent=2))
