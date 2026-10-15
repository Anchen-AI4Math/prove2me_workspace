"""Prepare the AP15 selected-minor clearing theorem payload without Lean or networking.

Pending preparation is available before compilation.  Final modes additionally
require the strict node certificate and an authoritative zero-match lookup saved
as ``verification/ap15/selected-minor-clearing-bound/exact-name-lookup.json``.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_selected_minor_clearing_bound_node as consumer
import publish_standalone_platform_node as publisher
import stage_selected_minor_clearing_bound_node as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v4"
CERT = STAGE / stage.CERTIFICATE
LOOKUP = STAGE / "exact-name-lookup.json"
LOOKUP_RUNNER = TASK / "scripts/check_selected_minor_clearing_bound_platform_name.py"
SCALES_PUBLICATION = stage.scales.STAGE / "publication-v2/publication.json"
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_selected_minor_clearing_bound_node.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
API_REVIEW_MANIFEST = API_REVIEW / "manifest.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_EXTERNAL_INSTANCE_DIFFERENCES = {
    "OAI.PiExponent.Arithmetic.gaussian_norm_one_le": {
        "source_only": ["AddGroup.existsAddOfLE", "Complex.instNormedField",
            "FloorRing.toFloorSemiring", "FloorSemiring.instCharZero",
            "NeZero.charZero_one", "NormedField.toNormedCommRing",
            "Real.instAddGroup", "Real.instFloorRing"],
        "generated_only": ["CommCStarAlgebra.toNormedCommRing",
            "CommRing.toNonUnitalCommRing", "NeZero.one",
            "NonUnitalCommRing.toNonUnitalCommSemiring",
            "NonUnitalCommSemiring.toNonUnitalSemiring", "Real.instNontrivial",
            "Real.instStarOrderedRing", "StarOrderedRing.toExistsAddOfLE",
            "instCommCStarAlgebraComplex", "instStarRingReal"],
        "fields": ["valueRefs", "allUsedConstants"]},
    "OAI.PiExponent.Arithmetic.cleared_det_norm_bound": {
        "source_only": ["NormedCommRing.toNormedRing", "NormedField.toNormedCommRing"],
        "generated_only": ["CStarAlgebra.toNormedRing",
            "CommCStarAlgebra.toCStarAlgebra", "CommCStarAlgebra.toNormedCommRing",
            "instCommCStarAlgebraComplex"],
        "fields": ["valueRefs", "allUsedConstants"]},
    "OAI.PiExponent.MatrixArithmetic.log_columnScale": {
        "source_only": ["NormMulClass.toNoZeroDivisors",
            "NormedCommRing.toNormedRing", "NormedDivisionRing.toNormMulClass",
            "NormedField.toNormedDivisionRing", "Real.normedCommRing",
            "Real.normedField", "isReduced_of_noZeroDivisors"],
        "generated_only": ["IsFormallyReal.instIsReduced",
            "IsFormallyReal.instOfIsStrictOrderedRing", "Real.instIsStrictOrderedRing"],
        "fields": ["valueRefs", "allUsedConstants"]},
}


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
        raise ValueError("Frozen AP15 selected-minor clearing artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(raw)


def metadata(prep):
    source = prep["metadata"]
    statement = (
        source["statement"] + "\n\n"
        "Here $m,K\\in\\mathbb{N}$; $w_0,v_0,\\theta,F,H\\in\\mathbb{R}$; "
        "$p:\\operatorname{Fin}(m)\\to\\mathbb{Z}$; "
        "$q:\\operatorname{Fin}(m)\\to\\mathbb{N}$ with $q_i\\ge 2$; "
        "$w_0>0$; and the selection maps the source row index set to the "
        "source column index set.  If the selected minor $M_{\\mathrm{sel}}$ "
        "has nonzero determinant, then, with $r$ its row count, $D$ the "
        "source common denominator, and $C_{\\mathrm{col}},C_{\\mathrm{row}}$ "
        "the source column and row costs,\n\n"
        "$$-r\\log D-C_{\\mathrm{col}}+C_{\\mathrm{row}}"
        "\\leq\\log\\lVert\\det M_{\\mathrm{sel}}\\rVert.$$"
    )
    explanation = (
        source["explanation"] + "  The positive row and column scales clear "
        "each selected entry into a Gaussian integer after multiplication by "
        "the common denominator.  The nonzero Gaussian-integer determinant "
        "has norm at least one; expanding the logarithms of the scale products "
        "gives exactly the row-count, row-cost, and column-cost terms above."
    )
    witness = {
        "source_commit": stage.COMMIT,
        "source_url": source["source_url"],
        "source_module": stage.TARGET_MODULE,
        "source_path": task_rel(stage.base.source_path(stage.TARGET_MODULE)),
        "source_sha256": sha(stage.base.source_path(stage.TARGET_MODULE)),
        "original_source_path": task_rel(stage.base.source_path(stage.TARGET_MODULE, "source")),
        "original_source_sha256": sha(stage.base.source_path(stage.TARGET_MODULE, "source")),
        "target_ast": prep["target_ast"],
        "target_source_command_sha256": prep["target_source_command_sha256"],
        "target_proof_suffix_sha256": prep["target_proof_suffix_sha256"],
        "original_route_AST_units": 19,
        "proof_AST_units_after_data_provider": 19,
        "inline_helper_count": 18,
        "genuine_lazy_equation_CI_count": 2,
        "provider_subtracted_names": prep["provider_subtracted_names"],
        "existing_port_adaptations": [],
        "mathematical_role": (
            "Clears denominators in a selected square interpolation minor and "
            "turns the Gaussian-integer determinant estimate into the stated "
            "logarithmic lower bound with row and column costs."
        ),
    }
    return {
        "theorem_name": stage.PLATFORM_NAME,
        "theorem_title": source["title"],
        "natural_language_statement": statement,
        "explanation": explanation,
        "tags": source["tags"],
        "source_witness": witness,
    }


def scales_publication_guard():
    need(SCALES_PUBLICATION.is_file(), "Published AP15 scales/costs evidence is pending")
    record = read(SCALES_PUBLICATION)
    provider = stage.scales.STAGE / stage.scales.PROVIDER_FILE
    provider_raw = provider.read_bytes()
    definition_id = record.get("definition_id")
    verdict = record.get("last_publish_verdict", {})
    verdict_body = verdict.get("body", {})
    readback = record.get("target_readback", {})
    body = readback.get("body", {})
    need(isinstance(definition_id, str) and bool(definition_id)
         and record.get("definition_name") ==
             "OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts"
         and record.get("environment") == publisher.ENV
         and record.get("publish_payload_sha256") ==
             sha(stage.scales.STAGE / "publication-v2/publish-payload.json")
         and record.get("publish_intent", {}).get("validation_sha256") ==
             sha(stage.scales.STAGE / "actual-provider-validation.json")
         and record.get("publish_intent", {}).get("bundle_source_sha256") == sha(provider)
         and verdict.get("http_status") == 200
         and verdict_body.get("status") == "PUBLISHED"
         and verdict_body.get("theorem_id") == definition_id
         and readback.get("http_status") == 200
         and body.get("theorem_id") == definition_id
         and body.get("theorem_name") == record["definition_name"]
         and body.get("status") == "Definition"
         and body.get("mathlib_rev") == publisher.ENV
         and body.get("definition", "").encode("utf-8") == provider_raw,
         "AP15 scales/costs Published record or exact public wire differs")
    return {"publication": task_rel(SCALES_PUBLICATION),
            "publication_sha256": sha(SCALES_PUBLICATION),
            "definition_id": definition_id,
            "public_definition_sha256": sha_bytes(body["definition"].encode("utf-8")),
            "provider_source_sha256": sha(provider),
            "certificate_sha256": sha(stage.scales.STAGE / "actual-provider-validation.json")}


def static():
    stage.check_only()
    prep = read(STAGE / "preparation.json")
    scales_publication_guard()
    need(prep["source_name"] == stage.TARGET
         and prep["platform_name"] == stage.PLATFORM_NAME
         and prep["source_module"] == stage.TARGET_MODULE
         and prep["source_commit"] == stage.COMMIT
         and prep["original_proof_AST_units_after_data_and_AP14"] == 19
         and prep["original_proof_source_lines_after_data_and_AP14"] == 201
         and len(prep["graph_closure_names"]) == 39
         and len(prep["provider_subtracted_names"]) == 18
         and len(prep["inline_helper_names"]) == 18
         and len(prep["inline_exact_source_units"]) == 18
         and prep["genuine_lazy_equation_CIs"] == stage.EQUATIONS,
         "AP15 source identity/full closure differs")
    need(prep["global_solution_preserves_literal_source_proof"] is True
         and prep["all_helper_proofs_literal_original"] is True
         and prep["existing_port_adaptations"] == [],
         "AP15 literal target/helper provenance differs")
    rows = prep["inline_exact_source_units"] + [prep["target_exact_source_unit"]]
    source_names = [row["name"] for row in rows] + stage.EQUATIONS
    generated_names = [row["name"] for row in rows[:-1]] + ["solution"] + stage.EQUATIONS
    need(prep["source_type_only_names"] == source_names
         and prep["generated_type_only_names"] == generated_names
         and all(row["original_port_command_equal_modulo_line_endings"] is True for row in rows),
         "AP15 full source declaration/equation domain differs")
    need(list(prep["files"]) == stage.FILES
         and [prep["files"][x]["mode"] for x in stage.FILES] == stage.MODES
         and [prep["files"][x]["imports"] for x in stage.FILES] ==
             [stage.IMPORTS, stage.IMPORTS,
              ["Lean", stage.TARGET_MODULE], ["Lean", stage.SOLUTION_MODULE]],
         "AP15 ordered compiler contract differs")

    statement = STAGE / stage.TARGET_OUTPUT
    assembled = (prep["preamble"] + prep["formal_statement"]).encode()
    need(statement.read_bytes() == assembled
         and (STAGE / "wire-theorem-source.lean").read_bytes() == assembled,
         "AP15 preamble/formal statement is not the complete comparator")
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
         "AP15 global solution does not preserve the literal target source proof")
    before = raw[:-len(renamed) - 1]
    need(b"theorem solution" not in before
         and all(sum(line.startswith(("theorem " + name.rsplit(".", 1)[1] + " ").encode())
                     for line in before.splitlines()) == 1
                 for name in prep["inline_helper_names"]),
         "AP15 solution is not the unique final global theorem")

    academic = metadata(prep)
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap15-selected-minor-clearing-bound-publication-manifest",
        "theorem_name": stage.PLATFORM_NAME,
        "preamble": prep["preamble"], "formal_statement": prep["formal_statement"],
        "statement": root_rel(statement), "statement_sha256": sha(statement),
        "platform_statement_assembly_sha256": sha_bytes(assembled),
        "comparator_namespace_suffix_sha256": sha_bytes(b""),
        "solution": root_rel(solution), "solution_sha256": sha(solution),
        "source_commit": stage.COMMIT, "source_url": prep["metadata"]["source_url"],
        "source_module": stage.TARGET_MODULE,
        "source_ast_unit_sha256": prep["target_source_command_sha256"],
        "inline_exact_source_command_count": 18, "graph_closure_count": 39,
        "provider_subtracted_count": 18, "official_equation_CI_count": 2,
        "existing_port_adaptation_count": 0,
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
         "AP15 payload changes exact statement or solution bytes")
    return prep, manifest, academic, payloads, assembled


def lookup_guard():
    need(LOOKUP.is_file(), "AP15 authoritative exact-name lookup is pending")
    doc = read(LOOKUP)
    rows = [row for row in doc.get("records", [])
            if row.get("theorem_name") == stage.PLATFORM_NAME]
    need(doc.get("artifact_kind") == "ap15-selected-minor-clearing-bound-read-only-exact-name-lookup"
         and doc.get("read_only") is True and doc.get("environment") == publisher.ENV
         and doc.get("request_methods") == ["GET"]
         and doc.get("credentials_or_tokens_recorded") is False
         and len(rows) == 1 and rows[0].get("http_status") == 200
         and rows[0].get("matches") == [] and rows[0].get("pages"),
         "AP15 exact-name lookup does not certify zero matches")
    for page in rows[0]["pages"]:
        raw = page.get("raw_body_utf8")
        need(page.get("http_status") == 200 and isinstance(raw, str)
             and page.get("raw_body_sha256") == sha_bytes(raw.encode("utf-8"))
             and json.loads(raw) == page.get("parsed_body")
             and "theorem_name=" in page.get("route", "")
             and "&env=" + publisher.ENV in page.get("route", ""),
             "AP15 saved exact-name GET page differs")


def replay(cert, prep):
    need(consumer.validate() == cert, "AP15 certificate differs from strict replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap15-selected-minor-clearing-bound-node-validation"
         and cert["validated"] is True and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False
         and cert["source_name"] == stage.TARGET
         and cert["platform_name"] == stage.PLATFORM_NAME
         and cert["source_module"] == stage.TARGET_MODULE
         and cert["source_byte_range"] == [16341, 17643]
         and cert["solution_module"] == stage.SOLUTION_MODULE,
         "AP15 certificate identity/state differs")
    need(cert["preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["target_wire_sha256"] == sha(STAGE / stage.TARGET_OUTPUT)
         and cert["solution_source_sha256"] == sha(STAGE / stage.SOLUTION_OUTPUT)
         and cert["existing_port_adaptations"] == []
         and cert["all_helpers_literal_original"] is True
         and cert["source_and_generated_types_equal"] is True
         and cert["source_and_generated_theorem_values_null"] is True
         and cert["source_and_generated_actual_proof_references_paired"] is True
         and cert["source_and_generated_actual_proof_references_bitwise_equal"] is False
         and cert["actual_external_instance_reference_differences"] ==
             EXPECTED_EXTERNAL_INSTANCE_DIFFERENCES
         and cert["Std3_only"] is True,
         "AP15 exact type/proof/adaptation gates differ")
    need(set(cert["preflights"]) == set(stage.FILES)
         and 0 < cert["max_file_seconds"] <= 300
         and set(cert["actual_provider_bindings"]) ==
             {"scales_costs", "closed_AP14_child", "AP10_interpolation",
              "AP10_arithmetic", "AP10_determinant"}
         and len(cert["official_equation_pairs"]) == 2
         and [row["equation"] for row in cert["official_equation_pairs"]] == stage.EQUATIONS
         and all(row["actual_primary_definition_values_equal"] is True
                 and row["equation_types_and_Std3_equal"] is True
                 for row in cert["official_equation_pairs"]),
         "AP15 preflight/provider domain differs")
    for rows in cert["axioms"].values():
        for axioms in rows.values(): need(set(axioms) <= STD3, "AP15 nonstandard axiom")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP15 implementation changed: " + path)
    for filename, expected in cert["json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP15 kernel/proof JSON changed: " + filename)
    need(sha(TASK / cert["solution_olean"]) == cert["solution_olean_sha256"],
         "AP15 solution OLean changed")


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
                 "AP15 dependency OLean changed during compilation")
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
        "artifact_kind": "ap15-selected-minor-clearing-bound-pending-publication",
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
    need(CERT.is_file(), "AP15 strict actual certificate is pending")
    cert = read(CERT); replay(cert, prep)
    scales_publication = scales_publication_guard()
    pins = {"schema_version": 1,
        "artifact_kind": "ap15-selected-minor-clearing-bound-publication-preparation",
        "theorem_name": stage.PLATFORM_NAME, "environment": publisher.ENV,
        "manifest_sha256": sha_bytes(encode(manifest)), "validation_sha256": sha(CERT),
        "exact_name_lookup_sha256": sha(LOOKUP),
        "exact_name_lookup_runner_sha256": sha(LOOKUP_RUNNER),
        "scales_costs_publication": scales_publication,
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
        "official_equation_pairs_sha256": sha_bytes(encode(cert["official_equation_pairs"])),
        "actual_external_instance_reference_differences":
            cert["actual_external_instance_reference_differences"],
        "actual_external_instance_reference_differences_sha256":
            sha_bytes(encode(cert["actual_external_instance_reference_differences"])),
        "existing_port_adaptations_sha256": sha_bytes(encode([])),
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
        "official_equation_pairs": cert["official_equation_pairs"],
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
         "AP15 frozen manifest differs")
    direct = {CERT: frozen["validation_sha256"], LOOKUP: frozen["exact_name_lookup_sha256"],
              LOOKUP_RUNNER: frozen["exact_name_lookup_runner_sha256"],
              SCALES_PUBLICATION: frozen["scales_costs_publication"]["publication_sha256"],
              STAGE / "preparation.json": frozen["stage_preparation_sha256"],
              SELF: frozen["offline_wrapper_sha256"], ONLINE: frozen["online_wrapper_sha256"],
              Path(publisher.__file__): frozen["publisher_sha256"],
              ROOT / "scripts/p2m_api.py": frozen["api_client_sha256"],
              Path(stage.__file__): frozen["stage_producer_sha256"],
              Path(consumer.__file__): frozen["strict_consumer_sha256"]}
    for path, expected in direct.items():
        need(sha(path) == expected, "AP15 frozen implementation/evidence changed: " + str(path))
    for path, expected in frozen["stage_input_hashes"].items():
        need(sha(TASK / path) == expected, "AP15 frozen stage input changed: " + path)
    for filename, expected in frozen["compiler_manifest_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP15 frozen compiler manifest changed: " + filename)
    for value, expected in frozen["preflight_artifact_sha256"].items():
        need(sha(consumer.context.file(value)) == expected, "AP15 frozen preflight changed: " + value)
    for key, expected in frozen["dependency_olean_sha256"].items():
        need(sha(Path(key.split("|", 1)[1])) == expected, "AP15 frozen dependency changed: " + key)
    for filename, expected in frozen["output_json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP15 frozen kernel/proof JSON changed: " + filename)
    need(sha(TASK / frozen["solution_olean"]) == frozen["solution_olean_sha256"],
         "AP15 frozen solution OLean changed")
    need(scales_publication_guard() == frozen["scales_costs_publication"],
         "AP15 Published scales/costs binding changed")
    need(api_review_pins() == frozen["official_api_review"], "AP15 reviewed API docs changed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-pending", action="store_true")
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(pending() if args.prepare_pending else prepare() if args.prepare_only else check(),
                     ensure_ascii=False, indent=2))
