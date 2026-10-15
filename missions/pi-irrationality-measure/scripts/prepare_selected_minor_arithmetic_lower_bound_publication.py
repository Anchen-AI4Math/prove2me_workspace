"""Prepare the AP16 selected-minor arithmetic lower-bound payload offline."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_selected_minor_arithmetic_lower_bound_node_v2 as consumer
import publish_standalone_platform_node as publisher
import stage_selected_minor_arithmetic_lower_bound_node as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v4"
CERT = consumer.CERT_STAGE / stage.CERTIFICATE
ACTUAL_CI_AUDIT = consumer.AUDIT
ACTUAL_CI_AUDIT_RUNNER = TASK / "scripts/audit_selected_minor_arithmetic_lower_bound_actual_refs.py"
ORIGINAL_CONSUMER = TASK / "scripts/certify_selected_minor_arithmetic_lower_bound_node.py"
ORIGINAL_CONSUMER_PREIMAGE = consumer.PREIMAGE
LOOKUP = STAGE / "exact-name-lookup.json"
LOOKUP_RUNNER = TASK / "scripts/check_selected_minor_arithmetic_lower_bound_platform_name.py"
CANDIDATE_SPEC = STAGE / "candidate-spec.json"
ROUTE_PREPARATION = STAGE / "route-preparation.json"
CANDIDATE = STAGE / "candidate"
CLEARING_PUBLICATION = stage.clearing.STAGE / "publication-v4/publication.json"
CLEARING_CERT = stage.clearing.STAGE / stage.clearing.CERTIFICATE
MIRROR_CERT = stage.mirror_validation.STAGE / stage.mirror_validation.CERTIFICATE
MIRROR_PREPARATION = stage.mirror.STAGE / "preparation.json"
MIRROR_ACCEPTED = stage.mirror.ACCEPTED
MIRROR_SOURCE = stage.mirror.EMITTER_STAGE / stage.mirror.OUTPUT
MIRROR_RUNNER = stage.mirror.RUNNER
MIRROR_LEGACY_RUNNER = stage.mirror.LEGACY_RUNNER
MIRROR_PRODUCER = Path(stage.mirror.__file__)
MIRROR_DERIVATION_PRODUCER = Path(stage.mirror_validation.__file__)
MIRROR_CONSUMER = Path(consumer.mirror_cert.__file__)
MIRROR_LEDGER = stage.mirror_validation.LEDGER
MIRROR_FROZEN_V4_CONSUMER = stage.mirror_validation.FROZEN_V4_CONSUMER
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_selected_minor_arithmetic_lower_bound_node.py"
FAST_ONLINE = TASK / "scripts/publish_selected_minor_arithmetic_lower_bound_node_fast.py"
FAST_DESCRIPTOR_HELPER = TASK / "scripts/prepare_selected_minor_arithmetic_lower_bound_fast_descriptor.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
API_REVIEW_MANIFEST = API_REVIEW / "manifest.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}
DEFINITION_PUBLICATIONS = {
    TASK / "verification/ap7/publication/Def_OAI_NumberTheory_PiExponent_Approximation_Arithmetic/publication.json":
        "OAI_NumberTheory_PiExponent_Approximation_Arithmetic",
    TASK / "verification/ap9/simplex/publication/publication.json":
        "OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains",
    TASK / "verification/ap9/domains/publication/publication.json":
        "OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains",
    TASK / "verification/ap10/interpolation/publication/publication.json":
        "OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData",
    TASK / "verification/ap10/arithmetic/publication/publication.json":
        "OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData",
    TASK / "verification/ap10/determinant/publication-helper-v2/publication.json":
        "OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData",
    TASK / "verification/ap15/scales-costs/publication-v2/publication.json":
        "OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_ScalesCosts",
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
        raise ValueError("Frozen AP16 publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def lookup_guard():
    need(LOOKUP.is_file(), "AP16 authoritative exact-name lookup is pending")
    doc = read(LOOKUP)
    rows = [row for row in doc.get("records", [])
            if row.get("theorem_name") == stage.PLATFORM_NAME]
    need(doc.get("artifact_kind") ==
             "ap16-selected-minor-arithmetic-lower-bound-read-only-exact-name-lookup"
         and doc.get("read_only") is True and doc.get("environment") == publisher.ENV
         and doc.get("request_methods") == ["GET"]
         and doc.get("credentials_or_tokens_recorded") is False
         and len(rows) == 1 and rows[0].get("http_status") == 200
         and rows[0].get("matches") == [] and rows[0].get("pages"),
         "AP16 exact-name lookup does not certify zero matches")
    for page in rows[0]["pages"]:
        raw = page.get("raw_body_utf8")
        need(page.get("http_status") == 200 and isinstance(raw, str)
             and page.get("raw_body_sha256") == sha_bytes(raw.encode("utf-8"))
             and json.loads(raw) == page.get("parsed_body")
             and "theorem_name=" in page.get("route", "")
             and "&env=" + publisher.ENV in page.get("route", ""),
             "AP16 saved exact-name GET page differs")


def published_definitions():
    out = {}
    for path, expected_name in DEFINITION_PUBLICATIONS.items():
        doc = read(path)
        definition_id = doc.get("definition_id")
        verdict = doc.get("last_publish_verdict", {})
        readback = doc.get("target_readback", {})
        body = readback.get("body", {})
        intent = doc.get("publish_intent", {})
        intent_payload = intent.get("payload", {})
        need(isinstance(definition_id, str) and bool(definition_id)
             and doc.get("definition_name") == expected_name
             and intent.get("definition_name") == expected_name
             and intent_payload.get("definition_name") == expected_name
             and verdict.get("http_status") == 200
             and verdict.get("body", {}).get("status") == "PUBLISHED"
             and readback.get("http_status") == 200
             and body.get("theorem_id") == definition_id
             and body.get("theorem_name") == expected_name
             and body.get("status") == "Definition"
             and body.get("mathlib_rev") == publisher.ENV,
             "AP16 required Definition is not exact-read-back Published: " + str(path))
        submitted = intent_payload.get("definition")
        need(isinstance(submitted, str) and body.get("definition") == submitted,
             "AP16 Published Definition readback wire differs: " + str(path))
        out[task_rel(path)] = {"sha256": sha(path), "definition_id": definition_id,
                               "definition_name": expected_name,
                               "public_wire_sha256": sha_bytes(submitted.encode("utf-8"))}
    return out


def clearing_publication(require_proved):
    need(CLEARING_PUBLICATION.is_file() and CLEARING_CERT.is_file(),
         "AP15 clearing publication/certificate is pending")
    doc, cert = read(CLEARING_PUBLICATION), read(CLEARING_CERT)
    prep = read(stage.clearing.STAGE / "preparation.json")
    theorem_id = doc.get("theorem_id")
    verdict = doc.get("last_publish_verdict", {})
    readback = doc.get("target_readback", {})
    body = readback.get("body", {})
    need(isinstance(theorem_id, str) and bool(theorem_id)
         and verdict.get("http_status") == 200
         and verdict.get("body", {}).get("status") == "PUBLISHED"
         and verdict.get("body", {}).get("theorem_id") == theorem_id
         and readback.get("http_status") == 200
         and body.get("theorem_id") == theorem_id
         and body.get("theorem_name") == stage.clearing.TARGET
         and body.get("preamble") == prep["preamble"]
         and body.get("formal_statement") == prep["formal_statement"]
         and cert.get("validated") is True and cert.get("Std3_only") is True,
         "AP15 clearing public target/source certificate differs")
    if require_proved:
        need(doc.get("confirmed_proved") is True and body.get("status") == "Proved",
             "AP15 clearing target is not yet exact-read-back Proved")
    return {"publication": task_rel(CLEARING_PUBLICATION),
            "publication_sha256": sha(CLEARING_PUBLICATION),
            "theorem_id": theorem_id, "readback_status": body.get("status"),
            "confirmed_proved": doc.get("confirmed_proved") is True,
            "source_certificate": task_rel(CLEARING_CERT),
            "source_certificate_sha256": sha(CLEARING_CERT)}


def pending_mirror_boundary():
    """Pin the real v4 route without treating its pending certificate as proof."""
    need(MIRROR_PREPARATION.is_file() and MIRROR_LEDGER.is_file()
         and MIRROR_RUNNER.is_file()
         and MIRROR_LEGACY_RUNNER.is_file() and MIRROR_PRODUCER.is_file()
         and MIRROR_DERIVATION_PRODUCER.is_file() and MIRROR_CONSUMER.is_file()
         and MIRROR_FROZEN_V4_CONSUMER.is_file(),
         "AP16 v5 private-mirror derivation route is missing")
    prep = read(MIRROR_PREPARATION)
    need(prep.get("artifact_kind") ==
             "ap16-private-clearing-child-single-pass-probe-v4-preparation"
         and prep.get("proof_source_and_OLean_unchanged") is True
         and prep.get("public_platform_boundary_excludes_owned_data_equation_CIs") is True
         and prep.get("bounded_runner") == task_rel(MIRROR_RUNNER)
         and prep.get("bounded_runner_sha256") == sha(MIRROR_RUNNER)
         and prep.get("legacy_runner_sha256") == sha(MIRROR_LEGACY_RUNNER),
         "AP16 v4 private-mirror compiled route differs")
    ledger = read(MIRROR_LEDGER)
    need(ledger.get("artifact_kind") ==
             "ap16-private-clearing-child-v5-pure-derivation-ledger"
         and ledger.get("exact_automatic_helper_name") ==
             stage.mirror_validation.AUTO_HELPER
         and ledger.get("new_Lean_files") == []
         and ledger.get("Lean_started") is False and ledger.get("API_used") is False,
         "AP16 v5 private-mirror derivation ledger differs")
    return {"stage": task_rel(stage.mirror_validation.STAGE),
            "certificate": task_rel(MIRROR_CERT),
            "certificate_pending": not MIRROR_CERT.is_file(),
            "derived_ledger": task_rel(MIRROR_LEDGER),
            "derived_ledger_sha256": sha(MIRROR_LEDGER),
            "preparation": task_rel(MIRROR_PREPARATION),
            "preparation_sha256": sha(MIRROR_PREPARATION),
            "bounded_runner": task_rel(MIRROR_RUNNER),
            "bounded_runner_sha256": sha(MIRROR_RUNNER),
            "legacy_runner_sha256": sha(MIRROR_LEGACY_RUNNER),
            "v4_producer_sha256": sha(MIRROR_PRODUCER),
            "v5_derivation_producer_sha256": sha(MIRROR_DERIVATION_PRODUCER),
            "frozen_v4_consumer_sha256": sha(MIRROR_FROZEN_V4_CONSUMER),
            "consumer_sha256": sha(MIRROR_CONSUMER)}


def mirror_boundary_evidence(lower_cert):
    """Read the already replayed v4 certificate and freeze every evidence input."""
    need(MIRROR_CERT.is_file(), "AP16 v4 private-mirror certificate is pending")
    cert = read(MIRROR_CERT)
    need(cert.get("schema_version") == 1
         and cert.get("artifact_kind") ==
             "ap16-private-clearing-child-mirror-validation-v5"
         and cert.get("validated") is True and cert.get("Std3_only") is True
         and cert.get("submission_ready") is False
         and cert.get("proposal_status") == "Draft"
         and cert.get("Lean_started_by_consumer") is False
         and cert.get("API_used") is False
         and cert.get("public_platform_boundary_names") == [stage.clearing.TARGET]
         and cert.get("platform_boundary_certification_pending") is False
         and cert.get("accepted_parent_Proved") is True
         and cert.get("public_platform_boundary_remains_original_target_only") is True
         and cert.get("derived_ledger") == task_rel(MIRROR_LEDGER)
         and cert.get("derived_ledger_sha256") == sha(MIRROR_LEDGER)
         and cert.get("frozen_v4_consumer_sha256") == sha(MIRROR_FROZEN_V4_CONSUMER)
         and cert.get("actual_closed_automatic_data_helper_pair", {}).get("name") ==
             stage.mirror_validation.AUTO_HELPER
         and cert["actual_closed_automatic_data_helper_pair"].get(
             "full_type_axioms_and_all_actual_refs_equal") is True
         and cert["actual_closed_automatic_data_helper_pair"].get(
             "closed_source_and_generated_proof_values") is True
         and cert["actual_closed_automatic_data_helper_pair"].get(
             "only_actual_auxiliary_project_ref_exception") is True
         and cert.get("provider_source_sha256") == sha(MIRROR_SOURCE)
         and cert.get("provider_olean_sha256") == stage.mirror.EXPECTED_OLEAN
         and cert.get("preparation_sha256") == sha(MIRROR_PREPARATION)
         and cert.get("accepted_evidence_sha256") == sha(MIRROR_ACCEPTED)
         and cert.get("bounded_runner_sha256") == sha(MIRROR_RUNNER)
         and lower_cert.get("actual_closed_AP15_mirror_certificate") == task_rel(MIRROR_CERT)
         and lower_cert.get("actual_closed_AP15_mirror_certificate_sha256") == sha(MIRROR_CERT),
         "AP16 lower/v4 private-mirror certificate binding differs")
    olean = TASK / cert["provider_olean"]
    need(sha(olean) == cert["provider_olean_sha256"],
         "AP16 v4 private-mirror OLean differs")
    prep = read(MIRROR_PREPARATION)
    implementation = cert["implementation_hashes"]
    generated = cert["generated_json_sha256"]
    for path, expected in implementation.items():
        need(sha(TASK / path) == expected,
             "AP16 v4 implementation changed: " + path)
    for filename, expected in generated.items():
        need(sha(stage.mirror.STAGE / filename) == expected,
             "AP16 v4 written JSON changed: " + filename)
    for path, expected in prep["input_hashes"].items():
        need(sha(TASK / path) == expected,
             "AP16 v4 preparation input changed: " + path)
    return {"certificate": task_rel(MIRROR_CERT),
            "certificate_sha256": sha(MIRROR_CERT),
            "preparation": task_rel(MIRROR_PREPARATION),
            "preparation_sha256": sha(MIRROR_PREPARATION),
            "preparation_input_hashes": prep["input_hashes"],
            "derived_ledger": task_rel(MIRROR_LEDGER),
            "derived_ledger_sha256": sha(MIRROR_LEDGER),
            "derived_ledger_input_hashes": read(MIRROR_LEDGER)["input_hashes"],
            "frozen_v4_consumer": task_rel(MIRROR_FROZEN_V4_CONSUMER),
            "frozen_v4_consumer_sha256": sha(MIRROR_FROZEN_V4_CONSUMER),
            "actual_closed_automatic_data_helper_pair":
                cert["actual_closed_automatic_data_helper_pair"],
            "accepted_evidence": task_rel(MIRROR_ACCEPTED),
            "accepted_evidence_sha256": sha(MIRROR_ACCEPTED),
            "provider_source": task_rel(MIRROR_SOURCE),
            "provider_source_sha256": cert["provider_source_sha256"],
            "provider_olean": cert["provider_olean"],
            "provider_olean_sha256": cert["provider_olean_sha256"],
            "bounded_runner": task_rel(MIRROR_RUNNER),
            "bounded_runner_sha256": sha(MIRROR_RUNNER),
            "legacy_runner": task_rel(MIRROR_LEGACY_RUNNER),
            "legacy_runner_sha256": sha(MIRROR_LEGACY_RUNNER),
            "implementation_hashes": implementation,
            "generated_json_sha256": generated,
            "preflight_artifact_sha256": evidence_hashes(cert),
            "dependency_olean_sha256": dependency_oleans(cert)}


def academic(prep):
    source_url = ("https://github.com/openai/math/blob/" + stage.COMMIT
                  + "/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean#L360-L393")
    statement = (
        "Let $m,K\\in\\mathbb N$ and $w_0,v_0,\\theta,F,H,w_{\\min}\\in\\mathbb R$. "
        "Let $p:\\operatorname{Fin}(m)\\to\\mathbb Z$ and "
        "$q:\\operatorname{Fin}(m)\\to\\mathbb N$ with $q_i\\ge2$. Assume "
        "$K,w_0,v_0,\\theta,H,w_{\\min}>0$, $F\\ge0$, and "
        "$w_{\\min}\\le\\lceil\\log q_i\\rceil_+$ for every $i$. For a selection "
        "from the original row domain to the original column domain whose selected "
        "minor $M_{\\mathrm{sel}}$ has nonzero determinant, put "
        "$\\overline W=\\operatorname{meanRowWeight}(K,v_0,\\theta,q,H)$ and let "
        "$L$ be the source least-common-multiple constant. Then\n\n"
        "$$-(1-\\overline W)-\\left(\\frac{LFm}{v_0}"
        "+L\\sum_i\\frac1{\\lceil\\log q_i\\rceil_+}"
        "+\\frac{\\theta}{w_{\\min}}\\right)"
        "\\le\\frac{\\log\\lVert\\det M_{\\mathrm{sel}}\\rVert}{|\\mathcal R|H}.$$"
    )
    explanation = (
        "The denominator-clearing estimate supplies the determinant term. The "
        "source bounds for the common denominator, selected-column logarithmic "
        "cost, and row logarithmic cost then normalize it by the positive quantity "
        "$|\\mathcal R|H$. This is the arithmetic half of the later contradiction "
        "argument and preserves the source's exact finite row and column domains."
    )
    return {"theorem_name": stage.PLATFORM_NAME,
            "theorem_title": "An arithmetic lower bound for a selected interpolation minor",
            "natural_language_statement": statement, "explanation": explanation,
            "tags": ["number-theory", "linear-algebra", "openai-pi-exponent-017"],
            "source_witness": {"source_commit": stage.COMMIT, "source_url": source_url,
                "source_module": stage.TARGET_MODULE, "target_ast": prep["target_ast"],
                "target_source_command_sha256": prep.get("target_source_command_sha256",
                                                         prep.get("target_command_sha256")),
                "target_proof_suffix_sha256": prep["target_proof_suffix_sha256"],
                "original_proof_AST_units": 22, "original_source_lines": 247,
                "inline_helper_count": 21,
                "provider_subtracted_names": prep["provider_subtracted_names"],
                "existing_port_adaptations": []}}


def payload_bundle(prep, statement, solution, validated):
    raw_statement, raw_solution = statement.read_bytes(), solution.read_bytes()
    if "preamble" in prep:
        preamble, formal = prep["preamble"], prep["formal_statement"]
    else:
        head, tail = raw_statement.split(b"theorem ", 1)
        preamble, formal = head.decode(), (b"theorem " + tail).decode()
    assembled = (preamble + formal).encode()
    need(raw_statement == assembled and b"sorry" not in raw_solution,
         "AP16 candidate/final wire or global solution differs")
    meta = academic(prep)
    manifest = {"schema_version": 1,
        "artifact_kind": "ap16-selected-minor-arithmetic-lower-bound-publication-manifest",
        "theorem_name": stage.PLATFORM_NAME, "preamble": preamble,
        "formal_statement": formal, "statement": root_rel(statement),
        "statement_sha256": sha(statement),
        "platform_statement_assembly_sha256": sha_bytes(assembled),
        "comparator_namespace_suffix_sha256": sha_bytes(b""),
        "solution": root_rel(solution), "solution_sha256": sha(solution),
        "source_commit": stage.COMMIT, "source_url": meta["source_witness"]["source_url"],
        "source_module": stage.TARGET_MODULE,
        "source_ast_unit_sha256": meta["source_witness"]["target_source_command_sha256"],
        "inline_exact_source_command_count": 21, "original_proof_AST_units": 22,
        "original_source_lines": 247, "existing_port_adaptation_count": 0,
        "proposal_status": "Draft", "validated": validated,
        "local_standalone_validated": validated,
        "submission_ready": False, "full_tree_ready": False}
    payloads = publisher.payloads(DEST, manifest, meta)
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    verify = json.loads(payloads["verification-payload.json"])
    need((problem["preamble"] + problem["formal_statement"]).encode() == assembled
         and problem["theorem_name"] == stage.PLATFORM_NAME
         and verify["theorem_id"] is None
         and verify["target_theorem_name"] == stage.PLATFORM_NAME
         and verify["file"]["utf8"].encode() == raw_solution,
         "AP16 payload changes exact statement or solution bytes")
    return manifest, meta, payloads, assembled


def candidate_static():
    stage.check_candidate()
    spec, route = read(CANDIDATE_SPEC), read(ROUTE_PREPARATION)
    need(spec["source_name"] == stage.TARGET and spec["source_module"] == stage.TARGET_MODULE
         and spec["source_AST_units"] == 22 and spec["source_lines"] == 247
         and spec["AP15_private_mirror_certificate_pending"] is True
         and spec["compiler_manifests_finalized"] is False
         and route["inline_proof_ast_count"] == 22
         and route["inline_source_line_count"] == 247,
         "AP16 candidate/route identity differs")
    lookup_guard(); published_definitions(); clearing_publication(False)
    statement = CANDIDATE / (stage.TARGET_OUTPUT + ".txt")
    solution = CANDIDATE / (stage.SOLUTION_OUTPUT + ".txt")
    manifest, meta, payloads, assembled = payload_bundle(spec, statement, solution, False)
    return spec, manifest, meta, payloads, assembled


def static():
    stage.check_only()
    prep = read(STAGE / "preparation.json")
    need(prep["source_name"] == stage.TARGET and prep["platform_name"] == stage.PLATFORM_NAME
         and prep["source_module"] == stage.TARGET_MODULE
         and prep["source_commit"] == stage.COMMIT
         and prep["original_proof_AST_units"] == 22
         and prep["original_source_lines"] == 247
         and len(prep["inline_helper_names"]) == 21
         and len(prep["inline_exact_source_units"]) == 21
         and prep["global_solution_preserves_literal_source_proof"] is True
         and prep["all_helper_proofs_literal_original"] is True
         and prep["existing_port_adaptations"] == [],
         "AP16 final source identity/provenance differs")
    rows = prep["inline_exact_source_units"] + [prep["target_exact_source_unit"]]
    need(prep["source_type_only_names"] == [r["name"] for r in rows]
         and prep["generated_type_only_names"] == [r["name"] for r in rows[:-1]] + ["solution"]
         and all(r["original_port_command_equal_modulo_line_endings"] is True for r in rows)
         and list(prep["files"]) == stage.FILES
         and [prep["files"][x]["mode"] for x in stage.FILES] == stage.MODES,
         "AP16 final declaration/compiler domain differs")
    statement, solution = STAGE / stage.TARGET_OUTPUT, STAGE / stage.SOLUTION_OUTPUT
    manifest, meta, payloads, assembled = payload_bundle(prep, statement, solution, CERT.is_file())
    need((STAGE / "wire-theorem-source.lean").read_bytes() == assembled,
         "AP16 complete comparator differs")
    return prep, manifest, meta, payloads, assembled


def replay(cert, prep):
    need(consumer.validate() == cert, "AP16 certificate differs from strict replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap16-selected-minor-arithmetic-lower-bound-validation-v2"
         and cert["validated"] is True and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False
         and cert["source_name"] == stage.TARGET
         and cert["platform_name"] == stage.PLATFORM_NAME
         and cert["source_module"] == stage.TARGET_MODULE
         and cert["source_byte_range"] == stage.route.TARGET_SOURCE_RANGE
         and cert["solution_module"] == stage.SOLUTION_MODULE
         and cert["preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["target_wire_sha256"] == sha(STAGE / stage.TARGET_OUTPUT)
         and cert["solution_source_sha256"] == sha(STAGE / stage.SOLUTION_OUTPUT)
         and cert["all_helpers_literal_original"] is True
         and cert["existing_port_adaptations"] == []
         and cert["source_and_generated_types_equal"] is True
         and cert["source_and_generated_theorem_values_null"] is True
         and cert["source_and_generated_actual_proof_references_paired"] is True
         and cert["source_and_generated_actual_proof_references_bitwise_equal"] is False
         and cert["actual_external_instance_reference_differences"] == {
             consumer.DELTA_NAME: consumer.EXACT_EXTERNAL_INSTANCE_DELTA
             | {"fields": ["valueRefs", "allUsedConstants"]}}
         and cert["complete_actual_CI_audit_sha256"] == sha(ACTUAL_CI_AUDIT)
         and cert["unrun_original_consumer_preimage_sha256"] ==
             sha(ORIGINAL_CONSUMER_PREIMAGE) == consumer.PREIMAGE_SHA256
         and sha(ORIGINAL_CONSUMER) == consumer.PREIMAGE_SHA256
         and cert["Std3_only"] is True and set(cert["preflights"]) == set(stage.FILES)
         and 0 < cert["max_file_seconds"] <= 300,
         "AP16 strict actual proof gates differ")
    for rows in cert["axioms"].values():
        for axioms in rows.values(): need(set(axioms) <= STD3, "AP16 nonstandard axiom")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP16 implementation changed: " + path)
    for filename, expected in cert["json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP16 kernel/proof JSON changed: " + filename)
    need(sha(TASK / cert["solution_olean"]) == cert["solution_olean_sha256"],
         "AP16 solution OLean changed")


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
                 "AP16 dependency OLean changed during compilation")
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
    spec, manifest, meta, payloads, assembled = candidate_static()
    for name, raw in payloads.items(): exact(DEST / name, raw)
    exact(DEST / "metadata.json", encode(meta)); exact(DEST / "wire-theorem-source.lean", assembled)
    record = {"schema_version": 1,
        "artifact_kind": "ap16-selected-minor-arithmetic-lower-bound-pending-publication",
        "theorem_name": stage.PLATFORM_NAME,
        "candidate_spec_sha256": sha(CANDIDATE_SPEC),
        "route_preparation_sha256": sha(ROUTE_PREPARATION),
        "exact_name_lookup_sha256": sha(LOOKUP),
        "clearing_publication": clearing_publication(False),
        "private_mirror_route": pending_mirror_boundary(),
        "published_definitions": published_definitions(),
        "publication_manifest_sha256": sha_bytes(encode(manifest)),
        "metadata_sha256": sha_bytes(encode(meta)), "wire_theorem_sha256": sha_bytes(assembled),
        "solution_sha256": manifest["solution_sha256"],
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "strict_validation_pending": not CERT.is_file(),
        "final_stage_pending": not (STAGE / "preparation.json").is_file(),
        "network_used": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft"}
    exact(DEST / "pending-preparation.json", encode(record))
    return {"prepared": True, "validation_pending": record["strict_validation_pending"],
            "final_stage_pending": record["final_stage_pending"], "network_used": False,
            "proposal_status": "Draft", "payload_sha256": record["payload_sha256"]}


def prepare():
    prep, manifest, meta, payloads, assembled = static()
    lookup_guard(); need(CERT.is_file(), "AP16 strict actual certificate is pending")
    cert = read(CERT); replay(cert, prep)
    clearing, definitions = clearing_publication(True), published_definitions()
    mirror = mirror_boundary_evidence(cert)
    pins = {"schema_version": 1,
        "artifact_kind": "ap16-selected-minor-arithmetic-lower-bound-publication-preparation",
        "theorem_name": stage.PLATFORM_NAME, "environment": publisher.ENV,
        "manifest_sha256": sha_bytes(encode(manifest)), "validation_sha256": sha(CERT),
        "exact_name_lookup_sha256": sha(LOOKUP),
        "exact_name_lookup_runner_sha256": sha(LOOKUP_RUNNER),
        "clearing_publication": clearing, "private_mirror_evidence": mirror,
        "published_definitions": definitions,
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "offline_wrapper_sha256": sha(SELF), "online_wrapper_sha256": sha(ONLINE),
        "fast_online_wrapper_sha256": sha(FAST_ONLINE),
        "fast_descriptor_helper_sha256": sha(FAST_DESCRIPTOR_HELPER),
        "publisher_sha256": sha(Path(publisher.__file__)),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "complete_actual_CI_audit": task_rel(ACTUAL_CI_AUDIT),
        "complete_actual_CI_audit_sha256": sha(ACTUAL_CI_AUDIT),
        "actual_CI_audit_runner_sha256": sha(ACTUAL_CI_AUDIT_RUNNER),
        "unrun_original_consumer": task_rel(ORIGINAL_CONSUMER),
        "unrun_original_consumer_sha256": sha(ORIGINAL_CONSUMER),
        "unrun_original_consumer_preimage": task_rel(ORIGINAL_CONSUMER_PREIMAGE),
        "unrun_original_consumer_preimage_sha256": sha(ORIGINAL_CONSUMER_PREIMAGE),
        "actual_external_instance_reference_differences":
            cert["actual_external_instance_reference_differences"],
        "source_and_generated_actual_proof_references_paired": True,
        "source_and_generated_actual_proof_references_bitwise_equal": False,
        "metadata_sha256": sha_bytes(encode(meta)),
        "wire_theorem_sha256": manifest["platform_statement_assembly_sha256"],
        "compiled_comparator_sha256": manifest["statement_sha256"],
        "solution_sha256": manifest["solution_sha256"],
        "target_source_command_sha256": prep["target_source_command_sha256"],
        "target_proof_suffix_sha256": prep["target_proof_suffix_sha256"],
        "runtime_sha256": sha(stage.clearing.RUNTIME),
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
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "official_api_review": api_review_pins(),
        "local_node_validated": True, "submission_ready": False,
        "full_tree_ready": False, "proposal_status": "Draft",
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "durable_post_policy": "saved publish_intent before POST; never repeat a recorded intent",
        "API_used": False}
    exact(DEST / "manifest.json", encode(manifest)); exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "metadata.json", encode(meta)); exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items(): exact(DEST / name, raw)
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": pins["payload_sha256"]}


def hash_gate(current_manifest, frozen):
    need(current_manifest == read(DEST / "manifest.json")
         and sha_bytes(encode(current_manifest)) == frozen["manifest_sha256"],
         "AP16 frozen manifest differs")
    direct = {CERT: frozen["validation_sha256"], LOOKUP: frozen["exact_name_lookup_sha256"],
              LOOKUP_RUNNER: frozen["exact_name_lookup_runner_sha256"],
              CLEARING_PUBLICATION: frozen["clearing_publication"]["publication_sha256"],
              CLEARING_CERT: frozen["clearing_publication"]["source_certificate_sha256"],
              STAGE / "preparation.json": frozen["stage_preparation_sha256"],
              SELF: frozen["offline_wrapper_sha256"], ONLINE: frozen["online_wrapper_sha256"],
              FAST_ONLINE: frozen["fast_online_wrapper_sha256"],
              FAST_DESCRIPTOR_HELPER: frozen["fast_descriptor_helper_sha256"],
              Path(publisher.__file__): frozen["publisher_sha256"],
              ROOT / "scripts/p2m_api.py": frozen["api_client_sha256"],
              Path(stage.__file__): frozen["stage_producer_sha256"],
              Path(consumer.__file__): frozen["strict_consumer_sha256"],
              ACTUAL_CI_AUDIT: frozen["complete_actual_CI_audit_sha256"],
              ACTUAL_CI_AUDIT_RUNNER: frozen["actual_CI_audit_runner_sha256"],
              ORIGINAL_CONSUMER: frozen["unrun_original_consumer_sha256"],
              ORIGINAL_CONSUMER_PREIMAGE:
                  frozen["unrun_original_consumer_preimage_sha256"]}
    for item in frozen["published_definitions"]:
        direct[TASK / item] = frozen["published_definitions"][item]["sha256"]
    mirror = frozen["private_mirror_evidence"]
    direct.update({TASK / mirror["certificate"]: mirror["certificate_sha256"],
                   TASK / mirror["preparation"]: mirror["preparation_sha256"],
                   TASK / mirror["derived_ledger"]: mirror["derived_ledger_sha256"],
                   TASK / mirror["frozen_v4_consumer"]:
                       mirror["frozen_v4_consumer_sha256"],
                   TASK / mirror["accepted_evidence"]: mirror["accepted_evidence_sha256"],
                   TASK / mirror["provider_source"]: mirror["provider_source_sha256"],
                   TASK / mirror["provider_olean"]: mirror["provider_olean_sha256"],
                   TASK / mirror["bounded_runner"]: mirror["bounded_runner_sha256"],
                   TASK / mirror["legacy_runner"]: mirror["legacy_runner_sha256"]})
    for path, expected in mirror["implementation_hashes"].items():
        direct[TASK / path] = expected
    for path, expected in direct.items():
        need(sha(path) == expected, "AP16 frozen implementation/evidence changed: " + str(path))
    for path, expected in frozen["stage_input_hashes"].items():
        need(sha(TASK / path) == expected, "AP16 frozen stage input changed: " + path)
    for filename, expected in frozen["compiler_manifest_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP16 frozen compiler manifest changed: " + filename)
    for value, expected in frozen["preflight_artifact_sha256"].items():
        need(sha(consumer.context.file(value)) == expected, "AP16 frozen preflight changed: " + value)
    for key, expected in frozen["dependency_olean_sha256"].items():
        need(sha(Path(key.split("|", 1)[1])) == expected, "AP16 frozen dependency changed: " + key)
    for filename, expected in frozen["output_json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP16 frozen kernel/proof JSON changed: " + filename)
    for path, expected in mirror["preparation_input_hashes"].items():
        need(sha(TASK / path) == expected,
             "AP16 frozen v4 preparation input changed: " + path)
    for path, expected in mirror["derived_ledger_input_hashes"].items():
        need(sha(TASK / path) == expected,
             "AP16 frozen v5 derivation input changed: " + path)
    for filename, expected in mirror["generated_json_sha256"].items():
        need(sha(stage.mirror.STAGE / filename) == expected,
             "AP16 frozen v4 written JSON changed: " + filename)
    for value, expected in mirror["preflight_artifact_sha256"].items():
        need(sha(consumer.context.file(value)) == expected,
             "AP16 frozen v4 preflight changed: " + value)
    for key, expected in mirror["dependency_olean_sha256"].items():
        need(sha(Path(key.split("|", 1)[1])) == expected,
             "AP16 frozen v4 dependency changed: " + key)
    need(sha(TASK / frozen["solution_olean"]) == frozen["solution_olean_sha256"],
         "AP16 frozen solution OLean changed")
    need(clearing_publication(True) == frozen["clearing_publication"]
         and published_definitions() == frozen["published_definitions"],
         "AP16 frozen public dependency bindings changed")
    need(api_review_pins() == frozen["official_api_review"], "AP16 reviewed API docs changed")


def check():
    result = prepare()
    hash_gate(read(DEST / "manifest.json"), read(DEST / "preparation.json"))
    return {"checked": True, **{k: v for k, v in result.items() if k != "prepared"}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-pending", action="store_true")
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    print(json.dumps(pending() if args.prepare_pending else prepare() if args.prepare_only else check(),
                     ensure_ascii=False, indent=2))
