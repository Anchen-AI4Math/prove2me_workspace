"""Freeze the source017f admissible-parent v3 publication bundle offline."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_admissible_parent_a1f_existing_v3 as consumer
import certify_admissible_parent_a1f_extra_ci as extra
import publish_standalone_platform_node as publisher
import stage_admissible_parent_a1f as stage
import validate_namespace_context_providers as context


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v3"
CERT = consumer.CERT
EXTRA_CERT = extra.CERT
SELF = Path(__file__).resolve()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(value):
    return publisher.encode(value)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("frozen a1f publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


CERT_FIELDS = {
    "schema_version", "artifact_kind", "stage", "source_name", "theorem_name",
    "source_commit", "stage_manifest_sha256", "preparation_sha256",
    "consumer_provenance",
    "implementation_hashes", "definition_dependencies", "proved_child_dependencies",
    "preflights", "compiled_Thm_exact_assembly", "type_equalities", "source_axioms",
    "solution_axioms", "proof_references", "project_proof_references",
    "private_ci_certificate", "private_ci_certificate_sha256",
    "private_ci_finite_reference_extension",
    "output_json_sha256", "max_file_seconds", "validated",
    "Lean_started_by_consumer", "API_used", "submission_ready", "proposal_status",
}
EXTRA_CERT_FIELDS = {
    "schema_version", "artifact_kind", "validated", "stage", "source_stage",
    "theorem_name", "source_commit", "preparation_sha256", "source_manifest_sha256",
    "generated_manifest_sha256", "source_probe_sha256", "generated_probe_sha256",
    "frozen_solution_sha256", "frozen_proof_references_sha256", "source_json_sha256",
    "generated_json_sha256", "prior_dimension_v", "private_ci_pairs",
    "certified_generated_private_names", "finite_project_reference_extension",
    "all_extra_ci_project_references_covered", "no_new_axioms_or_proof_assumptions",
    "Std3_only", "max_file_seconds", "source_preflight_replay",
    "generated_preflight_replay", "implementation_hashes", "Lean_started_by_consumer",
    "API_used", "submission_ready",
}
ACADEMIC_FIELDS = {
    "tags", "source_commit", "source_url", "theorem_title",
    "natural_language_statement", "mathematical_role", "explanation",
    "formalization_note", "source_lines",
}


def static_artifacts():
    stage.check_outputs(stage.stage_files())
    manifest = read(STAGE / "manifest.json")
    academic = read(STAGE / "academic-metadata.json")
    need(set(academic) == ACADEMIC_FIELDS, "academic paper metadata shape differs")
    need(academic["source_commit"] == stage.COMMIT, "academic source commit differs")
    need(academic["source_url"].endswith("#L105-L220"), "academic source line URL differs")
    need(academic["source_lines"] == [105, 220], "academic source line interval differs")
    need("hbad" in academic["natural_language_statement"], "academic statement omits hbad")
    need("does not assert" in academic["mathematical_role"],
         "academic role no longer records the conditional result")

    statement = ROOT / manifest["statement"]
    assembled = (manifest["preamble"] + manifest["formal_statement"]).encode("utf-8")
    need(statement.read_bytes() == assembled, "strict Thm differs from preamble + formal bytes")
    need(sha(statement) == manifest["statement_sha256"], "strict Thm manifest hash differs")

    metadata = {
        "theorem_name": manifest["theorem_name"],
        "theorem_title": academic["theorem_title"],
        "natural_language_statement": academic["natural_language_statement"],
        "tags": academic["tags"],
        "explanation": academic["explanation"],
        "source_witness": {
            "commit": academic["source_commit"],
            "source_url": academic["source_url"],
            "source_module": manifest["source_module"],
            "source_lines": academic["source_lines"],
            "mathematical_role": academic["mathematical_role"],
            "formalization_note": academic["formalization_note"],
            "source_sha256": manifest["source_sha256"],
        },
    }
    payloads = publisher.payloads(DEST, manifest, metadata)
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    need((problem["preamble"] + problem["formal_statement"]).encode("utf-8") == assembled,
         "publish payload changes strict Thm")
    verification = json.loads(payloads["verification-payload.json"])
    solution = ROOT / manifest["solution"]
    need(verification["file"]["utf8"].encode("utf-8") == solution.read_bytes(),
         "verification payload changes solution bytes")
    need(verification["file"]["sha256"] == sha(solution),
         "verification payload changes solution hash")
    return manifest, metadata, payloads, assembled


def replay_extra_certificate(cert, manifest):
    need(set(cert) == EXTRA_CERT_FIELDS, "actual a1f extra-CI report schema differs")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap6-a1-paired-private-ci-finite-closure-certificate"
         and cert["validated"] is True and cert["Lean_started_by_consumer"] is False
         and cert["API_used"] is False and cert["submission_ready"] is False
         and cert["Std3_only"] is True
         and cert["all_extra_ci_project_references_covered"] is True
         and cert["no_new_axioms_or_proof_assumptions"] is True,
         "a1f extra-CI certificate state differs")
    need(cert["theorem_name"] == stage.NAME and cert["source_commit"] == stage.COMMIT,
         "a1f extra-CI identity differs")
    need(cert["frozen_solution_sha256"] == sha(ROOT / manifest["solution"])
         and cert["frozen_proof_references_sha256"] == sha(STAGE / "proof-references.json"),
         "a1f extra-CI frozen proof inputs differ")
    need(cert["certified_generated_private_names"] == list(extra.PRIVATE_GENERATED)
         and cert["finite_project_reference_extension"]
             == sorted(set(extra.PRIVATE_GENERATED) | {extra.PRIOR_NAME})
         and len(cert["private_ci_pairs"]) == 4,
         "a1f finite private-CI closure differs")
    need(extra.validate(write=False) == cert,
         "a1f extra-CI certificate differs from full existing-evidence replay")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "a1f extra-CI implementation changed: " + path)


def replay_certificate(cert, manifest, extra_cert):
    need(set(cert) == CERT_FIELDS, "actual a1f consumer report schema differs")
    need(cert["schema_version"] == 1, "a1f report schema version differs")
    need(cert["artifact_kind"] == "ap6-a1-admissible-parent-strict-existing-v3-certificate",
         "a1f report artifact kind differs")
    need(cert["stage"] == rel(STAGE), "a1f report stage differs")
    need(cert["validated"] is True and cert["Lean_started_by_consumer"] is False
         and cert["API_used"] is False and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft", "a1f report state differs")
    need(cert["source_name"] == stage.SOURCE_NAME and cert["theorem_name"] == stage.NAME
         and cert["source_commit"] == stage.COMMIT, "a1f report identity differs")
    need(cert["stage_manifest_sha256"] == sha(STAGE / "manifest.json")
         and cert["preparation_sha256"] == sha(STAGE / "preparation.json"),
         "a1f report stage pins stale")
    preparation = read(STAGE / "preparation.json")
    base_v2_consumer = Path(consumer.ORIGINAL_CONSUMER)
    original_consumer = Path(stage.CONSUMER)
    provenance = cert["consumer_provenance"]
    need(set(provenance) == {"active_consumer_path", "active_consumer_sha256",
                             "original_staged_consumer_path",
                             "original_staged_consumer_sha256", "change"},
         "a1f consumer provenance shape differs")
    need(provenance["active_consumer_path"] == rel(Path(consumer.__file__))
         and provenance["active_consumer_sha256"] == sha(Path(consumer.__file__))
         and provenance["original_staged_consumer_path"] == rel(base_v2_consumer)
         and provenance["original_staged_consumer_sha256"] == sha(base_v2_consumer),
         "a1f active/base-v2 consumer provenance differs")
    need(preparation["strict_consumer"] == rel(original_consumer)
         and preparation["strict_consumer_sha256"] == sha(original_consumer),
         "a1f frozen original consumer pin differs")
    need(cert["definition_dependencies"] == manifest["definition_dependencies"],
         "a1f definition dependencies differ")
    expected_children = [{k: v for k, v in row.items() if k != "certificate"}
                         for row in manifest["proved_child_dependencies"]]
    need(cert["proved_child_dependencies"] == expected_children,
         "a1f proved-child dependencies differ")
    need(cert["private_ci_certificate"] == rel(EXTRA_CERT)
         and cert["private_ci_certificate_sha256"] == sha(EXTRA_CERT)
         and cert["private_ci_finite_reference_extension"]
             == extra_cert["finite_project_reference_extension"],
         "a1f parent/extra-CI certificate binding differs")

    strict = cert["compiled_Thm_exact_assembly"]
    need(set(strict) == {"preamble_sha256", "formal_statement_sha256",
                         "compiled_file_sha256", "byte_equal"},
         "a1f strict Thm report shape differs")
    need(strict["byte_equal"] is True
         and strict["preamble_sha256"] == sha_bytes(manifest["preamble"].encode("utf-8"))
         and strict["formal_statement_sha256"] == sha_bytes(
             manifest["formal_statement"].encode("utf-8"))
         and strict["compiled_file_sha256"] == manifest["statement_sha256"],
         "a1f strict Thm report differs")

    expected_implementations = {
        rel(Path(stage.__file__)): sha(Path(stage.__file__)),
        rel(Path(consumer.__file__)): sha(Path(consumer.__file__)),
        rel(Path(context.__file__)): sha(Path(context.__file__)),
    }
    need(expected_implementations.items() <= cert["implementation_hashes"].items(),
         "a1f primary implementation pins differ")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "a1f implementation changed: " + path)
    for path, expected in cert["output_json_sha256"].items():
        need(sha(TASK / path) == expected, "a1f output JSON changed: " + path)

    need(set(cert["preflights"]) == set(preparation["order"]),
         "a1f actual preflight domain differs")
    for name, row in cert["preflights"].items():
        data = row["data"]
        source = context.file(data["source"])
        compiler_manifest = context.file(data["manifest"])
        current = context.record(source, compiler_manifest, "modecheck",
                                 data["actual_module_identity"], STAGE)
        need(current == row, "actual context.record gate changed: " + name)
    for dependency in [*cert["definition_dependencies"], *cert["proved_child_dependencies"]]:
        need(sha(TASK / dependency["olean"]) == dependency["olean_sha256"],
             "actual first-search OLean changed: " + dependency["module"])


def artifacts():
    manifest, metadata, payloads, assembled = static_artifacts()
    need(EXTRA_CERT.is_file(), "strict a1f extra-CI certificate is pending")
    need(CERT.is_file(), "strict a1f v3 consumer certificate is pending")
    extra_cert, cert = read(EXTRA_CERT), read(CERT)
    replay_extra_certificate(extra_cert, manifest)
    replay_certificate(cert, manifest, extra_cert)
    return manifest, metadata, payloads, assembled, cert, extra_cert


def pins(manifest, metadata, payloads):
    return {
        "theorem_name": stage.NAME,
        "environment": publisher.ENV,
        "proposal_status": "Draft",
        "manifest_sha256": sha_bytes(encode(manifest)),
        "validation_sha256": sha(CERT),
        "extra_ci_validation_sha256": sha(EXTRA_CERT),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "publisher_sha256": sha(Path(publisher.__file__)),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "offline_wrapper_sha256": sha(SELF),
        "original_consumer_sha256": sha(Path(stage.CONSUMER)),
        "base_v2_consumer_sha256": sha(Path(consumer.ORIGINAL_CONSUMER)),
        "active_v3_consumer_sha256": sha(Path(consumer.__file__)),
        "extra_ci_consumer_sha256": sha(Path(extra.__file__)),
        "local_node_validated": True,
        "submission_ready": False,
        "full_tree_ready": False,
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "api_used": False,
    }


def pending():
    manifest, metadata, payloads, assembled = static_artifacts()
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    return {"prepared": True, "validation_pending": not (CERT.is_file() and EXTRA_CERT.is_file()),
            "network_used": False, "proposal_status": "Draft"}


def prepare():
    manifest, metadata, payloads, assembled, _, _ = artifacts()
    frozen_pins = pins(manifest, metadata, payloads)
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "extra-ci-validation.json", EXTRA_CERT.read_bytes())
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    exact(DEST / "preparation.json", encode(frozen_pins))
    return {"prepared": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": frozen_pins["payload_sha256"]}


def check():
    manifest, metadata, payloads, assembled, _, _ = artifacts()
    frozen_pins = pins(manifest, metadata, payloads)
    need((DEST / "manifest.json").read_bytes() == encode(manifest)
         and (DEST / "validation.json").read_bytes() == CERT.read_bytes()
         and (DEST / "extra-ci-validation.json").read_bytes() == EXTRA_CERT.read_bytes()
         and (DEST / "metadata.json").read_bytes() == encode(metadata)
         and (DEST / "wire-theorem-source.lean").read_bytes() == assembled
         and (DEST / "preparation.json").read_bytes() == encode(frozen_pins),
         "frozen a1f publication evidence differs")
    for name, raw in payloads.items():
        need((DEST / name).read_bytes() == raw, "frozen a1f payload differs: " + name)
    return {"checked": True, "network_used": False, "proposal_status": "Draft",
            "payload_sha256": frozen_pins["payload_sha256"]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-pending", action="store_true")
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    result = pending() if args.prepare_pending else prepare() if args.prepare_only else check()
    print(json.dumps(result, ensure_ascii=False, indent=2))
