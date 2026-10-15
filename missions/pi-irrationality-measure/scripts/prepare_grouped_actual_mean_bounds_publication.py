"""Prepare the AP12 actualMean_bounds publication without networking or Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_grouped_actual_mean_bounds_node as consumer
import publish_standalone_platform_node as publisher
import stage_grouped_actual_mean_bounds_node as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v2"
CERT = STAGE / stage.CERTIFICATE
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_grouped_actual_mean_bounds_node.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
API_REVIEW_MANIFEST = API_REVIEW / "manifest.json"
LOOKUP = TASK / "verification/determinant-core-exact-name-lookup-20261011T135109_614374Z.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def sha_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(Path(path).read_bytes())


def read(path: Path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def encode(value) -> bytes:
    return publisher.encode(value)


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def task_rel(path: Path) -> str:
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def root_rel(path: Path) -> str:
    return Path(path).resolve().relative_to(ROOT.resolve()).as_posix()


def exact(path: Path, raw: bytes) -> None:
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen AP12 actual-mean publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def exact_name_lookup_guard() -> None:
    doc = read(LOOKUP)
    rows = [row for row in doc.get("records", [])
            if row.get("theorem_name") == stage.PLATFORM_NAME]
    need(doc.get("read_only") is True and doc.get("environment") == publisher.ENV
         and len(rows) == 1 and rows[0].get("http_status") == 200
         and rows[0].get("matches") == [],
         "Authoritative exact-name lookup does not certify zero AP12 matches")


def academic_metadata(prep: dict) -> dict:
    source = prep["metadata"]
    statement = (
        "Let $\\nu\\in\\mathbb R$, let $d:\\mathrm{FixedData}(\\nu)$ be the original "
        "admissible determinant data, and let $H>0$.  Write $b_d(H)$ for its actual mean "
        "row weight: the total logarithmic coordinate weight of all interpolation rows, "
        "divided by the number of rows and by $H$.  Then\n\n"
        "$$\n0\\le b_d(H)\\le\\theta_d,\n$$\n\n"
        "where $\\theta_d>0$ is the theta parameter of the base data."
    )
    explanation = (
        "Each denominator satisfies $q_i\\ge2$, so its weight "
        "$w_i=\\lceil\\log q_i\\rceil$ is positive.  Membership in the strict weighted "
        "simplex gives, for every interpolation row $\\rho$,\n\n"
        "$$\n\\sum_i \\rho_{i+1}w_i\\le H\\theta_d.\n$$\n\n"
        "Summing this inequality over the finite row type bounds the numerator by "
        "$|\\mathrm{Row}(H)|H\\theta_d$.  The zero multi-index supplies a row, so the row "
        "count is positive; together with $H>0$, the normalizing denominator is positive. "
        "The numerator is a sum of nonnegative terms, which gives the lower bound, and "
        "division gives the upper bound.  This is the mean estimate used by the later "
        "NoFixedData determinant reduction."
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
        "inline_exact_source_command_count": len(prep["inline_exact_source_units"]),
        "inline_exact_source_units_sha256": sha_bytes(encode(prep["inline_exact_source_units"])),
        "graph_closure_count": len(prep["graph_closure_names"]),
        "mathematical_role": (
            "Two-sided normalized row-weight estimate used by the source-faithful "
            "NoFixedData determinant contradiction branch."
        ),
    }
    return {
        "theorem_name": stage.PLATFORM_NAME,
        "theorem_title": "The actual mean row weight lies between zero and theta",
        "natural_language_statement": statement,
        "explanation": explanation,
        "tags": ["number-theory", "weighted-simplex", "linear-algebra", "openai-pi-exponent-017"],
        "source_witness": witness,
    }


def static_artifacts():
    stage.check_only()
    exact_name_lookup_guard()
    prep = read(STAGE / "preparation.json")
    need(prep["source_name"] == stage.TARGET
         and prep["platform_name"] == stage.PLATFORM_NAME
         and prep["source_module"] == stage.TARGET_MODULE
         and prep["source_commit"] == stage.COMMIT
         and prep["metadata"]["source_url"].endswith("DeterminantContradiction.lean#L87-L92"),
         "AP12 identity/provenance differs")
    need(len(prep["graph_closure_names"]) == 36
         and len(prep["inline_helper_names"]) == 10
         and len(prep["inline_exact_source_units"]) == 10
         and prep["global_solution_preserves_literal_source_proof"] is True,
         "AP12 closure/helper/literal-proof contract differs")
    need(list(prep["files"]) == stage.FILES
         and [prep["files"][name]["mode"] for name in stage.FILES] == stage.MODES
         and [prep["files"][name]["emit_olean"] for name in stage.FILES] ==
             [False, True, False, False],
         "AP12 ordered compiler modes differ")
    expected_imports = [stage.IMPORTS, stage.IMPORTS,
                        ["Lean", stage.TARGET_MODULE], ["Lean", stage.SOLUTION_MODULE]]
    need([prep["files"][name]["imports"] for name in stage.FILES] == expected_imports,
         "AP12 ordered imports differ")

    statement = STAGE / stage.TARGET_OUTPUT
    raw = statement.read_bytes()
    preamble = prep["preamble"].encode()
    formal = prep["formal_statement"].encode()
    assembled = preamble + formal
    suffix = raw[len(assembled):] if raw.startswith(assembled) else None
    need(raw == assembled and suffix == b""
         and (STAGE / "wire-theorem-source.lean").read_bytes() == raw,
         "AP12 preamble plus formal statement is not the complete compiled comparator")

    solution = STAGE / stage.SOLUTION_OUTPUT
    command = (STAGE / "original-target-command.lean.txt").read_bytes()
    unit = prep["target_ast"]
    ns = unit["nameRange"]["start"]["offset"] - unit["start"]["offset"]
    ne = unit["nameRange"]["end"]["offset"] - unit["start"]["offset"]
    renamed = command[:ns] + b"solution" + command[ne:]
    solution_raw = solution.read_bytes()
    need(solution_raw.endswith(renamed + b"\n")
         and renamed[renamed.find(b":= by"):] ==
             command[unit["valueStart"]["offset"] - unit["start"]["offset"]:]
         and b"sorry" not in solution_raw,
         "AP12 global solution differs from the literal renamed source theorem")
    before = solution_raw[:-len(renamed) - 1]
    need(b"theorem solution" not in before
         and before.rstrip().endswith(b"open scoped Topology"),
         "AP12 solution is not the unique global top-level final theorem")

    metadata = academic_metadata(prep)
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap12-grouped-actual-mean-bounds-publication-manifest",
        "theorem_name": stage.PLATFORM_NAME,
        "exact_name_lookup_sha256": sha(LOOKUP),
        "preamble": prep["preamble"],
        "formal_statement": prep["formal_statement"],
        "statement": root_rel(statement),
        "statement_sha256": sha(statement),
        "platform_statement_assembly_sha256": sha_bytes(assembled),
        "comparator_namespace_suffix_sha256": sha_bytes(suffix),
        "comparator_namespace_suffix_bytes": len(suffix),
        "solution": root_rel(solution),
        "solution_sha256": sha(solution),
        "source_commit": stage.COMMIT,
        "source_url": prep["metadata"]["source_url"],
        "source_module": stage.TARGET_MODULE,
        "source_ast_unit_sha256": prep["target_source_command_sha256"],
        "inline_exact_source_command_count": 10,
        "graph_closure_count": 36,
        "proposal_status": "Draft",
        "validated": CERT.is_file(),
        "local_standalone_validated": CERT.is_file(),
        "submission_ready": False,
        "full_tree_ready": False,
    }
    payloads = publisher.payloads(DEST, manifest, metadata)
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    verify = json.loads(payloads["verification-payload.json"])
    need(problem["theorem_name"] == stage.PLATFORM_NAME
         and (problem["preamble"] + problem["formal_statement"]).encode() == raw
         and problem["source"] == prep["metadata"]["source_url"],
         "AP12 publication payload changes comparator bytes/provenance")
    need(verify["target_theorem_name"] == stage.PLATFORM_NAME
         and verify["theorem_id"] is None
         and verify["file"]["sha256"] == sha(solution)
         and verify["file"]["utf8"].encode() == solution_raw,
         "AP12 verification payload changes the literal solution")
    return prep, manifest, metadata, payloads, assembled


def replay_certificate(cert: dict, prep: dict) -> None:
    need(consumer.validate() == cert, "AP12 certificate differs from strict saved-evidence replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap12-grouped-actual-mean-bounds-node-validation"
         and cert["validated"] is True and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False,
         "AP12 certificate state differs")
    need(cert["source_name"] == stage.TARGET
         and cert["platform_name"] == stage.PLATFORM_NAME
         and cert["source_module"] == stage.TARGET_MODULE
         and cert["solution_module"] == stage.SOLUTION_MODULE
         and cert["source_commit"] == stage.COMMIT
         and cert["source_byte_range"] == [4002, 4395],
         "AP12 certificate identity/provenance differs")
    need(cert["preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["target_wire_sha256"] == sha(STAGE / stage.TARGET_OUTPUT)
         and cert["solution_source_sha256"] == sha(STAGE / stage.SOLUTION_OUTPUT),
         "AP12 stage/wire/solution pins differ")
    need(cert["source_and_generated_types_equal"] is True
         and cert["source_and_generated_theorem_values_null"] is True
         and cert["source_and_generated_actual_proof_references_paired"] is True
         and cert["Std3_only"] is True
         and cert["graph_closure_names"] == sorted(prep["graph_closure_names"])
         and cert["inline_helper_names"] == prep["inline_helper_names"],
         "AP12 type/proof/reference/Std3 gates differ")
    need(set(cert["preflights"]) == set(stage.FILES)
         and 0 < cert["max_file_seconds"] <= 300,
         "AP12 preflight domain or budget differs")
    for rows in cert["axioms"].values():
        for axioms in rows.values():
            need(set(axioms) <= STD3, "AP12 proof CI uses nonstandard axioms")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP12 implementation changed: " + path)
    for filename, expected in cert["json_sha256"].items():
        need(sha(STAGE / filename) == expected, "AP12 kernel/proof JSON changed: " + filename)
    for filename, theorem_name in ((stage.SOURCE_TYPE_JSON, stage.TARGET),
                                   (stage.GENERATED_TYPE_JSON, "solution")):
        row = next(x for x in read(STAGE / filename) if x["name"] == theorem_name)
        need(row["value"] is None, "AP12 TypeOnly theorem value is not null")
    olean = TASK / cert["solution_olean"]
    need(olean.is_file() and sha(olean) == cert["solution_olean_sha256"],
         "AP12 compiled solution OLean changed")
    need(set(cert["actual_provider_bindings"]) == set(stage.base.ap10.CONFIGS),
         "AP12 certified provider binding domain differs")


def artifacts():
    prep, manifest, metadata, payloads, assembled = static_artifacts()
    need(CERT.is_file(), "Actual AP12 validation certificate is pending")
    cert = read(CERT)
    replay_certificate(cert, prep)
    return prep, manifest, metadata, payloads, assembled, cert


def evidence_hashes(cert: dict) -> dict:
    found = {}
    for row in cert["preflights"].values():
        for key in ("source", "manifest", "log"):
            value = row["data"].get(key)
            if value:
                found[value] = sha(consumer.context.file(value))
    return dict(sorted(found.items()))


def dependency_oleans(cert: dict) -> dict:
    found = {}
    for row in cert["preflights"].values():
        for dep in row["data"]["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"],
                 "AP12 dependency OLean changed during compilation")
            found[dep["module"] + "|" + dep["path"]] = dep["sha256_before"]
    return dict(sorted(found.items()))


def api_review_pins() -> dict:
    review = read(API_REVIEW_MANIFEST)
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and docs["references/contribute.md"] == sha(API_REVIEW / "references/contribute.md")
         and docs["references/prove.md"] == sha(API_REVIEW / "references/prove.md"),
         "Reviewed official API documents differ")
    return {"official_tag": review["official_tag"], "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW_MANIFEST),
            "contribute_sha256": docs["references/contribute.md"],
            "prove_sha256": docs["references/prove.md"]}


def pins(prep, manifest, metadata, payloads, cert):
    return {
        "schema_version": 1,
        "artifact_kind": "ap12-grouped-actual-mean-bounds-publication-preparation",
        "theorem_name": stage.PLATFORM_NAME,
        "environment": publisher.ENV,
        "proposal_status": "Draft",
        "manifest_sha256": sha_bytes(encode(manifest)),
        "validation_sha256": sha(CERT),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "publisher_sha256": sha(Path(publisher.__file__)),
        "api_client_sha256": sha(ROOT / "scripts/p2m_api.py"),
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "offline_wrapper_sha256": sha(SELF),
        "online_wrapper_sha256": sha(ONLINE),
        "exact_name_lookup_sha256": sha(LOOKUP),
        "wire_theorem_sha256": manifest["platform_statement_assembly_sha256"],
        "compiled_comparator_sha256": manifest["statement_sha256"],
        "solution_sha256": manifest["solution_sha256"],
        "target_source_command_sha256": prep["target_source_command_sha256"],
        "target_proof_suffix_sha256": prep["target_proof_suffix_sha256"],
        "inline_exact_source_units_sha256": sha_bytes(encode(prep["inline_exact_source_units"])),
        "runtime_sha256": sha(stage.RUNTIME),
        "ordered_imports": {name: prep["files"][name]["imports"] for name in stage.FILES},
        "compiler_manifest_sha256": {
            prep["files"][name]["manifest"]: sha(STAGE / prep["files"][name]["manifest"])
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
        "local_node_validated": True,
        "submission_ready": False,
        "full_tree_ready": False,
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "http_lookup_scope": "exact theorem name and pinned environment only",
        "durable_post_policy": "saved publish_intent before POST; never repeat a recorded intent",
        "API_used": False,
    }


def hash_gate(current_manifest: dict, frozen: dict) -> None:
    need(current_manifest == read(DEST / "manifest.json")
         and sha_bytes(encode(current_manifest)) == frozen["manifest_sha256"],
         "Publisher manifest differs from frozen AP12 publication")
    direct = {CERT: frozen["validation_sha256"],
              STAGE / "preparation.json": frozen["stage_preparation_sha256"],
              Path(stage.__file__): frozen["stage_producer_sha256"],
              Path(consumer.__file__): frozen["strict_consumer_sha256"],
              SELF: frozen["offline_wrapper_sha256"], ONLINE: frozen["online_wrapper_sha256"],
              LOOKUP: frozen["exact_name_lookup_sha256"],
              ROOT / "scripts/p2m_api.py": frozen["api_client_sha256"],
              Path(publisher.__file__): frozen["publisher_sha256"]}
    for path, expected in direct.items():
        need(sha(path) == expected, "Frozen AP12 implementation/evidence changed: " + str(path))
    for path, expected in frozen["stage_input_hashes"].items():
        need(sha(TASK / path) == expected, "Frozen AP12 stage input changed: " + path)
    for filename, expected in frozen["compiler_manifest_sha256"].items():
        need(sha(STAGE / filename) == expected, "Frozen AP12 compiler manifest changed: " + filename)
    for value, expected in frozen["preflight_artifact_sha256"].items():
        need(sha(consumer.context.file(value)) == expected, "Frozen AP12 preflight changed: " + value)
    for key, expected in frozen["dependency_olean_sha256"].items():
        need(sha(Path(key.split("|", 1)[1])) == expected, "Frozen AP12 dependency OLean changed: " + key)
    for filename, expected in frozen["output_json_sha256"].items():
        need(sha(STAGE / filename) == expected, "Frozen AP12 kernel/proof JSON changed: " + filename)
    need(sha(TASK / frozen["solution_olean"]) == frozen["solution_olean_sha256"],
         "Frozen AP12 solution OLean changed")
    need(api_review_pins() == frozen["official_api_review"], "Reviewed API docs changed")


def pending():
    prep, manifest, metadata, payloads, assembled = static_artifacts()
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    record = {
        "schema_version": 1,
        "artifact_kind": "ap12-grouped-actual-mean-bounds-pending-publication",
        "theorem_name": stage.PLATFORM_NAME,
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "publication_manifest_sha256": sha_bytes(encode(manifest)),
        "metadata_sha256": sha_bytes(encode(metadata)),
        "wire_theorem_sha256": sha_bytes(assembled),
        "compiled_comparator_sha256": manifest["statement_sha256"],
        "solution_sha256": manifest["solution_sha256"],
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "strict_validation_pending": not CERT.is_file(),
        "network_used": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft",
    }
    exact(DEST / "pending-preparation.json", encode(record))
    return {"prepared": True, "validation_pending": not CERT.is_file(),
            "network_used": False, "proposal_status": "Draft",
            "payload_sha256": record["payload_sha256"]}


def prepare():
    prep, manifest, metadata, payloads, assembled, cert = artifacts()
    frozen = pins(prep, manifest, metadata, payloads, cert)
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
    prep, manifest, metadata, payloads, assembled, cert = artifacts()
    frozen = pins(prep, manifest, metadata, payloads, cert)
    need((DEST / "manifest.json").read_bytes() == encode(manifest)
         and (DEST / "validation.json").read_bytes() == CERT.read_bytes()
         and (DEST / "metadata.json").read_bytes() == encode(metadata)
         and (DEST / "wire-theorem-source.lean").read_bytes() == assembled
         and (DEST / "preparation.json").read_bytes() == encode(frozen),
         "Frozen AP12 publication evidence differs")
    for name, raw in payloads.items():
        need((DEST / name).read_bytes() == raw, "Frozen AP12 payload differs: " + name)
    hash_gate(manifest, frozen)
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
