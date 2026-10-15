"""Freeze the AP8 full-row-minor publication bundle without networking.

``--prepare-pending`` writes reviewable payloads before compilation finishes.
Final preparation is possible only after the pure saved-evidence consumer has
replayed the actual four-context certificate.  No mode starts Lean or an API.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_full_row_minor_node as consumer
import publish_standalone_platform_node as publisher
import stage_full_row_minor_node as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication"
CERT = consumer.CERT
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_full_row_minor_node.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
API_REVIEW_MANIFEST = API_REVIEW / "manifest.json"
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
        raise ValueError("Frozen full-row-minor publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def academic_metadata(prep: dict) -> dict:
    statement = (
        "Let $R$ and $C$ be finite index types, let $K$ be a field, and let "
        "$A=(A_{r,c})_{r\\in R,\\,c\\in C}$ be an $R$-by-$C$ matrix over $K$. "
        "Assume equality on $R$ is decidable and multiplication by $A$ defines a "
        "surjective $K$-linear map $K^C\\to K^R$. Then there is a function "
        "$s:R\\to C$ such that $s$ is injective and\n\n"
        "$$\n\\det\\bigl(A[\\operatorname{id}_R,s]\\bigr)\\ne 0.\n$$\n\n"
        "Thus the selected columns form a nonsingular square minor containing every "
        "row. This generic matrix-rank lemma is a direct core dependency for choosing "
        "a nonvanishing interpolation minor in the $\\pi$ irrationality-measure argument."
    )
    explanation = (
        "Let $A:K^C\\to K^R$ be the surjective matrix map in the statement. We prove\n\n"
        "$$\n\\exists s:R\\to C,\\qquad s\\text{ injective},\\qquad "
        "\\det\\bigl(A[\\operatorname{id}_R,s]\\bigr)\\ne0.\n$$\n\n"
        "Choose a matrix right inverse $B$, so $AB=I_R$ and hence $\\det(AB)=1$. "
        "Expanding this determinant in Cauchy--Binet form gives a finite sum over "
        "functions $p:R\\to C$:\n\n"
        "$$\n\\det(AB)=\\sum_{p:R\\to C} "
        "\\det\\bigl(A[\\operatorname{id}_R,p]\\bigr)"
        "\\prod_{i\\in R}B_{p(i),i}.\n$$\n\n"
        "Because the sum equals $1$, at least one summand is nonzero, and its matrix "
        "minor therefore has nonzero determinant. If its column selector identified "
        "two different rows, the square minor would have two equal columns and zero "
        "determinant. The selector is consequently injective."
    )
    witness = {
        "source_commit": stage.SOURCE_COMMIT,
        "source_url": stage.SOURCE_URL,
        "source_module": stage.MODULE,
        "source_path": prep["source_path"],
        "source_sha256": prep["source_sha256"],
        "original_source_path": prep["original_source_path"],
        "original_source_sha256": prep["original_source_sha256"],
        "source_byte_range": prep["source_byte_range"],
        "source_line_range": prep["source_line_range"],
        "source_ast_unit": prep["source_ast_unit"],
        "source_unit_sha256": prep["source_unit_sha256"],
        "original_port_command_equal_modulo_line_endings":
            prep["original_port_command_equal_modulo_line_endings"],
        "mathematical_role": (
            "Generic finite matrix-rank lemma and direct core dependency for the "
            "nonsingular interpolation minor used by OpenAI math family 017."
        ),
    }
    return {
        "theorem_name": stage.NAME,
        "theorem_title": "A surjective matrix has a nonsingular full-row minor",
        "natural_language_statement": statement,
        "explanation": explanation,
        "tags": ["linear-algebra", "matrix-theory", "openai-pi-exponent-017"],
        "source_witness": witness,
    }


def static_artifacts():
    stage.check_only()
    prep = read(STAGE / "preparation.json")
    need(prep["source_name"] == stage.NAME and prep["source_module"] == stage.MODULE
         and prep["source_commit"] == stage.SOURCE_COMMIT
         and prep["source_url"] == stage.SOURCE_URL,
         "Full-row-minor preparation identity/provenance differs")
    need(prep["source_byte_range"] == stage.BYTE_RANGE
         and prep["source_line_range"] == [135, 166]
         and prep["source_unit_sha256"] == stage.UNIT_SHA
         and prep["source_sha256"] == stage.SOURCE_SHA,
         "Full-row-minor source AST witness differs")
    need(list(prep["files"]) == stage.FILES,
         "Full-row-minor compiler file order differs")
    need([prep["files"][name]["imports"] for name in stage.FILES] ==
         [stage.IMPORTS, stage.IMPORTS, ["Lean", stage.MODULE],
          ["Lean", stage.SOLUTION_MODULE]],
         "Full-row-minor ordered import contract differs")
    need([prep["files"][name]["mode"] for name in stage.FILES] == stage.MODES
         and [prep["files"][name]["emit_olean"] for name in stage.FILES] ==
         [False, True, False, False],
         "Full-row-minor compiler modes differ")

    statement = STAGE / stage.SOURCE_OUTPUT
    solution = STAGE / stage.SOLUTION_OUTPUT
    assembled = (prep["preamble"] + prep["formal_statement"]).encode("utf-8")
    _, _, expected_statement, expected_solution = stage.assembly()
    need(statement.read_bytes() == assembled == expected_statement
         and (STAGE / "wire-theorem-source.lean").read_bytes() == assembled
         and sha_bytes(assembled) == prep["compiled_statement_assembly_sha256"],
         "Compiled Thm is not exact preamble + formal_statement bytes")
    need(solution.read_bytes() == expected_solution
         and sha(solution) == prep["solution_source_sha256"]
         and prep["solution_binding"] == "Global top-level literal theorem solution",
         "Literal global solution differs from the exact renamed source command")
    source_command = stage.source_unit()
    renamed = source_command.replace(
        b"theorem exists_full_row_minor_of_surjective", b"theorem solution", 1)
    need(expected_solution.endswith(renamed) and renamed != source_command
         and b"namespace " not in expected_solution[:-len(renamed)]
         and b"sorry" not in expected_solution,
         "Solution is namespaced, incomplete, or not the literal source proof")

    metadata = academic_metadata(prep)
    need(set(metadata) == {"theorem_name", "theorem_title",
                           "natural_language_statement", "explanation", "tags",
                           "source_witness"},
         "Full-row-minor academic metadata schema differs")
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap8-full-row-minor-publication-manifest",
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
        "source_ast_unit_sha256": stage.UNIT_SHA,
        "proposal_status": "Draft",
        "validated": CERT.is_file(),
        "local_standalone_validated": CERT.is_file(),
        "submission_ready": False,
        "full_tree_ready": False,
    }
    payloads = publisher.payloads(DEST, manifest, metadata)
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    verify = json.loads(payloads["verification-payload.json"])
    need(problem["theorem_name"] == stage.NAME
         and (problem["preamble"] + problem["formal_statement"]).encode("utf-8") == assembled,
         "Publish payload changes the exact compiled theorem bytes")
    need(problem["source"] == stage.SOURCE_URL
         and verify["target_theorem_name"] == stage.NAME
         and verify["theorem_id"] is None
         and verify["file"]["sha256"] == sha(solution)
         and verify["file"]["utf8"].encode("utf-8") == solution.read_bytes(),
         "Verification payload changes the source witness or literal solution")
    return prep, manifest, metadata, payloads, assembled


def _owner(owner: dict, module: str) -> None:
    need(set(owner) == {"kind", "module", "moduleIndex"}
         and owner["kind"] == "ImportedModule" and owner["module"] == module
         and type(owner["moduleIndex"]) is int and owner["moduleIndex"] >= 0,
         "Proof reference owner is not the asserted imported module: " + module)


def replay_certificate(cert: dict, prep: dict) -> None:
    current = consumer.validate(write=False)
    need(current == cert, "Certificate differs from the frozen strict consumer replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap8-full-row-minor-strict-actual-node-validation"
         and cert["validated"] is True and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False,
         "Full-row-minor certificate state differs")
    need(cert["source_name"] == stage.NAME and cert["solution_name"] == "solution"
         and cert["source_module"] == stage.MODULE
         and cert["solution_module"] == stage.SOLUTION_MODULE
         and cert["source_commit"] == stage.SOURCE_COMMIT
         and cert["source_url"] == stage.SOURCE_URL,
         "Full-row-minor certificate identity/provenance differs")
    need(cert["source_sha256"] == sha(stage.SOURCE)
         and cert["original_source_sha256"] == sha(stage.ORIGINAL)
         and cert["source_ast_unit_sha256"] == stage.UNIT_SHA
         and cert["stage_preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["wire_theorem_sha256"] == prep["compiled_statement_assembly_sha256"],
         "Full-row-minor certificate input/wire pins differ")
    need(cert["source_type_equals_solution_type"] is True
         and cert["source_proof_byte_exact_after_name_change"] is True
         and cert["top_level_global_theorem_solution"] is True
         and cert["type_only_theorem_values_null"] is True
         and cert["Std3_only"] is True
         and cert["source_axioms"] == cert["generated_axioms"]
         and set(cert["source_axioms"]) <= STD3,
         "Full-row-minor type/proof/global/Std3 gates differ")
    _owner(cert["source_owner"], stage.MODULE)
    _owner(cert["generated_owner"], stage.SOLUTION_MODULE)
    source_helpers = {pair[0] for pair in cert["automatic_inline_helper_pairs"]}
    generated_helpers = {pair[1] for pair in cert["automatic_inline_helper_pairs"]}
    need(cert["actual_source_project_references"] == sorted(source_helpers)
         and cert["actual_generated_project_references"] == sorted(generated_helpers),
         "Generic proof project-reference closure differs from its certified helpers")
    need(set(cert["preflights"]) == set(stage.FILES)
         and 0 < cert["max_file_seconds"] <= 300,
         "Full-row-minor exact four-preflight domain or budget differs")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected,
             "Full-row-minor input implementation changed: " + path)
    for path, expected in cert["output_json_sha256"].items():
        need(sha(TASK / path) == expected,
             "Full-row-minor kernel/proof output changed: " + path)
    for filename, theorem_name in ((stage.SOURCE_TYPE_JSON, stage.NAME),
                                   (stage.GENERATED_TYPE_JSON, "solution")):
        rows = read(STAGE / filename)
        need(len(rows) == 1 and rows[0]["name"] == theorem_name
             and rows[0]["value"] is None,
             "Type snapshot theorem proof value is not null: " + filename)
    olean = TASK / cert["solution_olean"]
    need(olean.is_file() and sha(olean) == cert["solution_olean_sha256"],
         "Actual compiled solution OLean changed")


def artifacts():
    prep, manifest, metadata, payloads, assembled = static_artifacts()
    need(CERT.is_file(), "Actual full-row-minor validation certificate is pending")
    cert = read(CERT)
    replay_certificate(cert, prep)
    return prep, manifest, metadata, payloads, assembled, cert


def evidence_artifact_hashes(cert: dict) -> dict:
    found = {}
    for row in cert["preflights"].values():
        data = row["data"]
        for key in ("source", "manifest", "log"):
            value = data.get(key)
            if value:
                path = consumer.context.file(value)
                found[str(value)] = sha(path)
    return dict(sorted(found.items()))


def dependency_olean_hashes(cert: dict) -> dict:
    found = {}
    for row in cert["preflights"].values():
        for dep in row["data"]["dependency_oleans"]:
            key = dep["module"] + "|" + dep["path"]
            need(dep["sha256_before"] == dep["sha256_after"]
                 and dep["stable_during_compile"] is True,
                 "An imported OLean was not stable during compilation")
            found[key] = dep["sha256_before"]
    return dict(sorted(found.items()))


def api_review_pins() -> dict:
    review = read(API_REVIEW_MANIFEST)
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and docs["references/contribute.md"] == sha(API_REVIEW / "references/contribute.md")
         and docs["references/prove.md"] == sha(API_REVIEW / "references/prove.md"),
         "Reviewed official publication API documents differ")
    return {"official_tag": review["official_tag"],
            "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW_MANIFEST),
            "contribute_sha256": docs["references/contribute.md"],
            "prove_sha256": docs["references/prove.md"]}


def pins(prep, manifest, metadata, payloads, cert):
    return {
        "schema_version": 1,
        "artifact_kind": "ap8-full-row-minor-publication-preparation",
        "theorem_name": stage.NAME,
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
        "wire_theorem_sha256": prep["compiled_statement_assembly_sha256"],
        "solution_sha256": manifest["solution_sha256"],
        "source_sha256": prep["source_sha256"],
        "original_source_sha256": prep["original_source_sha256"],
        "source_ast_unit_sha256": prep["source_unit_sha256"],
        "runtime_sha256": prep["runtime_sha256"],
        "ordered_imports": {name: prep["files"][name]["imports"] for name in stage.FILES},
        "compiler_manifest_sha256": {
            prep["files"][name]["manifest"]: sha(STAGE / prep["files"][name]["manifest"])
            for name in stage.FILES
        },
        "stage_input_hashes": prep["input_hashes"],
        "preflight_artifact_sha256": evidence_artifact_hashes(cert),
        "dependency_olean_sha256": dependency_olean_hashes(cert),
        "output_json_sha256": cert["output_json_sha256"],
        "solution_olean": cert["solution_olean"],
        "solution_olean_sha256": cert["solution_olean_sha256"],
        "actual_imported_modules": {
            "source": cert["source_owner"], "solution": cert["generated_owner"]},
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "official_api_review": api_review_pins(),
        "local_node_validated": True,
        "submission_ready": False,
        "full_tree_ready": False,
        "verification_payload_is_offline_descriptor": True,
        "verification_theorem_id_late_bound_only": True,
        "http_lookup_scope": "exact theorem name and pinned environment only; no graph reconstruction",
        "durable_post_policy": "saved publish_intent before POST; never repeat a recorded intent",
        "API_used": False,
    }


def hash_gate(current_manifest: dict, frozen: dict) -> None:
    expected_manifest = read(DEST / "manifest.json")
    need(current_manifest == expected_manifest
         and sha_bytes(encode(current_manifest)) == frozen["manifest_sha256"],
         "Publisher manifest differs from frozen full-row-minor publication")
    direct = {
        CERT: frozen["validation_sha256"],
        STAGE / "preparation.json": frozen["stage_preparation_sha256"],
        Path(stage.__file__): frozen["stage_producer_sha256"],
        Path(consumer.__file__): frozen["strict_consumer_sha256"],
        SELF: frozen["offline_wrapper_sha256"],
        ONLINE: frozen["online_wrapper_sha256"],
        ROOT / "scripts/p2m_api.py": frozen["api_client_sha256"],
        Path(publisher.__file__): frozen["publisher_sha256"],
    }
    for path, expected in direct.items():
        need(sha(path) == expected, "Frozen publication implementation/evidence changed: " + str(path))
    for path, expected in frozen["stage_input_hashes"].items():
        need(sha(TASK / path) == expected, "Frozen stage input changed: " + path)
    for filename, expected in frozen["compiler_manifest_sha256"].items():
        need(sha(STAGE / filename) == expected, "Frozen compiler manifest changed: " + filename)
    for value, expected in frozen["preflight_artifact_sha256"].items():
        need(sha(consumer.context.file(value)) == expected,
             "Frozen preflight artifact changed: " + value)
    for key, expected in frozen["dependency_olean_sha256"].items():
        _, value = key.split("|", 1)
        need(sha(Path(value)) == expected, "Frozen imported OLean changed: " + key)
    for path, expected in frozen["output_json_sha256"].items():
        need(sha(TASK / path) == expected, "Frozen kernel/proof JSON changed: " + path)
    need(sha(TASK / frozen["solution_olean"]) == frozen["solution_olean_sha256"],
         "Frozen solution OLean changed")
    need(api_review_pins() == frozen["official_api_review"],
         "Reviewed official API documentation changed")


def pending():
    prep, manifest, metadata, payloads, assembled = static_artifacts()
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "wire-theorem-source.lean", assembled)
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    record = {
        "schema_version": 1,
        "artifact_kind": "ap8-full-row-minor-pending-publication",
        "theorem_name": stage.NAME,
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
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
         "Frozen full-row-minor publication evidence differs")
    for name, raw in payloads.items():
        need((DEST / name).read_bytes() == raw,
             "Frozen full-row-minor payload differs: " + name)
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
