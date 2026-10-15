"""Prepare the AP11 grouped collision-rate theorem publication without networking.

``--prepare-pending`` freezes the academic payload before compilation finishes.
Final preparation requires exact replay of the four primary compiler contexts
and the additive source-helper CI certificate.  No mode starts Lean or an API.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_grouped_collision_rate_node as consumer
import publish_standalone_platform_node as publisher
import stage_grouped_collision_rate_node as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication"
CERT = consumer.CERT
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_grouped_collision_rate_node.py"
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
        raise ValueError("Frozen grouped-collision publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def academic_metadata(prep: dict) -> dict:
    statement = (
        "Let $\\nu\\in\\mathbb R$ and let $d$ be fixed approximation data. "
        "Write $m,K,v_0,\\theta,A,\\eta$ for its dimension, multiplicity, "
        "row scale, interpolation scale, simplex scale, and collision parameter. "
        "For denominator weights $w_i=\\lceil\\log q_i\\rceil>0$, let $M(H)$ "
        "be the weighted interpolation-row count and let $N(H)$ be the low-index "
        "weighted-simplex count. With $c=\\log(2)/4$, define\n\n"
        "$$\n\\gamma(H)=\\frac{c\\eta^2M(H)}{H N(H)}.\n$$\n\n"
        "Then, as $H\\to+\\infty$,\n\n"
        "$$\n\\gamma(H)\\longrightarrow\\gamma_\\infty"
        "=\\frac{c\\eta^2K\\theta^m}{(m+1)v_0A^m}.\n$$\n\n"
        "The statement is uniform in the theorem's actual input $d:\\mathrm{FixedData}(\\nu)$; "
        "it imposes no separate hypothesis $\\nu>2$."
    )
    explanation = (
        "The denominators in $d$ satisfy $q_i\\ge2$, so "
        "$w_i=\\lceil\\log q_i\\rceil$ are positive rational weights. "
        "The weighted-simplex counting theorem gives the leading $H^m$ term of "
        "$N(H)$.  Summing the admissible row levels adds one degree, so $M(H)$ "
        "has a leading $H^{m+1}$ term.  After dividing by $H N(H)$, the common "
        "simplex-volume and weight factors cancel, leaving\n\n"
        "$$\n\\frac{M(H)}{H N(H)}\\longrightarrow "
        "\\frac{K\\theta^m}{(m+1)v_0A^m}.\n$$\n\n"
        "Positivity of the weights and the eventual positivity of the finite "
        "simplex count justify the quotient limit. Multiplication by the fixed "
        "factor $c\\eta^2$ yields the displayed limit for $\\gamma(H)$.  The "
        "formal solution preserves the original thirty source helper commands "
        "and the original target proof; the mathematical argument is the "
        "weighted row-count/simplex-count asymptotic ratio, rather than a tactic trace."
    )
    witness = {
        "source_commit": stage.COMMIT,
        "source_url": prep["source_url"],
        "source_module": stage.TARGET_MODULE,
        "source_path": task_rel(stage.source_path(stage.TARGET_MODULE)),
        "source_sha256": sha(stage.source_path(stage.TARGET_MODULE)),
        "original_source_path": task_rel(stage.source_path(stage.TARGET_MODULE, "source")),
        "original_source_sha256": sha(stage.source_path(stage.TARGET_MODULE, "source")),
        "target_ast": prep["target_ast"],
        "target_source_command_sha256": prep["target_source_command_sha256"],
        "target_proof_suffix_sha256": prep["target_proof_suffix_sha256"],
        "inline_exact_source_command_count": len(prep["inline_exact_source_units"]),
        "inline_exact_source_units_sha256": sha_bytes(encode(prep["inline_exact_source_units"])),
        "graph_closure_count": len(prep["graph_closure_names"]),
        "mathematical_role": (
            "Asymptotic collision-rate lemma converting weighted row and simplex "
            "counts into the explicit constant used by the determinant contradiction."
        ),
    }
    return {
        "theorem_name": stage.TARGET,
        "theorem_title": "The collision rate converges to its explicit weighted-simplex limit",
        "natural_language_statement": statement,
        "explanation": explanation,
        "tags": ["asymptotics", "weighted-simplex", "number-theory", "openai-pi-exponent-017"],
        "source_witness": witness,
    }


def statement_parts(prep: dict):
    statement = STAGE / stage.TARGET_OUTPUT
    raw = statement.read_bytes()
    formal = prep["formal_statement"].replace("\r\n", "\n").encode()
    start = raw.find(formal)
    need(start >= 0 and raw.count(formal) == 1, "Formal theorem is not unique in compiled comparator")
    preamble, suffix = raw[:start], raw[start + len(formal):]
    expected_suffix = stage.GROUP_FOOTERS[stage.TARGET_MODULE]
    need(suffix == b"\n" + expected_suffix,
         "Comparator suffix differs from the exact source namespace closure")
    return statement, preamble.decode(), formal.decode(), preamble + formal


def static_artifacts():
    stage.check_only()
    prep = read(STAGE / "preparation.json")
    need(prep["source_name"] == stage.TARGET
         and prep["source_module"] == stage.TARGET_MODULE
         and prep["source_commit"] == stage.COMMIT
         and prep["source_url"].endswith("DeterminantContradiction.lean#L108-L125"),
         "Grouped-collision preparation identity/provenance differs")
    need(len(prep["graph_closure_names"]) == 71
         and len(prep["inline_helper_names"]) == 30
         and len(prep["inline_exact_source_units"]) == 30
         and prep["global_solution_name"] == "solution"
         and prep["global_solution_preserves_literal_source_proof"] is True,
         "Grouped-collision exact closure/helper contract differs")
    need(list(prep["files"]) == stage.FILES
         and [prep["files"][name]["mode"] for name in stage.FILES] == stage.MODES
         and [prep["files"][name]["emit_olean"] for name in stage.FILES] ==
             [False, True, False, False],
         "Grouped-collision ordered compiler modes differ")
    expected_imports = [stage.IMPORTS, stage.IMPORTS,
                        ["Lean", stage.TARGET_MODULE], ["Lean", stage.SOLUTION_MODULE]]
    need([prep["files"][name]["imports"] for name in stage.FILES] == expected_imports,
         "Grouped-collision ordered imports differ")

    statement, preamble, formal, assembled = statement_parts(prep)
    solution = STAGE / stage.SOLUTION_OUTPUT
    original_command = (STAGE / "original-target-command.lean.txt").read_bytes()
    unit = prep["target_ast"]
    ns = unit["nameRange"]["start"]["offset"] - unit["start"]["offset"]
    ne = unit["nameRange"]["end"]["offset"] - unit["start"]["offset"]
    renamed = (original_command[:ns] + b"solution" + original_command[ne:]).replace(b"\r\n", b"\n")
    solution_raw = solution.read_bytes()
    need(solution_raw.endswith(renamed + b"\n")
         and renamed[renamed.find(b":= by"):] ==
             original_command[unit["valueStart"]["offset"] - unit["start"]["offset"]:].replace(b"\r\n", b"\n")
         and b"sorry" not in solution_raw,
         "Global solution differs from the literal renamed source theorem")
    before = solution_raw[:-len(renamed) - 1]
    need(b"theorem solution" not in before
         and before.rstrip().endswith(b"open scoped Topology"),
         "Final theorem solution is not global top-level")
    need((STAGE / "wire-theorem-source.lean").read_bytes() == statement.read_bytes(),
         "Stage wire theorem differs from compiled comparator")

    metadata = academic_metadata(prep)
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap11-grouped-collision-rate-publication-manifest",
        "theorem_name": stage.TARGET,
        "preamble": preamble,
        "formal_statement": formal,
        "statement": root_rel(statement),
        "statement_sha256": sha(statement),
        "platform_statement_assembly_sha256": sha_bytes(assembled),
        "comparator_namespace_suffix_sha256": sha_bytes(statement.read_bytes()[len(assembled):]),
        "solution": root_rel(solution),
        "solution_sha256": sha(solution),
        "source_commit": stage.COMMIT,
        "source_url": prep["source_url"],
        "source_module": stage.TARGET_MODULE,
        "source_ast_unit_sha256": prep["target_source_command_sha256"],
        "inline_exact_source_command_count": 30,
        "graph_closure_count": 71,
        "proposal_status": "Draft",
        "validated": CERT.is_file(),
        "local_standalone_validated": CERT.is_file(),
        "submission_ready": False,
        "full_tree_ready": False,
    }
    payloads = publisher.payloads(DEST, manifest, metadata)
    problem = json.loads(payloads["publish-payload.json"])["problems"][0]
    verify = json.loads(payloads["verification-payload.json"])
    need(problem["theorem_name"] == stage.TARGET
         and (problem["preamble"] + problem["formal_statement"]).encode() == assembled
         and problem["source"] == prep["source_url"],
         "Grouped-collision publish payload changes the theorem assembly/provenance")
    need(verify["target_theorem_name"] == stage.TARGET
         and verify["theorem_id"] is None
         and verify["file"]["sha256"] == sha(solution)
         and verify["file"]["utf8"].encode() == solution_raw,
         "Grouped-collision verification payload changes the literal solution")
    return prep, manifest, metadata, payloads, assembled


def _owner(owner: dict, module: str) -> None:
    need(set(owner) == {"kind", "module", "moduleIndex"}
         and owner["kind"] == "ImportedModule" and owner["module"] == module
         and type(owner["moduleIndex"]) is int and owner["moduleIndex"] >= 0,
         "Proof CI owner differs from asserted imported module: " + module)


def replay_certificate(cert: dict, prep: dict) -> None:
    need(consumer.validate(write=False) == cert,
         "AP11 certificate differs from exact strict saved-evidence replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "ap11-grouped-collision-rate-strict-actual-node-validation"
         and cert["validated"] is True and cert["submission_ready"] is False
         and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False,
         "AP11 certificate state differs")
    need(cert["source_name"] == stage.TARGET and cert["solution_name"] == "solution"
         and cert["source_module"] == stage.TARGET_MODULE
         and cert["solution_module"] == stage.SOLUTION_MODULE
         and cert["source_commit"] == stage.COMMIT,
         "AP11 certificate identity/provenance differs")
    need(cert["stage_preparation_sha256"] == sha(STAGE / "preparation.json")
         and cert["source_ast_unit_sha256"] == sha(STAGE / "original-target-command.lean.txt")
         and cert["wire_theorem_sha256"] == sha(STAGE / "wire-theorem-source.lean"),
         "AP11 source AST/wire/stage pins differ")
    need(cert["source_type_equals_global_solution_type"] is True
         and cert["source_helper_types_equal"] is True
         and cert["source_helper_full_def_values_equal"] is True
         and cert["source_original_proof_byte_exact_after_name_change"] is True
         and cert["global_top_level_theorem_solution"] is True
         and cert["type_only_theorem_values_null"] is True
         and cert["source_helper_count"] == 30
         and cert["Std3_only"] is True
         and cert["source_axioms"] == cert["generated_axioms"]
         and set(cert["source_axioms"]) <= STD3,
         "AP11 type/proof/helper/global/Std3 gates differ")
    _owner(cert["source_owner"], stage.TARGET_MODULE)
    _owner(cert["generated_owner"], stage.SOLUTION_MODULE)
    source_modules = {row["name"]: row["module"] for row in prep["inline_exact_source_units"]}
    need(set(cert["source_helper_actual_owners"]) == set(prep["inline_helper_names"])
         and set(cert["generated_helper_actual_owners"]) == set(prep["inline_helper_names"]),
         "AP11 actual helper owner domain differs")
    for name in prep["inline_helper_names"]:
        _owner(cert["source_helper_actual_owners"][name], source_modules[name])
        _owner(cert["generated_helper_actual_owners"][name], stage.SOLUTION_MODULE)
    need(isinstance(cert["actual_private_helper_pairs"], list)
         and len({tuple(x) for x in cert["actual_private_helper_pairs"]}) ==
             len(cert["actual_private_helper_pairs"])
         and isinstance(cert["external_elaboration_reference_differences"], dict),
         "AP11 finite private-helper pairing/reference envelope differs")
    need(set(cert["primary_preflights"]) == set(stage.FILES)
         and cert["source_helper_preflight"]["data"]["success"] is True
         and 0 < cert["max_file_seconds"] <= 300,
         "AP11 five-preflight domain or budget differs")
    for path, expected in cert["implementation_hashes"].items():
        need(sha(TASK / path) == expected, "AP11 input implementation changed: " + path)
    for path, expected in cert["output_json_sha256"].items():
        need(sha(TASK / path) == expected, "AP11 kernel/proof output changed: " + path)
    for filename, theorem_name in ((stage.SOURCE_TYPE_JSON, stage.TARGET),
                                   (stage.GENERATED_TYPE_JSON, "solution")):
        rows = read(STAGE / filename)
        target = next(row for row in rows if row["name"] == theorem_name)
        need(target["value"] is None, "Type snapshot theorem proof value is not null: " + filename)
    olean = TASK / cert["solution_olean"]
    need(olean.is_file() and sha(olean) == cert["solution_olean_sha256"],
         "AP11 actual compiled solution OLean changed")
    expected_provider_keys = ({"ap9/" + key for key in stage.ap9.CONFIGS} |
                              {"ap10/" + key for key in stage.ap10.CONFIGS})
    need(set(cert["certified_AP9_AP10_provider_bindings"]) == expected_provider_keys,
         "AP11 certified provider binding domain differs")


def artifacts():
    prep, manifest, metadata, payloads, assembled = static_artifacts()
    need(CERT.is_file(), "Actual AP11 grouped-collision validation certificate is pending")
    cert = read(CERT)
    replay_certificate(cert, prep)
    return prep, manifest, metadata, payloads, assembled, cert


def evidence_artifact_hashes(cert: dict) -> dict:
    found = {}
    for row in [*cert["primary_preflights"].values(), cert["source_helper_preflight"]]:
        data = row["data"]
        for key in ("source", "manifest", "log"):
            value = data.get(key)
            if value:
                found[str(value)] = sha(consumer.context.file(value))
    return dict(sorted(found.items()))


def dependency_olean_hashes(cert: dict) -> dict:
    found = {}
    for row in [*cert["primary_preflights"].values(), cert["source_helper_preflight"]]:
        for dep in row["data"]["dependency_oleans"]:
            need(dep["sha256_before"] == dep["sha256_after"]
                 and dep["stable_during_compile"] is True,
                 "An AP11 imported OLean was not stable during compilation")
            found[dep["module"] + "|" + dep["path"]] = dep["sha256_before"]
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
        "artifact_kind": "ap11-grouped-collision-rate-publication-preparation",
        "theorem_name": stage.TARGET,
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
        "wire_theorem_sha256": manifest["platform_statement_assembly_sha256"],
        "compiled_comparator_sha256": manifest["statement_sha256"],
        "solution_sha256": manifest["solution_sha256"],
        "target_source_command_sha256": prep["target_source_command_sha256"],
        "target_proof_suffix_sha256": prep["target_proof_suffix_sha256"],
        "inline_exact_source_units_sha256": sha_bytes(encode(prep["inline_exact_source_units"])),
        "runtime_sha256": prep["runtime_sha256"],
        "ordered_imports": {name: prep["files"][name]["imports"] for name in stage.FILES},
        "compiler_manifest_sha256": {
            prep["files"][name]["manifest"]: sha(STAGE / prep["files"][name]["manifest"])
            for name in stage.FILES},
        "stage_input_hashes": prep["input_hashes"],
        "preflight_artifact_sha256": evidence_artifact_hashes(cert),
        "dependency_olean_sha256": dependency_olean_hashes(cert),
        "output_json_sha256": cert["output_json_sha256"],
        "solution_olean": cert["solution_olean"],
        "solution_olean_sha256": cert["solution_olean_sha256"],
        "actual_imported_modules": {"source": cert["source_owner"],
                                    "solution": cert["generated_owner"]},
        "certified_AP9_AP10_provider_bindings": cert["certified_AP9_AP10_provider_bindings"],
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
    need(current_manifest == read(DEST / "manifest.json")
         and sha_bytes(encode(current_manifest)) == frozen["manifest_sha256"],
         "Publisher manifest differs from frozen AP11 publication")
    direct = {CERT: frozen["validation_sha256"],
              STAGE / "preparation.json": frozen["stage_preparation_sha256"],
              Path(stage.__file__): frozen["stage_producer_sha256"],
              Path(consumer.__file__): frozen["strict_consumer_sha256"],
              SELF: frozen["offline_wrapper_sha256"],
              ONLINE: frozen["online_wrapper_sha256"],
              ROOT / "scripts/p2m_api.py": frozen["api_client_sha256"],
              Path(publisher.__file__): frozen["publisher_sha256"]}
    for path, expected in direct.items():
        need(sha(path) == expected, "Frozen AP11 implementation/evidence changed: " + str(path))
    for path, expected in frozen["stage_input_hashes"].items():
        need(sha(TASK / path) == expected, "Frozen AP11 stage input changed: " + path)
    for filename, expected in frozen["compiler_manifest_sha256"].items():
        need(sha(STAGE / filename) == expected, "Frozen AP11 compiler manifest changed: " + filename)
    for value, expected in frozen["preflight_artifact_sha256"].items():
        need(sha(consumer.context.file(value)) == expected, "Frozen AP11 preflight artifact changed: " + value)
    for key, expected in frozen["dependency_olean_sha256"].items():
        _, value = key.split("|", 1)
        need(sha(Path(value)) == expected, "Frozen AP11 imported OLean changed: " + key)
    for path, expected in frozen["output_json_sha256"].items():
        need(sha(TASK / path) == expected, "Frozen AP11 kernel/proof JSON changed: " + path)
    need(sha(TASK / frozen["solution_olean"]) == frozen["solution_olean_sha256"],
         "Frozen AP11 solution OLean changed")
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
        "artifact_kind": "ap11-grouped-collision-rate-pending-publication",
        "theorem_name": stage.TARGET,
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
         "Frozen AP11 publication evidence differs")
    for name, raw in payloads.items():
        need((DEST / name).read_bytes() == raw, "Frozen AP11 payload differs: " + name)
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
