"""Prepare the original AP20 translation-count logarithm theorem offline.

The wrapper stays inert until the genuine four-context derived certificate
exists. It performs one strict replay and separately checks parsed-report
equality and the consumer's exact Windows JSON encoding before freezing hashes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_log_translation_count_node_v5 as consumer
import stage_log_translation_count_node as stage

TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_log_translation_term_count_node_v7.py"
DEST = STAGE / "publication-v7"
CERT = STAGE / consumer.CERTIFICATE
LOOKUP = stage.LOOKUP
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
API = ROOT / "scripts/p2m_api.py"
API_REVIEW = stage.V / "api-review-20261011-v0.12.4/manifest.json"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return digest(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("utf-8")


def certificate_bytes(value):
    """Match the frozen consumer's Windows indent-2 write_text output exactly."""
    return stage.encode(value).replace(b"\n", b"\r\n")


def resolve(path):
    p = Path(path)
    return p if p.is_absolute() else TASK / p


def pin_key(path):
    path = Path(path).resolve()
    try:
        return path.relative_to(TASK.resolve()).as_posix()
    except ValueError:
        return str(path)


def exact(path, raw):
    path = Path(path)
    if path.exists():
        need(path.read_bytes() == raw, "Frozen translation artifact differs: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def split_wire(raw):
    marker = ("theorem " + stage.TARGET).encode()
    need(raw.count(marker) == 1, "Exact translation theorem marker differs")
    at = raw.index(marker)
    preamble, formal = raw[:at].decode(), raw[at:].decode()
    need(formal.startswith("theorem " + stage.TARGET)
         and formal.endswith(":= by\n  sorry\n") and formal.count("sorry") == 1,
         "Exact translation Open comparator differs")
    return preamble, formal


def static():
    stage.check_only()
    prep = read(STAGE / "preparation.json")
    need(prep["artifact_kind"] ==
             "ap20-log-translation-count-four-original-AST-proof-preparation"
         and prep["source_name"] == stage.TARGET
         and prep["platform_name"] == stage.TARGET
         and prep["source_commit"] == stage.route.COMMIT
         and prep["original_source_lines"] == 42
         and len(prep["exact_source_units"]) == 4
         and prep["three_helper_proof_suffixes_unchanged"] is True
         and prep["target_proof_suffix_unchanged"] is True
         and prep["global_solution_name_only_rewritten"] is True
         and prep["published_data_definition_id"] ==
             "04008248-130e-40ba-b6a3-df3e9b9df91b"
         and prep["accepted_logdiv_theorem_id"] ==
             "8b1c0341-2978-4a9d-8acc-8a5e3538cbda"
         and prep["proposal_status"] == "Draft"
         and prep["validated"] is False and prep["submission_ready"] is False,
         "Original four-AST translation preparation differs")

    lookup = read(LOOKUP)
    rows = [row for row in lookup["records"] if row["theorem_name"] == stage.TARGET]
    need(lookup["environment"] == ENV and lookup["request_methods"] == ["GET"]
         and len(rows) == 1 and rows[0]["environment"] == ENV
         and rows[0]["lookup_total"] == 0 and rows[0]["matches"] == []
         and len(rows[0]["pages"]) == 1 and rows[0]["pages"][0]["http_status"] == 200
         and rows[0]["pages"][0]["parsed_body"] == {"theorems": [], "total": 0}
         and digest(rows[0]["pages"][0]["raw_body_utf8"].encode()) ==
             rows[0]["pages"][0]["raw_body_sha256"],
         "Saved exact-name lookup is not the genuine zero-match predecessor")

    theorem = (STAGE / stage.TARGET_OUTPUT).read_bytes()
    solution = (STAGE / stage.SOLUTION_OUTPUT).read_bytes()
    preamble, formal = split_wire(theorem)
    need(solution.count(b"theorem solution ") == 1 and b"sorry" not in solution
         and ("import " + stage.MODULE).encode() not in solution,
         "Closed global translation solution differs")
    target_unit = next(row for row in prep["exact_source_units"]
                       if row["name"] == stage.TARGET)
    source_url = ("https://github.com/openai/math/blob/" + prep["source_commit"] + "/"
                  + target_unit["original"].removeprefix("source/"))
    metadata = {
        "theorem_title": "Negligible logarithmic growth of the translation count",
        "natural_language_statement": (
            "For every natural number $m$ and real $v>0$, the translation count "
            "$T_m(v,H)$ has polynomial growth of degree $2m+1$, hence "
            "$$\\frac{\\log T_m(v,H)}{H}\\longrightarrow 0$$ as $H\\to+\\infty$. "
            "The source proof first establishes the positive normalized limit "
            "$T_m(v,H)/H^{2m+1}\\to 1/v$ from the floor-count limits and then applies "
            "the accepted logarithm-of-polynomial-growth theorem."),
        "source": source_url,
        "tags": ["pi", "asymptotics", "logarithm", "translation count"],
    }
    problem = {"theorem_name": stage.TARGET, **metadata,
               "preamble": preamble, "formal_statement": formal}
    publish = {"problems": [problem], "env": ENV, "private": False}
    verify = {
        "env": ENV, "proof_type": "prove", "target_theorem_name": stage.TARGET,
        "theorem_id": None,
        "theorem_id_binding":
            "exact public theorem name/environment/preamble/formal_statement readback",
        "explanation": (
            "The source-faithful proof derives the normalized polynomial limit from "
            "the original floor-count lemmas and applies the already proved logarithmic "
            "growth theorem; positivity of the limiting constant follows from $v>0$."),
        "file": {"filename": Path(stage.SOLUTION_OUTPUT).name,
                 "source": stage.ws(STAGE / stage.SOLUTION_OUTPUT),
                 "sha256": sha(STAGE / stage.SOLUTION_OUTPUT),
                 "utf8": solution.decode()},
    }
    manifest = {
        "schema_version": 1,
        "artifact_kind": "ap20-log-translation-count-proof-publication-manifest",
        "theorem_name": stage.TARGET, "environment": ENV, "visibility": "public",
        "preamble": preamble, "formal_statement": formal,
        "statement": stage.ws(STAGE / stage.TARGET_OUTPUT),
        "statement_sha256": sha(STAGE / stage.TARGET_OUTPUT),
        "solution": stage.ws(STAGE / stage.SOLUTION_OUTPUT),
        "solution_sha256": sha(STAGE / stage.SOLUTION_OUTPUT),
        "source_commit": prep["source_commit"], "source_units": prep["exact_source_units"],
        "original_AST_units": 4, "original_source_lines": 42,
        "prior_exact_name_lookup_sha256": sha(LOOKUP),
        "published_data_definition_id": prep["published_data_definition_id"],
        "accepted_logdiv_theorem_id": prep["accepted_logdiv_theorem_id"],
        "certificate": stage.ws(CERT), "validated": CERT.is_file(),
        "proposal_status": "Draft", "submission_ready": False,
    }
    return prep, manifest, metadata, publish, verify


def historical(cert):
    artifacts, deps = {}, {}
    for output, data in cert["preflights"].items():
        record = (STAGE / output).with_suffix(".lean.preflight.json")
        need(record.is_file(), "Actual translation preflight record is missing: " + output)
        artifacts[stage.rel(record)] = sha(record)
        need(data["source_unchanged"] is True
             and data["source_sha256_before"] == data["source_sha256_after"] ==
                 sha(resolve(data["source"]))
             and data["manifest_unchanged"] is True
             and data["manifest_sha256_before"] == data["manifest_sha256_after"] ==
                 sha(resolve(data["manifest"]))
             and data["log_sha256"] == data["stdout_and_stderr_sha256"] ==
                 sha(resolve(data["log"])),
             "Historical translation source/manifest/log witness differs")
        for field, key in (("source", "source_sha256_before"),
                           ("manifest", "manifest_sha256_before"),
                           ("log", "log_sha256")):
            artifacts[data[field]] = data[key]
        for dep in data["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"] == sha(Path(dep["path"])),
                 "Historical imported OLean changed")
            deps[dep["path"]] = dep["sha256_before"]
        if data["output_olean"]:
            need(sha(resolve(data["output_olean"])) == data["output_olean_sha256"],
                 "Emitted translation proof OLean changed")
            deps[data["output_olean"]] = data["output_olean_sha256"]
    return dict(sorted(artifacts.items())), dict(sorted(deps.items()))


def prepare():
    need(CERT.is_file(), "Four actual contexts and the derived strict certificate are pending")
    prep, manifest, metadata, publish, verify = static()
    failure_path = STAGE / "publication-preparation-failure-v5.json"
    failure = read(failure_path)
    need(failure["wrapper"] == "scripts/prepare_log_translation_term_count_publication_v5.py"
         and failure["wrapper_sha256"] == sha(
             TASK / "scripts/prepare_log_translation_term_count_publication_v5.py")
         and failure["exit_code"] == 1
         and failure["error"] ==
             "Single complete derived strict replay differs from actual certificate"
         and failure["no_API"] is True and failure["prior_Lean_unchanged"] is True
         and failure["certificate_current_sha256"] == sha(CERT),
         "Preserved v5 serialization-gate failure evidence differs")
    cert = read(CERT)
    replay = consumer.validate()
    need(cert == replay
         and CERT.read_bytes() == certificate_bytes(replay)
         and cert["artifact_kind"] ==
             "ap20-log-translation-count-four-original-AST-validation-v5"
         and cert["validated"] is True and cert["Std3_only"] is True
         and cert["original_AST_units"] == 4 and cert["original_source_lines"] == 42
         and cert["original_proof_suffixes_unchanged"] is True
         and cert["source_and_generated_full_types_equal"] is True
         and cert["source_and_generated_actual_proof_references_paired"] is True
         and cert["references_bitwise_equal_under_actual_mapping"] is False
         and cert["raw_owned_inventory_exact"] is True
         and len(cert["actual_private_helper_mappings"]) == 3
         and cert["published_data_definition_id"] == prep["published_data_definition_id"]
         and cert["accepted_logdiv_theorem_id"] == prep["accepted_logdiv_theorem_id"]
         and cert["published_data_cert_sha256"] == sha(stage.route.CERT)
         and cert["accepted_logdiv_mirror_cert_sha256"] == sha(stage.route.LOGDIV_CERT)
         and cert["frozen_original_consumer_preimage_sha256"] ==
             sha(Path(consumer.preimage.__file__))
         and cert["frozen_v3_consumer_preimage_sha256"] ==
             sha(Path(consumer.imported_boundary.__file__))
         and cert["frozen_v4_consumer_preimage_sha256"] ==
             sha(TASK / "scripts/certify_log_translation_count_node_v4.py"),
         "Parsed v5 certificate or exact Windows serialization differs")
    expected_deltas = {
        name: {"valueRefs": row, "allUsedConstants": row}
        for name, row in consumer.EXTERNAL_INSTANCE_DELTAS.items()
    }
    unused = cert["actual_unused_raw_closed_CIs"]
    caches = unused["unreferenced_proof_caches"]
    need(cert["actual_external_instance_deltas"] == expected_deltas
         and unused["data_equation"]["name"] ==
             "OAI.PiExponent.translationTermCount.eq_1"
         and unused["data_equation"]["published_definition_id"] ==
             prep["published_data_definition_id"]
         and unused["data_equation"]["exact_binders_lhs_and_rhs_equal"] is True
         and unused["data_equation"]["full_def_metadata_sha256"] == sha(
             TASK / "verification/ap19/analytic-remainder-data/generated-full-ci.jsonl")
         and unused["complete_raw_owner_inventory_sha256"] == cert["owned_inventory_sha256"]
         and unused["actual_all_CI_audit_sha256"] == consumer.AUDIT_SHA256 ==
             sha(STAGE / "actual-ci-audit.json")
         and len(caches) == 7
         and all(row["unreferenced_by_four_proof_roots"] is True
                 and row["full_CI"]["closedType"] is True
                 and row["full_CI"]["closedValue"] is True
                 and set(row["full_CI"]["axioms"]) <=
                     {"propext", "Classical.choice", "Quot.sound"}
                 and not any(name.startswith("OAI.") or
                             name.startswith("_private.") and ".OAI." in name
                             for name in row["full_CI"]["allUsedConstants"])
                 for row in caches),
         "Actual finite instance deltas or unused closed-CI inventory differs")
    refs = cert["actual_imported_certified_provider_oleans"]
    need(set(refs) == {"c1_published_data", "c2_published_data", "c2_accepted_logdiv"}
         and all(row["stable_during_compile"] is True
                 and row["sha256_before"] == row["sha256_after"] == sha(Path(row["path"]))
                 for row in refs.values()),
         "Actual certified provider OLean imports differ")
    seconds = [row["seconds"] for row in cert["preflights"].values()]
    need(len(seconds) == 4 and all(0 < value <= 300 for value in seconds)
         and cert["max_file_seconds"] == max(seconds)
         and cert["submission_ready"] is False and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False,
         "Actual translation compiler budget or Draft/pure boundary differs")
    compiler_hashes = {f"c{i}.json": sha(STAGE / f"c{i}.json") for i in range(1, 5)}
    need(cert["compiler_manifest_hashes"] == compiler_hashes,
         "Actual compiler manifest hashes differ")
    artifacts, deps = historical(cert)
    pin_paths = [SELF, ONLINE, API, API_REVIEW, Path(stage.__file__), Path(consumer.__file__),
                 Path(consumer.preimage.__file__), Path(consumer.imported_boundary.__file__),
                 TASK / "scripts/certify_log_translation_count_node_v4.py",
                 TASK / "scripts/prepare_log_translation_term_count_publication_v5.py",
                 TASK / "scripts/publish_log_translation_term_count_node_v5.py",
                 TASK / "scripts/prepare_log_translation_term_count_publication_v6.py",
                 TASK / "scripts/publish_log_translation_term_count_node_v6.py",
                 failure_path,
                 CERT, LOOKUP, STAGE / "preparation.json",
                 STAGE / stage.TARGET_OUTPUT, STAGE / stage.SOLUTION_OUTPUT,
                 STAGE / stage.SOURCE_TYPES, STAGE / stage.GENERATED_TYPES,
                 STAGE / stage.SOURCE_REFS, STAGE / stage.GENERATED_REFS,
                 STAGE / stage.INVENTORY, stage.ROUTE / "route-preparation.json",
                 STAGE / "actual-ci-audit.json",
                 TASK / "verification/ap19/analytic-remainder-data/generated-full-ci.jsonl",
                 stage.route.CERT, stage.route.PUBLISHED, stage.route.LOGDIV_CERT]
    pin_files = {pin_key(path): sha(path) for path in pin_paths}
    pin_files.update(prep["input_hashes"])
    pin_files.update(artifacts)
    pin_files.update(cert["implementation_hashes"])
    for name, expected in {
        stage.SOURCE_TYPES: cert["source_types_sha256"],
        stage.GENERATED_TYPES: cert["generated_types_sha256"],
        stage.SOURCE_REFS: cert["source_refs_sha256"],
        stage.GENERATED_REFS: cert["generated_refs_sha256"],
        stage.INVENTORY: cert["owned_inventory_sha256"],
    }.items():
        need(sha(STAGE / name) == expected, "Actual kernel JSON changed: " + name)
        pin_files[stage.rel(STAGE / name)] = expected
    for row in refs.values():
        deps[row["path"]] = row["sha256_before"]
    payloads = {"publish-payload.json": encode(publish),
                "verification-payload.json": encode(verify)}
    pins = {
        "schema_version": 1,
        "artifact_kind": "ap20-log-translation-count-frozen-publication",
        "theorem_name": stage.TARGET, "environment": ENV, "visibility": "public",
        "offline_wrapper_sha256": sha(SELF), "online_wrapper_sha256": sha(ONLINE),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "validation_sha256": sha(CERT), "manifest_sha256": digest(encode(manifest)),
        "metadata_sha256": digest(encode(metadata)),
        "payload_sha256": {name: digest(raw) for name, raw in payloads.items()},
        "actual_solution_olean_sha256": cert["solution_olean_sha256"],
        "historical_and_input_hashes": dict(sorted(pin_files.items())),
        "historical_dependency_olean_hashes": dict(sorted(deps.items())),
        "actual_max_file_seconds": max(seconds),
        "compiler_manifest_sha256": compiler_hashes,
        "certification_semantics": {
            "validated": True, "Std3_only": True, "closed_global_solution": True,
            "submission_ready": False, "proposal_status": "Draft",
            "Lean_started_by_consumer": False, "API_used": False},
        "one_complete_strict_replay_performed": True,
        "strict_replay_count_in_this_successor": 1,
        "v5_prepare_failure_record_sha256": sha(failure_path),
        "subsequent_HTTP_guards_hash_only": True,
        "proposal_status": "Draft", "submission_ready": False, "API_used": False,
    }
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "metadata.json", encode(metadata))
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "wire-theorem-source.lean", (STAGE / stage.TARGET_OUTPUT).read_bytes())
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False,
            "strict_replay_count_this_successor": 1,
            "theorem_name": stage.TARGET, "proposal_status": "Draft"}


def frozen():
    pins = read(DEST / "preparation.json")
    need(sha(SELF) == pins["offline_wrapper_sha256"]
         and sha(ONLINE) == pins["online_wrapper_sha256"]
         and sha(STAGE / "preparation.json") == pins["stage_preparation_sha256"]
         and sha(CERT) == pins["validation_sha256"],
         "Frozen translation publication implementation changed")
    for path, expected in pins["historical_and_input_hashes"].items():
        need(sha(resolve(path)) == expected, "Frozen translation input changed: " + path)
    for path, expected in pins["historical_dependency_olean_hashes"].items():
        need(sha(Path(path)) == expected, "Frozen translation imported OLean changed: " + path)
    need(all(sha(STAGE / name) == expected
             for name, expected in pins["compiler_manifest_sha256"].items())
         and 0 < pins["actual_max_file_seconds"] <= 300,
         "Frozen actual translation certification semantics changed")
    need(sha(DEST / "manifest.json") == pins["manifest_sha256"]
         and sha(DEST / "metadata.json") == pins["metadata_sha256"]
         and sha(DEST / "validation.json") == pins["validation_sha256"]
         and sha(DEST / "wire-theorem-source.lean") == sha(STAGE / stage.TARGET_OUTPUT)
         and all(sha(DEST / name) == expected
                 for name, expected in pins["payload_sha256"].items()),
         "Frozen translation payload or comparator changed")
    return read(DEST / "manifest.json"), read(DEST / "metadata.json"), {
        name: (DEST / name).read_bytes() for name in pins["payload_sha256"]}, pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--prepare-only", action="store_true")
    group.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        print(json.dumps(prepare(), ensure_ascii=False))
    else:
        frozen()
        print(json.dumps({"checked": True, "network_used": False}, ensure_ascii=False))


if __name__ == "__main__":
    main()




