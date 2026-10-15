"""Prepare AP20's two-layer analytic Open-sketch graph publication offline.

The file is intentionally inert until the genuine eighteen-context certificate
exists.  Final preparation performs one complete strict replay.  Every later
HTTP operation uses only the frozen hashes written here.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import certify_analytic_translated_two_layer_reduction_v3 as consumer
import finalize_analytic_translated_two_layer_reduction_v3 as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_analytic_translated_two_layer_graph_v3.py"
CERT = stage.CERTIFICATE
DEST = STAGE / "publication-v3"
API = ROOT / "scripts/p2m_api.py"
API_REVIEW = stage.V / "api-review-20261011-v0.12.4"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("utf-8")


def resolved(path):
    p = Path(path)
    return p if p.is_absolute() else TASK / p


def exact(path, raw):
    path = Path(path)
    if path.exists():
        need(path.read_bytes() == raw, "Frozen AP20 graph artifact differs: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def theorem_path(name): return STAGE / stage.theorem_file(name)
def solution_path(parent): return STAGE / stage.solution_file(parent)


def split_wire(name, raw, opened):
    marker = ("theorem " + name).encode("utf-8")
    need(raw.count(marker) == 1, "Exact theorem marker differs: " + name)
    at = raw.index(marker)
    preamble, formal = raw[:at].decode("utf-8"), raw[at:].decode("utf-8")
    need(formal.startswith("theorem " + name), "Formal statement name differs: " + name)
    if opened:
        need(formal.endswith(":= by\n  sorry\n") and formal.count("sorry") == 1,
             "New interface is not the exact Open placeholder: " + name)
    return preamble, formal


def problem(name, raw, metadata):
    preamble, formal = split_wire(name, raw, True)
    need(set(metadata) == {"theorem_name", "theorem_title", "natural_language_statement",
                           "source", "tags"}
         and metadata["theorem_name"] == name
         and metadata["source"].startswith("https://github.com/openai/math/blob/" + stage.data.COMMIT),
         "Academic metadata differs: " + name)
    return {"theorem_name": name, "theorem_title": metadata["theorem_title"],
            "natural_language_statement": metadata["natural_language_statement"],
            "preamble": preamble, "formal_statement": formal,
            "source": metadata["source"], "tags": metadata["tags"]}


def static_artifacts():
    plan = read(STAGE / "preparation.json")
    expected_edges = {
        stage.NORM: stage.CHILDREN[stage.NORM] + [stage.route.TRANSLATED],
        stage.ACTUAL: stage.CHILDREN[stage.ACTUAL] + [stage.route.LOGSUM],
    }
    need(plan["artifact_kind"] ==
             "ap20-analytic-translated-two-layer-finite-metadata-recursion-successor-final-preparation"
         and plan["new_analytic_names"] == stage.NEW_NAMES
         and plan["new_analytic_name_count"] == 11
         and plan["graph_children"] == stage.CHILDREN
         and plan["existing_actual_parent_id"] == stage.ACTUAL_ID
         and plan["parent_wire_unchanged"] is True
         and plan["Open_sketch_only"] is True and plan["closed_proof"] is False
         and plan["generated_Std3_only"] is False
         and plan["local_placeholder_sorryAx_expected"] is True
         and plan["boundary"]["data_definition_id"] ==
             "20a36293-ad9b-41de-b2a1-463e0f7f0094"
         and plan["boundary"]["data_certificate_sha256"] ==
             "d6971119f345b9172eb0368c80d9b65f39ce797c24fe5b2da16beea33aaeef4c"
         and plan["reused_context_count"] == 15
         and plan["new_bounded_context_count"] == 3
         and len(plan["reused_actual_contexts"]) == 15
         and plan["multiplicity_binding"]["definition_id"] ==
             "9e7cfb76-3480-4078-b240-661c13a8f231"
         and plan["multiplicity_binding"]["provided_names"] ==
             [stage.MISSING_CI]
         and plan["multiplicity_binding"]["Std3_only"] is True
         and plan["full14_source_type_import_closure_audit_sha256"] ==
             sha(STAGE / "type-import-closure-audit.json")
         and plan["only_comparator_math_change"] ==
             "none; one exact actual Published Definition import added to norm_choiceMatrix_le preamble"
         and plan["original_parent_proof_bytes_unchanged"] is True
         and plan["finite_metadata_maxRecDepth"] == 100000
         and set(plan["metadata_only_changes"]) == {
             stage.SOURCE_SNAPSHOT, *stage.GENERATED_SNAPSHOTS.values()}
         and all(row["maxRecDepth"] == 100000
                 and row["only_changes"] ==
                     "finite maxRecDepth option and IO output directory; all mathematical declarations unchanged"
                 for row in plan["metadata_only_changes"].values())
         and plan["prior_failed_c16_preserved"]["reason"] ==
             "maximum recursion depth reached in metadata #eval; source axioms outputs remain Std3"
         and plan["mathematical_proof_and_interface_bytes_unchanged"] is True
         and plan["validated"] is False and plan["submission_ready"] is False
         and plan["proposal_status"] == "Draft",
         "Final two-layer Open-sketch preparation differs")

    problems, nodes = [], []
    for name in stage.NEW_NAMES:
        raw = theorem_path(name).read_bytes()
        interface = plan["wire_interfaces"][name]
        need(raw == (interface["preamble"] + interface["formal_statement"]).encode("utf-8")
             and interface["local_role"] == "Open interface placeholder, not a closed proof",
             "Exact staged Open wire differs: " + name)
        row = problem(name, raw, plan["academic_metadata"][name])
        problems.append(row)
        nodes.append({"name": name, "module": stage.theorem_module(name),
                      "wire": stage.rel(theorem_path(name)), "wire_sha256": sha_bytes(raw),
                      "status": "Open", "closed_proof": False})

    norm_batch = [stage.NORM] + stage.CHILDREN[stage.NORM]
    actual_batch = [n for n in stage.CHILDREN[stage.ACTUAL] if n != stage.NORM]
    need(len(norm_batch) == 8 and len(actual_batch) == 3
         and norm_batch[0] == stage.NORM
         and norm_batch[1:] == stage.CHILDREN[stage.NORM]
         and actual_batch == [n for n in stage.CHILDREN[stage.ACTUAL] if n != stage.NORM]
         and len(set(norm_batch) | set(actual_batch)) == 11
         and set(norm_batch).isdisjoint(actual_batch)
         and set(norm_batch) | set(actual_batch) == set(stage.NEW_NAMES),
         "Required two publication batches differ")
    by_name = {row["theorem_name"]: row for row in problems}
    publish_payloads = {
        "publish-norm-batch.json": {"problems": [by_name[n] for n in norm_batch],
                                    "env": ENV, "private": False},
        "publish-actual-siblings-batch.json": {"problems": [by_name[n] for n in actual_batch],
                                               "env": ENV, "private": False},
    }

    parent_wires = {}
    actual_raw = (STAGE / "parent-existing-wire.lean").read_bytes()
    actual_preamble, actual_formal = split_wire(stage.ACTUAL, actual_raw, True)
    need(sha_bytes(actual_raw) == plan["parent_existing_wire_sha256"],
         "Existing actual-minor parent wire changed")
    parent_wires[stage.ACTUAL] = {"theorem_id": stage.ACTUAL_ID,
                                  "preamble": actual_preamble,
                                  "formal_statement": actual_formal,
                                  "wire_sha256": sha_bytes(actual_raw)}
    norm_row = by_name[stage.NORM]
    parent_wires[stage.NORM] = {"theorem_id": None,
                                "preamble": norm_row["preamble"],
                                "formal_statement": norm_row["formal_statement"],
                                "wire_sha256": sha(theorem_path(stage.NORM))}

    explanations = {
        stage.NORM: ("This source-faithful sketch applies the original seven immediate "
                     "literal-interface children and the already Proved translated-summand "
                     "bound. The local children are typed Open placeholders, so the result "
                     "is a SKETCH_ACCEPTED decomposition, not a closed proof."),
        stage.ACTUAL: ("This source-faithful sketch applies the three original analytic "
                       "siblings, the newly sketched norm-actual-summand interface, and the "
                       "already Proved logarithmic-sum bound. Open children remain, so this "
                       "is a SKETCH_ACCEPTED decomposition, not a closed proof."),
    }
    verify_payloads = {}
    for parent in (stage.NORM, stage.ACTUAL):
        sol = solution_path(parent)
        raw = sol.read_bytes()
        need(raw.count(b"theorem solution") == 1 and b"sorry" not in raw
             and ("import " + stage.theorem_module(parent)).encode("utf-8") not in raw,
             "Global sketch solution imports its target or contains sorry: " + parent)
        verify_payloads["verify-norm.json" if parent == stage.NORM else "verify-actual.json"] = {
            "target_theorem_name": parent,
            "theorem_id": parent_wires[parent]["theorem_id"],
            "theorem_id_binding": "exact public name/environment/preamble/formal_statement readback",
            "proof_type": "prove", "explanation": explanations[parent],
            "file": {"filename": Path(stage.solution_file(parent)).name,
                     "source": stage.rel(sol), "sha256": sha(sol),
                     "utf8": raw.decode("utf-8")},
        }

    boundary_nodes = {}
    for name in stage.ACCEPTED:
        raw = theorem_path(name).read_bytes()
        preamble, formal = split_wire(name, raw, False)
        witness = plan["server_Proved_children"][name]
        boundary_nodes[name] = {"theorem_id": witness["theorem_id"],
                                "proof_id": witness["proof_id"],
                                "preamble": preamble, "formal_statement": formal,
                                "wire_sha256": sha_bytes(raw),
                                "publication_record": witness["publication_record"],
                                "publication_record_sha256": witness["publication_record_sha256"],
                                "expected_status": "Proved"}

    payloads = {name: json.dumps(value, ensure_ascii=False).encode("utf-8")
                for name, value in publish_payloads.items()}
    payloads.update({name: encode(value) for name, value in verify_payloads.items()})
    manifest = {"schema_version": 1,
        "artifact_kind": "ap20-analytic-translated-two-layer-graph-publication-manifest",
        "environment": ENV, "visibility": "public", "new_nodes": nodes,
        "new_node_names": stage.NEW_NAMES, "norm_batch_names": norm_batch,
        "actual_batch_names": actual_batch, "parent_wires": parent_wires,
        "boundary_nodes": boundary_nodes, "expected_graph_edges": expected_edges,
        "publication_sequence": ["publish norm plus seven norm children",
                                 "verify norm sketch",
                                 "publish three actual-minor siblings",
                                 "verify existing actual-minor sketch"],
        "expected_verify_status": "SKETCH_ACCEPTED", "Open_sketch_only": True,
        "closed_proof": False, "count_as_own_Accepted_proof": False,
        "creates_campaign_proposal": False, "proposal_status": "Draft"}
    return plan, manifest, payloads


def replay_certificate(cert):
    actual = consumer.validate()
    expected_edges = {
        stage.NORM: stage.CHILDREN[stage.NORM] + [stage.route.TRANSLATED],
        stage.ACTUAL: stage.CHILDREN[stage.ACTUAL] + [stage.route.LOGSUM],
    }
    need(stage.encode(actual) == CERT.read_bytes() and actual == cert
         and cert["artifact_kind"] ==
             "ap20-analytic-translated-two-layer-actual-Open-sketch-validation-v3"
         and cert["validated"] is True and cert["Open_sketch_only"] is True
         and cert["closed_proof"] is False and cert["source_Std3_only"] is True
         and cert["generated_Std3_only"] is False
         and cert["local_placeholder_sorryAx_expected"] is True
         and cert["existing_actual_parent_id"] == stage.ACTUAL_ID
         and cert["new_analytic_names"] == stage.NEW_NAMES
         and cert["new_analytic_name_count"] == 11
         and cert["expected_graph_edges"] == expected_edges
         and cert["boundary"] == read(STAGE / "preparation.json")["boundary"]
         and cert["reused_actual_context_count"] == 15
         and cert["new_actual_context_count"] == 3
         and cert["prior_failed_c11_preserved"] ==
             read(STAGE / "preparation.json")["legacy_failure"]
         and cert["prior_failed_c16_preserved"] ==
             read(STAGE / "preparation.json")["prior_failed_c16_preserved"]
         and cert["finite_metadata_maxRecDepth"] == 100000
         and cert["metadata_only_changes"] ==
             read(STAGE / "preparation.json")["metadata_only_changes"]
         and cert["mathematical_proof_and_interface_bytes_unchanged"] is True
         and cert["multiplicity_binding"] ==
             read(STAGE / "preparation.json")["multiplicity_binding"]
         and cert["all14_source_types_have_complete_Published_data_import_closure"] is True
         and cert["source_type_import_closure_audit_sha256"] ==
             sha(STAGE / "type-import-closure-audit.json")
         and cert["original_parent_proof_bytes_unchanged"] is True
         and cert["legacy_frozen_consumer_sha256"] ==
             sha(TASK / cert["legacy_frozen_consumer"])
         and set(cert["parent_reports"]) == {stage.NORM, stage.ACTUAL}
         and all(row["source_generated_complete_type_equal"] is True
                 and row["generated_Std3_only"] is False
                 and row["local_sorryAx_expected"] is True
                 and row["closed_proof"] is False
                 for row in cert["parent_reports"].values())
         and cert["all_source_generated_full_kernel_interface_types_equal"] is True
         and set(cert["actual_owned_CI_names"]) == {stage.NORM, stage.ACTUAL}
         and all(row["full_type_equal"] is True and row["actual_closed_Prop"] is True
                 for row in cert["actual_typed_auxiliary_Prop_pairs"])
         and all(row["actual_closed_Prop"] is True
                 and row["unused_by_all_raw_owned_CIs"] is True
                 for row in cert["actual_unused_external_only_Prop_CIs"])
         and 0 < cert["max_file_seconds"] <= 300
         and cert["submission_ready"] is False and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False,
         "One genuine complete two-layer strict replay differs")


def historical(cert):
    artifacts, oleans = {}, {}
    for witness in cert["preflights"].values():
        data = witness["data"]
        need(sha(resolved(witness["record"])) == witness["record_sha256"],
             "Actual preflight record changed")
        need(data["source_unchanged"] is True
             and data["source_sha256_before"] == data["source_sha256_after"] ==
                 sha(resolved(data["source"]))
             and data["manifest_unchanged"] is True
             and data["manifest_sha256_before"] == data["manifest_sha256_after"] ==
                 sha(resolved(data["manifest"]))
             and data["log_sha256"] == data["stdout_and_stderr_sha256"] ==
                 sha(resolved(data["log"])),
             "Historical source/manifest/log before-after evidence differs")
        artifacts[witness["record"]] = witness["record_sha256"]
        artifacts[data["source"]] = data["source_sha256_before"]
        artifacts[data["manifest"]] = data["manifest_sha256_before"]
        artifacts[data["log"]] = data["log_sha256"]
        for dep in data["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"] == sha(Path(dep["path"])),
                 "Actual imported OLean changed")
            oleans[dep["path"]] = dep["sha256_before"]
    for row in cert["emitted_oleans"].values():
        need(sha(resolved(row["path"])) == row["sha256"], "Actual emitted OLean changed")
        oleans[row["path"]] = row["sha256"]
    return dict(sorted(artifacts.items())), dict(sorted(oleans.items()))


def api_review():
    review = read(API_REVIEW / "manifest.json")
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and all(sha(API_REVIEW / name) == value for name, value in docs.items()),
         "Reviewed official API documentation changed")
    return {"official_tag": review["official_tag"],
            "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW / "manifest.json"), "documents": docs}


def prepare():
    need(CERT.is_file(), "Actual eighteen-context strict sketch certificate is pending")
    cert = read(CERT)
    replay_certificate(cert)
    plan, manifest, payloads = static_artifacts()
    artifacts, oleans = historical(cert)
    direct = {stage.rel(p): sha(p) for p in [SELF, ONLINE, Path(stage.__file__),
        Path(consumer.__file__),
        TASK / "scripts/prepare_analytic_translated_two_layer_publication_v2.py",
        TASK / "scripts/publish_analytic_translated_two_layer_graph_v2.py",
        STAGE / "preparation.json", STAGE / "compile-commands.txt", CERT]}
    direct[str(API)] = sha(API)
    direct.update(plan["input_hashes"])
    direct.update(cert["implementation_hashes"])
    direct.update(cert["output_json_sha256"])
    direct.update(artifacts)
    for name, row in plan["files"].items():
        direct[stage.rel(STAGE / name)] = row["sha256"]
        manifest_path = (TASK / plan["reused_actual_contexts"][name]["manifest"]
                         if row.get("actual_context_reused") is True
                         else STAGE / row["manifest"])
        direct[stage.rel(manifest_path)] = sha(manifest_path)
    for name, row in manifest["boundary_nodes"].items():
        direct[row["publication_record"]] = row["publication_record_sha256"]
    for path, expected in direct.items():
        need(sha(resolved(path)) == expected, "Frozen graph input differs: " + path)
    for path, expected in plan["external_dependency_olean_hashes"].items():
        need(sha(Path(path)) == expected, "Frozen external OLean differs: " + path)

    all_oleans = dict(plan["external_dependency_olean_hashes"])
    for path, expected in oleans.items():
        need(path not in all_oleans or all_oleans[path] == expected,
             "Conflicting frozen OLean hashes: " + path)
        all_oleans[path] = expected
    pins = {"schema_version": 1,
        "artifact_kind": "ap20-analytic-translated-two-layer-graph-publication-preparation",
        "environment": ENV, "visibility": "public",
        "new_node_names": stage.NEW_NAMES,
        "norm_batch_names": manifest["norm_batch_names"],
        "actual_batch_names": manifest["actual_batch_names"],
        "existing_actual_parent_id": stage.ACTUAL_ID,
        "offline_wrapper_sha256": sha(SELF), "online_wrapper_sha256": sha(ONLINE),
        "api_client_sha256": sha(API), "finalizer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "validation_sha256": sha(CERT), "manifest_sha256": sha_bytes(encode(manifest)),
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "frozen_input_hashes": dict(sorted(direct.items())),
        "external_and_actual_olean_hashes": dict(sorted(all_oleans.items())),
        "actual_max_file_seconds": cert["max_file_seconds"],
        "expected_graph_edges": cert["expected_graph_edges"],
        "official_api_review": api_review(),
        "one_complete_strict_replay_performed": True,
        "subsequent_HTTP_guards_hash_only": True,
        "durable_policy": "write every POST intent first; never repeat uncertain POST; poll only known ids",
        "Open_sketch_only": True, "closed_proof": False,
        "count_as_own_Accepted_proof": False, "creates_campaign_proposal": False,
        "API_used": False, "submission_ready": False, "proposal_status": "Draft"}
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    for name, raw in payloads.items(): exact(DEST / name, raw)
    for name in stage.NEW_NAMES:
        exact(DEST / "node-wires" / (name.rsplit(".", 1)[1] + ".lean"),
              theorem_path(name).read_bytes())
    exact(DEST / "parent-existing-wire.lean", (STAGE / "parent-existing-wire.lean").read_bytes())
    for parent in (stage.NORM, stage.ACTUAL):
        exact(DEST / ("solution-" + ("norm" if parent == stage.NORM else "actual") + ".lean"),
              solution_path(parent).read_bytes())
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "strict_replay_count": 1,
            "new_nodes": 11, "Open_sketch_only": True, "closed_proof": False,
            "payload_sha256": pins["payload_sha256"], "proposal_status": "Draft"}


def hash_gate(pins):
    need(sha(SELF) == pins["offline_wrapper_sha256"]
         and sha(ONLINE) == pins["online_wrapper_sha256"]
         and sha(API) == pins["api_client_sha256"]
         and sha(Path(stage.__file__)) == pins["finalizer_sha256"]
         and sha(Path(consumer.__file__)) == pins["strict_consumer_sha256"]
         and sha(STAGE / "preparation.json") == pins["stage_preparation_sha256"]
         and sha(CERT) == pins["validation_sha256"],
         "Frozen graph implementation/certificate changed")
    for path, expected in pins["frozen_input_hashes"].items():
        need(sha(resolved(path)) == expected, "Frozen graph input changed: " + path)
    for path, expected in pins["external_and_actual_olean_hashes"].items():
        need(sha(Path(path) if Path(path).is_absolute() else resolved(path)) == expected,
             "Frozen graph OLean changed: " + path)
    need((DEST / "preparation.json").read_bytes() == encode(pins)
         and sha(DEST / "manifest.json") == pins["manifest_sha256"]
         and sha(DEST / "validation.json") == pins["validation_sha256"]
         and all(sha(DEST / name) == expected for name, expected in pins["payload_sha256"].items())
         and api_review() == pins["official_api_review"],
         "Frozen graph payload/API review changed")
    manifest = read(DEST / "manifest.json")
    for row in manifest["new_nodes"]:
        need(sha(DEST / "node-wires" / (row["name"].rsplit(".", 1)[1] + ".lean")) == row["wire_sha256"],
             "Frozen node wire changed: " + row["name"])
    need(sha(DEST / "parent-existing-wire.lean") == manifest["parent_wires"][stage.ACTUAL]["wire_sha256"],
         "Frozen existing parent wire changed")
    for key in ("norm", "actual"):
        verify = read(DEST / ("verify-" + key + ".json"))
        need(sha(DEST / ("solution-" + key + ".lean")) == verify["file"]["sha256"],
             "Frozen sketch solution copy changed: " + key)


def frozen():
    pins = read(DEST / "preparation.json")
    hash_gate(pins)
    payloads = {name: (DEST / name).read_bytes() for name in pins["payload_sha256"]}
    return read(DEST / "manifest.json"), payloads, pins


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        result = prepare()
    else:
        frozen()
        result = {"checked": True, "network_used": False,
                  "strict_replay_reused_by_hash": True,
                  "Open_sketch_only": True, "closed_proof": False,
                  "proposal_status": "Draft"}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()


