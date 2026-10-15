"""Prepare AP19's two Open analytic children and existing-parent sketch offline.

Final preparation binds the genuine v2 five-context interface certificate and
the already Published four-definition provider.  The strict v2 consumer has
already performed the one complete replay; this successor checks its exact
certificate bytes and uses frozen hashes for all later network calls.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

import certify_analytic_aggregate_two_child_reduction_v2 as consumer
import finalize_analytic_aggregate_two_child_reduction as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
CERT = consumer.CERT
DEST = STAGE / "publication-v3"
SELF = Path(__file__).resolve()
ONLINE = TASK / "scripts/publish_analytic_aggregate_two_child_graph_v2.py"
API = ROOT / "scripts/p2m_api.py"
API_REVIEW = TASK / "verification/api-review-20261011-v0.12.4"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True,
                       separators=(",", ":")) + "\n").encode("utf-8")


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen AP19 analytic publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def resolved(path):
    p = Path(path)
    return p if p.is_absolute() else TASK / p


def child_file(name):
    return STAGE / (stage.candidate.theorem_module(name).replace(".", "/") + ".lean")


def split_wire(name, raw):
    marker = ("theorem " + name).encode("utf-8")
    need(raw.count(marker) == 1, "AP19 child wire lacks one exact theorem marker: " + name)
    at = raw.index(marker)
    preamble, formal = raw[:at].decode("utf-8"), raw[at:].decode("utf-8")
    need(formal.startswith("theorem " + name)
         and formal.endswith(":= by\n  sorry\n")
         and formal.count("sorry") == 1,
         "AP19 child formal statement is not the exact Open placeholder: " + name)
    return preamble, formal


def static_artifacts():
    plan = read(STAGE / "preparation.json")
    names = [n for n, *_ in stage.candidate.CHILDREN]
    need(plan["artifact_kind"] ==
             "ap19-analyticAggregate-two-child-Open-sketch-final-preparation"
         and plan["parent_existing_theorem_id"] == stage.candidate.PARENT_ID
         and plan["parent_platform_name"] == stage.candidate.PARENT
         and plan["parent_wire_unchanged"] is True
         and plan["child_names"] == names
         and plan["child_sorry_placeholders"] is True
         and plan["child_closed_proofs"] is False
         and plan["Open_child_sorryAx_expected"] is True
         and plan["closed_proof"] is False
         and plan["validated"] is False and plan["submission_ready"] is False,
         "AP19 final Open-sketch preparation differs")
    problems, children = [], []
    for name in names:
        raw = child_file(name).read_bytes()
        preamble, formal = split_wire(name, raw)
        key = name.rsplit(".", 1)[1]
        metadata_path = stage.CANDIDATE / "children" / key / "academic-metadata.json"
        metadata = read(metadata_path)
        need(set(metadata) == {"title", "statement", "tags", "source_commit", "source_url"}
             and metadata["source_commit"] == stage.candidate.COMMIT
             and isinstance(metadata["statement"], str) and metadata["statement"],
             "AP19 child academic metadata differs: " + name)
        problem = {"theorem_name": name, "theorem_title": metadata["title"],
                   "preamble": preamble, "formal_statement": formal,
                   "natural_language_statement": metadata["statement"],
                   "source": metadata["source_url"], "tags": metadata["tags"]}
        problems.append(problem)
        children.append({"name": name,
                         "module": stage.candidate.theorem_module(name),
                         "wire": stage.rel(child_file(name)),
                         "wire_sha256": sha_bytes(raw),
                         "metadata": stage.rel(metadata_path),
                         "metadata_sha256": sha(metadata_path),
                         "status": "Open", "closed_proof": False})
    publish = {"problems": problems, "env": ENV, "private": False}
    publish_raw = json.dumps(publish, ensure_ascii=False).encode("utf-8")

    parent_wire = (STAGE / "parent-existing-wire.lean").read_bytes()
    parent_marker = ("theorem " + stage.candidate.PARENT).encode("utf-8")
    need(parent_wire.count(parent_marker) == 1, "AP19 existing parent wire differs")
    parent_at = parent_wire.index(parent_marker)
    parent_preamble = parent_wire[:parent_at].decode("utf-8")
    parent_formal = parent_wire[parent_at:].decode("utf-8")
    need(sha_bytes(parent_wire) == plan["parent_existing_wire_sha256"]
         and parent_formal.endswith(":= by\n  sorry\n"),
         "AP19 existing parent comparator bytes differ")
    solution = STAGE / stage.candidate.SOLUTION_FILE
    solution_raw = solution.read_bytes()
    need(b"theorem solution" in solution_raw and b"sorry" not in solution_raw
         and stage.candidate.PARENT.encode("utf-8") not in solution_raw
         and ("Theorems.Thm_" + stage.candidate.PARENT.replace(".", "_")).encode("utf-8")
             not in solution_raw,
         "AP19 parent sketch is not the target-independent original six-line reduction")
    explanation = (
        "This is the source-faithful two-step analytic reduction. The first Open child "
        "is the original theorem that the analytic remainder tends to zero. The second "
        "Open child is the original selected-minor logarithmic bound. The unchanged "
        "six-line source proof combines them to establish the existing analytic aggregate "
        "interface. Both children remain Open, so this verification is a SKETCH_ACCEPTED "
        "decomposition rather than a closed proof."
    )
    verify = {"theorem_id": stage.candidate.PARENT_ID, "proof_type": "prove",
              "explanation": explanation,
              "file": {"filename": Path(stage.candidate.SOLUTION_FILE).name,
                       "source": stage.rel(solution), "sha256": sha(solution),
                       "utf8": solution_raw.decode("utf-8")}}
    spec = importlib.util.spec_from_file_location("p2m_ap19_analytic_offline", API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    multipart, ctype = api._multipart(
        {"theorem_id": verify["theorem_id"], "proof_type": verify["proof_type"],
         "explanation": verify["explanation"]},
        {"file": (verify["file"]["filename"], solution_raw)})
    payloads = {"publish-payload.json": publish_raw,
                "verification-payload.json": encode(verify),
                "verification-request.multipart": multipart}
    manifest = {"schema_version": 1,
        "artifact_kind": "ap19-analyticAggregate-two-child-publication-manifest",
        "parent_theorem_id": stage.candidate.PARENT_ID,
        "parent_theorem_name": stage.candidate.PARENT,
        "parent_preamble": parent_preamble, "parent_formal_statement": parent_formal,
        "parent_wire_sha256": sha_bytes(parent_wire), "child_nodes": children,
        "environment": ENV, "visibility": "public",
        "publish_route": "/submit-problem", "verify_route": "/verify",
        "expected_verify_status": "SKETCH_ACCEPTED",
        "Open_sketch": True, "closed_proof": False,
        "creates_campaign_proposal": False, "proposal_status": "Draft"}
    return plan, publish, verify, payloads, ctype, manifest


def replay(cert):
    need(stage.encode(cert) == CERT.read_bytes(),
         "AP19 actual v2 Open-sketch certificate encoding differs")
    names = [n for n, *_ in stage.candidate.CHILDREN]
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] ==
             "ap19-analyticAggregate-two-child-actual-Open-sketch-validation"
         and cert["validated"] is True and cert["source_Std3_only"] is True
         and cert["generated_sorryAx_from_exactly_two_Open_child_interfaces"] is True
         and cert["generated_Std3_only"] is False
         and cert["closed_proof"] is False and cert["Open_sketch_only"] is True
         and cert["submission_ready"] is False and cert["proposal_status"] == "Draft"
         and cert["parent_existing_theorem_id"] == stage.candidate.PARENT_ID
         and cert["parent_existing_wire_sha256"] == sha(STAGE / "parent-existing-wire.lean")
         and cert["child_names"] == names
         and cert["child_comparator_status"] == "Open placeholders, not proofs"
         and cert["source_generated_full_kernel_types_equal"] is True
         and cert["source_generated_project_proof_refs_equal"] is False
         and cert["source_generated_project_proof_refs_equal_after_one_certified_closed_Prop_pair"] is True
         and all(name in cert["generated_solution_project_valueRefs"] for name in names)
         and cert["actual_owned_CI_names"] == sorted(names + ["solution"])
         and 0 < cert["max_file_seconds"] <= 300
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False,
         "AP19 actual Open-sketch type/reference/axiom/budget contract differs")
    pair = cert["certified_closed_Prop_helper_pair"]
    need(pair == {
             "source_name": "OAI.PiExponent.DeterminantContradiction.collisionConstant._proof_1",
             "generated_name": "OAI.PiExponent.DeterminantContradiction.GlobalInterpolationStatement._proof_1",
             "actual_closed_propositional_types_equal": True,
             "actual_full_proof_values_equal": True}
         and cert["certified_closed_Prop_helper_pair_certificate"] ==
             "verification/ap10/determinant/actual-provider-validation-helper-v2.json"
         and cert["certified_closed_Prop_helper_pair_certificate_sha256"] ==
             "d17d1a485e9b7310e16741d70f6ac0cd4b5a37fbfd4c2913a1b58cfb0f98a30e"
         and len(cert["source_parent_project_valueRefs"]) == 25
         and len(cert["generated_solution_project_valueRefs"]) == 25
         and sorted(set(cert["source_parent_project_valueRefs"]) -
                    set(cert["generated_solution_project_valueRefs"])) == [pair["source_name"]]
         and sorted(set(cert["generated_solution_project_valueRefs"]) -
                    set(cert["source_parent_project_valueRefs"])) == [pair["generated_name"]],
         "AP19 certified closed-Prop helper reference boundary differs")
    for axioms in cert["axioms"]["source"].values():
        need(set(axioms) <= STD3 and "sorryAx" not in axioms,
             "AP19 original source theorem is not Std3-only")
    for axioms in cert["axioms"]["generated"].values():
        need("sorryAx" in axioms and set(axioms) <= STD3 | {"sorryAx"},
             "AP19 generated Open interface has an unexpected axiom")


def preflight_hashes(cert):
    found = {}
    for row in cert["preflights"].values():
        found[row["record"]] = row["record_sha256"]
        for key in ("source", "manifest", "log"):
            path = consumer.context.file(row["data"][key])
            found[str(path)] = sha(path)
    return dict(sorted(found.items()))


def dependency_oleans(cert):
    found = {}
    for row in cert["preflights"].values():
        for dep in row["data"]["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"],
                 "AP19 imported OLean changed during an actual context")
            found[dep["path"]] = dep["sha256_before"]
    for row in cert["emitted_oleans"].values():
        found[str((TASK / row["path"]).resolve())] = row["sha256"]
    return dict(sorted(found.items()))


def certified_helper_evidence_hashes(cert):
    helper_path = resolved(cert["certified_closed_Prop_helper_pair_certificate"])
    need(sha(helper_path) == cert["certified_closed_Prop_helper_pair_certificate_sha256"],
         "AP19 certified helper certificate changed")
    helper = read(helper_path)
    found = {str(helper_path): sha(helper_path)}

    def add(path, expected):
        key = str(path)
        need(key not in found or found[key] == expected,
             "AP19 certified helper evidence has conflicting hashes: " + key)
        need(sha(resolved(path)) == expected,
             "AP19 certified helper evidence changed: " + key)
        found[key] = expected

    for collection in (helper["output_json_sha256"], helper["implementation_hashes"]):
        for path, expected in collection.items():
            add(path, expected)
    witnesses = list(helper["preflights"].values())
    witnesses += [helper["certified_actual_helper_pair"]["actual_witnesses"][side]["preflight"]
                  for side in ("source", "generated")]
    for witness in witnesses:
        add(witness["record"], witness["record_sha256"])
        for key in ("source", "manifest", "log"):
            add(witness["data"][key], sha(resolved(witness["data"][key])))
        for dep in witness["data"]["dependency_oleans"]:
            need(dep["stable_during_compile"] is True
                 and dep["sha256_before"] == dep["sha256_after"],
                 "AP19 certified helper dependency OLean was unstable")
            add(dep["path"], dep["sha256_before"])
    for side in ("source", "generated"):
        row = helper["certified_actual_helper_pair"]["actual_witnesses"][side]
        add(row["output"], row["output_sha256"])
    return dict(sorted(found.items()))


def api_review():
    review = read(API_REVIEW / "manifest.json")
    docs = {row["name"]: row["sha256"] for row in review["documents"]}
    need(review["official_tag"] == "v0.12.4"
         and review["official_commit"] == "78989800ba0b3149ee34205257025bd0f617e8ef"
         and all(sha(API_REVIEW / name) == expected for name, expected in docs.items()),
         "AP19 reviewed official API documents differ")
    return {"official_tag": review["official_tag"],
            "official_commit": review["official_commit"],
            "manifest_sha256": sha(API_REVIEW / "manifest.json"), "documents": docs}


def prepare():
    need(CERT.is_file(), "AP19 genuine five-context Open-sketch certificate is pending")
    cert = read(CERT)
    replay(cert)
    plan, publish, verify, payloads, ctype, manifest = static_artifacts()
    pins = {"schema_version": 1,
        "artifact_kind": "ap19-analyticAggregate-two-child-publication-preparation-v2",
        "parent_theorem_id": stage.candidate.PARENT_ID,
        "parent_theorem_name": stage.candidate.PARENT,
        "child_names": [n for n, *_ in stage.candidate.CHILDREN],
        "environment": ENV, "visibility": "public",
        "offline_wrapper_sha256": sha(SELF), "online_wrapper_sha256": sha(ONLINE),
        "api_client_sha256": sha(API),
        "candidate_producer_sha256": sha(Path(stage.candidate.__file__)),
        "finalizer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "validation_sha256": sha(CERT),
        "manifest_sha256": sha_bytes(encode(manifest)),
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "multipart_content_type": ctype,
        "stage_input_hashes": plan["input_hashes"],
        "compiler_manifest_sha256": cert["compiler_manifest_sha256"],
        "preflight_artifact_sha256": preflight_hashes(cert),
        "dependency_and_emitted_olean_sha256": dependency_oleans(cert),
        "certified_helper_evidence_sha256": certified_helper_evidence_hashes(cert),
        "implementation_hashes": cert["implementation_hashes"],
        "snapshot_json_sha256": cert["output_json_sha256"],
        "provider_boundary": cert["boundary"],
        "source_parent_project_valueRefs": cert["source_parent_project_valueRefs"],
        "generated_solution_project_valueRefs": cert["generated_solution_project_valueRefs"],
        "official_api_review": api_review(),
        "one_complete_strict_replay_already_performed_by_v2_consumer": True,
        "subsequent_HTTP_guards_are_hash_only": True,
        "publish_route": "/submit-problem", "verify_route": "/verify",
        "expected_verify_status": "SKETCH_ACCEPTED",
        "durable_policy": "write intent before each POST; never repeat an uncertain POST; poll only known ids",
        "Open_sketch": True, "closed_proof": False,
        "creates_campaign_proposal": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft"}
    exact(DEST / "manifest.json", encode(manifest))
    exact(DEST / "validation.json", CERT.read_bytes())
    for name, raw in payloads.items():
        exact(DEST / name, raw)
    for name in pins["child_names"]:
        exact(DEST / "child-wires" / (name.rsplit(".", 1)[1] + ".lean"),
              child_file(name).read_bytes())
    exact(DEST / "parent-existing-wire.lean", (STAGE / "parent-existing-wire.lean").read_bytes())
    exact(DEST / "parent-solution.lean", (STAGE / stage.candidate.SOLUTION_FILE).read_bytes())
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False,
            "one_complete_strict_replay_already_performed_by_v2_consumer": True,
            "Open_sketch": True, "closed_proof": False,
            "payload_sha256": pins["payload_sha256"], "proposal_status": "Draft"}


def hash_gate(pins):
    direct = {SELF: pins["offline_wrapper_sha256"], ONLINE: pins["online_wrapper_sha256"],
              API: pins["api_client_sha256"],
              Path(stage.candidate.__file__): pins["candidate_producer_sha256"],
              Path(stage.__file__): pins["finalizer_sha256"],
              Path(consumer.__file__): pins["strict_consumer_sha256"],
              STAGE / "preparation.json": pins["stage_preparation_sha256"],
              CERT: pins["validation_sha256"]}
    for path, expected in direct.items():
        need(sha(path) == expected, "AP19 frozen implementation/evidence changed: " + str(path))
    for collection in (pins["stage_input_hashes"], pins["implementation_hashes"],
                       pins["snapshot_json_sha256"]):
        for path, expected in collection.items():
            need(sha(resolved(path)) == expected, "AP19 frozen input changed: " + path)
    for name, expected in pins["compiler_manifest_sha256"].items():
        need(sha(STAGE / name) == expected, "AP19 compiler manifest changed: " + name)
    for path, expected in pins["preflight_artifact_sha256"].items():
        need(sha(resolved(path)) == expected, "AP19 preflight artifact changed: " + path)
    for path, expected in pins["dependency_and_emitted_olean_sha256"].items():
        need(sha(resolved(path)) == expected, "AP19 imported/emitted OLean changed: " + path)
    for path, expected in pins["certified_helper_evidence_sha256"].items():
        need(sha(resolved(path)) == expected, "AP19 certified helper evidence changed: " + path)
    need((DEST / "preparation.json").read_bytes() == encode(pins)
         and sha(DEST / "manifest.json") == pins["manifest_sha256"]
         and sha(DEST / "validation.json") == pins["validation_sha256"]
         and all(sha(DEST / name) == expected
                 for name, expected in pins["payload_sha256"].items()),
         "AP19 frozen publication artifacts changed")
    manifest = read(DEST / "manifest.json")
    for row in manifest["child_nodes"]:
        need(sha(DEST / "child-wires" / (row["name"].rsplit(".", 1)[1] + ".lean")) ==
                 row["wire_sha256"], "AP19 frozen child wire changed: " + row["name"])
    need(sha(DEST / "parent-existing-wire.lean") == manifest["parent_wire_sha256"]
         and sha(DEST / "parent-solution.lean") ==
             read(DEST / "verification-payload.json")["file"]["sha256"],
         "AP19 frozen parent wire/solution changed")
    need(api_review() == pins["official_api_review"], "AP19 API review pins changed")


def frozen():
    pins = read(DEST / "preparation.json")
    hash_gate(pins)
    payloads = {name: (DEST / name).read_bytes() for name in pins["payload_sha256"]}
    return read(DEST / "manifest.json"), payloads, pins


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
