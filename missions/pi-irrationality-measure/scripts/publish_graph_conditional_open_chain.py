"""Publish the genuine NoFixedData Open node and verify the existing conditional target.

Offline modes never use credentials, a network, or Lean.  ``--advance`` writes
durable intent before each POST and only polls known jobs/submissions afterwards.
The resulting conditional submission is an Open sketch, not a closed proof.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import certify_graph_conditional_open_chain as consumer
import stage_graph_conditional_open_chain as stage


TASK, ROOT, STAGE = stage.TASK, stage.ROOT, stage.STAGE
DEST = STAGE / "publication-v3"
SELF = Path(__file__).resolve()
API = ROOT / "scripts/p2m_api.py"
CERT = consumer.CERT
SOURCE_ROOT_RECORD = stage.SOURCE_ROOT / "publication-v2/publication.json"
ROOT_READBACK = stage.SOURCE_ROOT / "publication-v2/post-root-target.json"
ROOT_ID = "e717eef2-11b1-4b14-9789-65f52c0502e1"
CONDITIONAL_ID = "cbe4fb5f-2db8-4484-b209-ecb4e4efea9a"
A1_ID = "fdcbce8c-d9e6-43dd-8587-cfe865e6e78a"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
STD3 = {"propext", "Classical.choice", "Quot.sound"}
PUBLISH_STATUSES = {"PENDING", "COMPILING", "PUBLISHED", "FAILED", "ERROR"}
VERIFY_STATUSES = {"PENDING", "COMPILING", "SKETCH_ACCEPTED", "ACCEPTED",
                   "CE", "WA", "SORRY", "FAILED", "ERROR"}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha_bytes(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return sha_bytes(Path(path).read_bytes())
def read(path): return json.loads(Path(path).read_text(encoding="utf-8"))
def encode(value): return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def exact(path, raw):
    path = Path(path)
    if path.exists() and path.read_bytes() != raw:
        raise ValueError("Frozen conditional-chain publication artifact differs: " + str(path))
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def task_path(value):
    path = Path(value)
    return path if path.is_absolute() else TASK / path


def metadata(prep):
    statement = (
        "Assume the original global interpolation statement and analytic aggregate statement. "
        "For every real exponent $\\nu>2$ and every fixed admissible datum "
        "$d:\\mathrm{FixedData}(\\nu)$, these hypotheses imply a contradiction:\n\n"
        "$$\n" r"\mathrm{GlobalInterpolation}\;\land\;\mathrm{AnalyticAggregate}"
        r"\;\Longrightarrow\;\bot." "\n$$\n\n"
        "Thus no fixed admissible family can coexist with both source hypotheses at an "
        "exponent above $2$.  This is the source theorem that converts the determinant "
        "estimates into the conditional lower bound for rational approximations to $\\pi$."
    )
    return {
        "theorem_name": stage.previous.NO_FIXED,
        "theorem_title": "The interpolation and analytic bounds exclude fixed admissible data",
        "natural_language_statement": statement,
        "tags": ["number-theory", "determinants", "irrationality-measure", "openai-pi-exponent-017"],
        "source": ("https://github.com/openai/math/blob/" + prep["source_commit"] +
                   "/lean/OAI/NumberTheory/PiExponent/Approximation/"
                   "DeterminantContradiction.lean#L125-L165"),
    }


def explanation():
    return (
        "Assume the global interpolation and analytic aggregate hypotheses.  To prove the "
        "eventual lower bound, fix $\\nu>2$ and suppose it fails.  Negating the eventual "
        "quantifier yields rational approximations of exponent $\\nu$ beyond every natural "
        "threshold.  The accepted source theorem "
        "`OAI.PiExponent.exists_admissible_parameters_source017` constructs fixed admissible "
        "data from those approximations.  The source-faithful NoFixedData theorem then applies "
        "to that datum and the two global hypotheses, producing a contradiction.  Therefore "
        "there is a threshold $Q\\ge2$ beyond which\n\n"
        "$$\nq^{-\\nu}\\le\\left|\\pi-\\frac pq\\right|\n$$\n\n"
        "for every integer $p$ and natural $q\\ge Q$.  The two imported children are the "
        "proved A1 existence theorem and the Open NoFixedData target, so this submission is "
        "intentionally a dependency sketch."
    )


def exact_theorem(current, expected, theorem_id, status=None):
    need(current.get("theorem_id") == theorem_id
         and current.get("theorem_name") == expected["theorem_name"]
         and current.get("preamble") == expected["preamble"]
         and current.get("formal_statement") == expected["formal_statement"]
         and current.get("mathlib_rev") == ENV
         and current.get("visibility") == "public"
         and current.get("deprecated_at") is None,
         "Server theorem identity/wire differs: " + expected["theorem_name"])
    if status is not None:
        need(current.get("status") == status,
             "Server theorem status differs: " + expected["theorem_name"])


def static(require_cert=False):
    stage.check()
    prep = read(STAGE / stage.PREP)
    need(prep["NoFixedData"]["name"] == stage.previous.NO_FIXED
         and prep["A1_reference"]["platform_theorem_id"] == A1_ID
         and prep["A1_reference"]["actual_platform_status"] == "ACCEPTED_AND_PROVED"
         and prep["conditional"]["platform_theorem_id"] == CONDITIONAL_ID
         and prep["conditional"]["platform_status"] == "Open"
         and prep["validated"] is False and prep["submission_ready"] is False,
         "Conditional-chain stage identity/status differs")
    nfd = STAGE / stage.NFD_FILE
    nfd_raw = nfd.read_bytes()
    nfd_preamble = prep["NoFixedData"]["preamble"]
    nfd_formal = prep["NoFixedData"]["formal_statement"]
    need((nfd_preamble + nfd_formal).encode() == nfd_raw
         and sha(nfd) == prep["NoFixedData"]["complete_compiled_wire_sha256"],
         "NoFixedData preamble/formal statement is not the complete compiled wire")
    conditional_wire = (STAGE / "conditional-published-wire.lean").read_bytes()
    conditional = read(stage.CONDITIONAL_READBACK)
    need((conditional["preamble"] + conditional["formal_statement"]).encode() == conditional_wire
         and conditional["theorem_id"] == CONDITIONAL_ID and conditional["status"] == "Open",
         "Frozen conditional public wire differs")
    a1_record = read(stage.previous.A1_RECORD)
    a1 = a1_record["target_readback"]["body"]
    need(a1_record["confirmed_proved"] is True
         and a1_record["last_verify_verdict"]["body"]["status"] == "ACCEPTED"
         and a1["theorem_id"] == A1_ID and a1["status"] == "Proved"
         and (a1["preamble"] + a1["formal_statement"]).encode() ==
             (STAGE / stage.A1_FILE).read_bytes(),
         "Frozen A1 Accepted/Proved wire differs")
    root_readback = read(ROOT_READBACK)
    need(root_readback["theorem_id"] == ROOT_ID
         and root_readback["status"] == "Open"
         and root_readback["mathlib_rev"] == ENV,
         "Frozen e717 root readback differs")
    solution = STAGE / stage.SOLUTION_FILE
    solution_raw = solution.read_bytes()
    need(sha(solution) == prep["conditional"]["candidate_solution_sha256"]
         and solution_raw.count(stage.previous.A1.encode()) == 1
         and solution_raw.count(b"no_fixed_data_of_interpolation_and_analytic_aggregate") == 2
         and solution_raw.count(b"theorem solution") == 1
         and b"sorry" not in solution_raw
         and stage.previous.TARGET.encode() not in solution_raw,
         "Conditional solution is not the exact two-parent source route")
    problem = {"theorem_name": stage.previous.NO_FIXED,
               "theorem_title": metadata(prep)["theorem_title"],
               "preamble": nfd_preamble, "formal_statement": nfd_formal,
               "natural_language_statement": metadata(prep)["natural_language_statement"],
               "source": metadata(prep)["source"], "tags": metadata(prep)["tags"]}
    publish = {"problems": [problem], "env": ENV, "private": False}
    descriptor = {"theorem_id": CONDITIONAL_ID, "proof_type": "prove",
                  "explanation": explanation(),
                  "file": {"filename": Path(stage.SOLUTION_FILE).name,
                           "source": stage.rel(solution), "sha256": sha(solution),
                           "utf8": solution_raw.decode("utf-8")}}
    spec = importlib.util.spec_from_file_location("p2m_api_offline", API)
    api = importlib.util.module_from_spec(spec); spec.loader.exec_module(api)
    multipart, ctype = api._multipart(
        {"theorem_id": CONDITIONAL_ID, "proof_type": "prove",
         "explanation": descriptor["explanation"]},
        {"file": (descriptor["file"]["filename"], solution_raw)})
    cert = None
    if require_cert:
        need(CERT.is_file(), "Actual conditional Open-chain certificate is pending")
        cert = read(CERT)
        replay(cert, prep)
    payloads = {"publish-payload.json": json.dumps(publish, ensure_ascii=False).encode(),
                "verification-payload.json": encode(descriptor),
                "verification-request.multipart": multipart}
    pins = {
        "schema_version": 1,
        "artifact_kind": "conditional-open-NoFixedData-publish-and-existing-target-sketch-preparation",
        "NoFixedData_name": stage.previous.NO_FIXED,
        "conditional_theorem_id": CONDITIONAL_ID,
        "conditional_name": stage.previous.TARGET,
        "A1_theorem_id": A1_ID, "A1_name": stage.previous.A1,
        "root_theorem_id": ROOT_ID, "environment": ENV,
        "stage_preparation_sha256": sha(STAGE / stage.PREP),
        "validation_sha256": sha(CERT) if CERT.is_file() else None,
        "stage_producer_sha256": sha(Path(stage.__file__)),
        "strict_consumer_sha256": sha(Path(consumer.__file__)),
        "wrapper_sha256": sha(SELF), "api_client_sha256": sha(API),
        "NoFixedData_wire_sha256": sha(nfd),
        "conditional_wire_sha256": sha(STAGE / "conditional-published-wire.lean"),
        "A1_wire_sha256": sha(STAGE / stage.A1_FILE),
        "solution_sha256": sha(solution),
        "input_sha256": prep["input_sha256"],
        "compiler_manifest_sha256": {name: sha(STAGE / name)
                                     for name in prep["ordered_compiler_manifests"]},
        "source_root_record_sha256": sha(SOURCE_ROOT_RECORD),
        "root_readback_sha256": sha(ROOT_READBACK),
        "payload_sha256": {name: sha_bytes(raw) for name, raw in payloads.items()},
        "multipart_content_type": ctype,
        "publish_route": "/submit-problem", "verify_route": "/verify",
        "exact_existing_conditional_only": True,
        "expected_verify_status": "SKETCH_ACCEPTED",
        "closed_proof": False, "Open_sketch": True,
        "durable_policy": "write intent before POST; never repeat an existing intent; poll only known ids",
        "API_used": False, "submission_ready": False,
    }
    return prep, problem, publish, descriptor, multipart, payloads, pins, cert


def replay(cert, prep):
    need(consumer.validate(write=False) == cert,
         "Conditional-chain certificate differs from exact replay")
    need(cert["schema_version"] == 1
         and cert["artifact_kind"] == "graph-conditional-open-NoFixedData-type-and-reference-validation"
         and cert["validated_interface"] is True
         and cert["validated_closed_proof"] is False
         and cert["NoFixedData_open_publication_type_ready"] is True
         and cert["conditional_sketch_only"] is True
         and cert["submission_ready"] is False and cert["proposal_status"] == "Draft"
         and cert["Lean_started_by_consumer"] is False and cert["API_used"] is False,
         "Conditional-chain certificate semantic state differs")
    need(cert["NoFixedData_name"] == stage.previous.NO_FIXED
         and cert["NoFixedData_source_command_sha256"] == prep["NoFixedData"]["source_command_sha256"]
         and cert["NoFixedData_exact_wire_sha256"] == sha(STAGE / stage.NFD_FILE)
         and cert["A1_platform_accepted_and_proved"] is True
         and cert["conditional_published_Open_theorem_id"] == CONDITIONAL_ID
         and cert["source_to_generated_type_equal"] is True
         and cert["theorem_proof_values_exported"] is False,
         "Conditional-chain type/wire/identity gates differ")
    need(cert["conditional_exact_A1_reference_replacement"] ==
         ["OAI.PiExponent.exists_admissible_parameters", stage.previous.A1]
         and stage.previous.A1 in cert["conditional_actual_solution_project_valueRefs"]
         and stage.previous.NO_FIXED in cert["conditional_actual_solution_project_valueRefs"]
         and stage.previous.TARGET not in cert["conditional_actual_solution_project_valueRefs"],
         "Conditional actual proof references differ")
    for axioms in cert["source_axioms"].values():
        need(set(axioms) <= STD3 and "sorryAx" not in axioms,
             "Original source proof is not closed Std3")
    for axioms in cert["generated_local_sketch_axioms"].values():
        need(set(axioms) <= STD3 | {"sorryAx"} and "sorryAx" in axioms,
             "Generated Open sketch has unexpected axiom envelope")
    need(set(cert["all_five_preflights"]) == set(prep["ordered_compiler_manifests"])
         and all(row["success"] is True and 0 < row["seconds"] <= 300
                 for row in cert["all_five_preflights"].values()),
         "Conditional-chain five-preflight domain/budget differs")
    need(sha(TASK / cert["source_snapshot"]) == cert["source_snapshot_sha256"]
         and sha(TASK / cert["generated_snapshot"]) == cert["generated_snapshot_sha256"]
         and cert["stage_preparation_sha256"] == sha(STAGE / stage.PREP)
         and cert["NoFixedData_exact_name_lookup_sha256"] == sha(stage.NO_FIXED_GET)
         and cert["A1_actual_publication_sha256"] == sha(stage.previous.A1_RECORD)
         and cert["conditional_actual_public_readback_sha256"] == sha(stage.CONDITIONAL_READBACK),
         "Conditional-chain evidence hashes differ")
    for path, expected in cert["implementation_sha256"].items():
        need(sha(TASK / path) == expected, "Conditional-chain implementation changed: " + path)


def prepare_pending():
    *_, payloads, pins, cert = static(require_cert=False)
    for name, raw in payloads.items(): exact(DEST / name, raw)
    record = dict(pins)
    record.update({"artifact_kind": "conditional-open-chain-pending-publication",
                   "strict_validation_pending": cert is None,
                   "network_used": False, "proposal_status": "Draft"})
    exact(DEST / "pending-preparation.json", encode(record))
    return {"prepared": True, "validation_pending": cert is None, "network_used": False,
            "Open_sketch": True, "closed_proof": False,
            "payload_sha256": pins["payload_sha256"]}


def prepare():
    *_, payloads, pins, cert = static(require_cert=True)
    for name, raw in payloads.items(): exact(DEST / name, raw)
    exact(DEST / "validation.json", CERT.read_bytes())
    exact(DEST / "preparation.json", encode(pins))
    return {"prepared": True, "network_used": False, "API_used": False,
            "Open_sketch": True, "closed_proof": False,
            "payload_sha256": pins["payload_sha256"]}


def check():
    result = static(require_cert=True)
    payloads, pins = result[-3], result[-2]
    need((DEST / "validation.json").read_bytes() == CERT.read_bytes()
         and (DEST / "preparation.json").read_bytes() == encode(pins),
         "Frozen conditional-chain preparation differs")
    for name, raw in payloads.items():
        need((DEST / name).read_bytes() == raw, "Frozen conditional-chain payload differs: " + name)
    need(sha(SELF) == pins["wrapper_sha256"] and sha(API) == pins["api_client_sha256"]
         and sha(SOURCE_ROOT_RECORD) == pins["source_root_record_sha256"]
         and sha(ROOT_READBACK) == pins["root_readback_sha256"],
         "Conditional-chain wrapper/API/root-route pins differ")
    for path, expected in pins["input_sha256"].items():
        need(sha(TASK / path) == expected, "Conditional-chain stage input changed: " + path)
    return result


def graph_check(graph, decompositions, submission_id, nfd_id):
    sketch = "sketch-" + submission_id
    edges = {(x.get("source"), x.get("target"), x.get("kind")) for x in graph.get("edges", [])}
    need(graph.get("root_id") == CONDITIONAL_ID
         and (A1_ID, sketch, "sketch") in edges
         and (nfd_id, sketch, "sketch") in edges
         and (sketch, CONDITIONAL_ID, "sketch") in edges,
         "Conditional graph lacks the actual A1/NoFixedData sketch edges")
    rows = [x for x in decompositions.get("decompositions", [])
            if x.get("submission_id") == submission_id]
    children = {x.get("theorem_id") for x in rows[0].get("children", [])} if len(rows) == 1 else set()
    need(children >= {A1_ID, nfd_id},
         "Conditional decomposition lacks its two actual children")
    return {"sketch_node": sketch, "A1_to_sketch": True,
            "NoFixedData_to_sketch": True, "sketch_to_conditional": True,
            "decomposition_two_children": True}


def root_path_check(graph, conditional_sketch, nfd_id):
    record = read(SOURCE_ROOT_RECORD)
    root_sketch = "sketch-" + record["submission_id"]
    edges = {(x.get("source"), x.get("target"), x.get("kind")) for x in graph.get("edges", [])}
    required = {(A1_ID, conditional_sketch, "sketch"),
                (nfd_id, conditional_sketch, "sketch"),
                (conditional_sketch, CONDITIONAL_ID, "sketch"),
                (CONDITIONAL_ID, root_sketch, "sketch"),
                (root_sketch, ROOT_ID, "sketch")}
    need(graph.get("root_id") == ROOT_ID and required <= edges,
         "Root graph lacks the actual A1/NoFixedData to conditional to e717 path")
    return {"root_sketch_node": root_sketch, "conditional_sketch_node": conditional_sketch,
            "A1_to_root_path": True, "NoFixedData_to_root_path": True,
            "nodes": len(graph.get("nodes", [])), "edges": len(graph.get("edges", []))}


def advance():
    prep, problem, publish, descriptor, multipart, payloads, pins, cert = check()
    record_path = DEST / "publication.json"
    record = read(record_path) if record_path.exists() else {
        "NoFixedData_name": stage.previous.NO_FIXED,
        "conditional_theorem_id": CONDITIONAL_ID, "A1_theorem_id": A1_ID,
        "root_theorem_id": ROOT_ID, "environment": ENV,
        "preparation_sha256": sha(DEST / "preparation.json")}
    need(record["NoFixedData_name"] == stage.previous.NO_FIXED
         and record["conditional_theorem_id"] == CONDITIONAL_ID
         and record["A1_theorem_id"] == A1_ID and record["root_theorem_id"] == ROOT_ID
         and record["environment"] == ENV
         and record["preparation_sha256"] == sha(DEST / "preparation.json"),
         "Existing conditional-chain durable record differs")

    def save():
        record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
        record_path.write_bytes(encode(record))

    spec = importlib.util.spec_from_file_location("p2m_api", API)
    api = importlib.util.module_from_spec(spec); spec.loader.exec_module(api)
    token = None
    def request(method, path, **kwargs):
        nonlocal token
        need(sha(SELF) == pins["wrapper_sha256"] and sha(API) == pins["api_client_sha256"]
             and sha(DEST / "preparation.json") == record["preparation_sha256"],
             "Frozen conditional-chain request inputs changed")
        if token is None: token = api.get_token()
        status, raw = api._request(method, path, token=token, **kwargs)
        need(sha(DEST / "preparation.json") == record["preparation_sha256"],
             "Frozen conditional-chain preparation changed during request")
        return status, json.loads(raw)
    def get(path):
        status, body = request("GET", path)
        need(status == 200 and isinstance(body, dict), "GET failed: " + path)
        return body

    if not record.get("NoFixedData_theorem_id") and not record.get("publish_intent"):
        matches, offset = [], 0
        while True:
            status, body = request("GET", "/theorems?theorem_name=" +
                                   quote(stage.previous.NO_FIXED) + f"&env={ENV}&limit=100&offset={offset}")
            need(status == 200 and isinstance(body.get("theorems"), list),
                 "NoFixedData exact-name lookup failed")
            page = body["theorems"]
            matches += [x for x in page if x.get("theorem_name") == stage.previous.NO_FIXED]
            offset += len(page)
            if offset >= body["total"]: break
            need(bool(page), "Incomplete NoFixedData exact-name pagination")
        need(len(matches) <= 1, "Duplicate exact NoFixedData name")
        if matches:
            theorem_id = matches[0].get("theorem_id")
            need(isinstance(theorem_id, str) and theorem_id, "Existing NoFixedData lacks id")
            item = get("/theorems/" + theorem_id)
            exact_theorem(item, problem, theorem_id, "Open")
            record["NoFixedData_theorem_id"] = theorem_id
            record["reused_exact_existing_NoFixedData"] = True; save()
        else:
            env = get("/environments")
            need(any(x.get("mathlib_rev") == ENV and x.get("toolchain") == TOOLCHAIN
                     for x in env.get("environments", [])), "Pinned environment unavailable")
            record["publish_intent"] = {"at_utc": datetime.now(timezone.utc).isoformat(),
                "endpoint": "/submit-problem",
                "payload_sha256": pins["payload_sha256"]["publish-payload.json"]}
            save()
            status, body = request("POST", "/submit-problem", raw_body=payloads["publish-payload.json"])
            record["publish_response"] = {"http_status": status, "body": body}
            jobs = body.get("jobs", [])
            if status == 202 and not body.get("errors") and len(jobs) == 1 \
                    and jobs[0].get("name") == stage.previous.NO_FIXED and jobs[0].get("job_id"):
                record["publish_job_id"] = jobs[0]["job_id"]
            save()
            need(record.get("publish_job_id"), "Uncertain NoFixedData POST recorded; never repeat")
            return record
    if not record.get("NoFixedData_theorem_id"):
        need(record.get("publish_job_id"), "Publish intent lacks known job; never repeat")
        status, body = request("GET", "/publish-jobs/" + record["publish_job_id"])
        record["last_publish_verdict"] = {"http_status": status, "body": body}; save()
        need(status == 200 and body.get("status") in PUBLISH_STATUSES,
             "Unknown NoFixedData publish status")
        if body.get("status") != "PUBLISHED": return record
        theorem_id = body.get("theorem_id")
        need(isinstance(theorem_id, str) and theorem_id, "PUBLISHED NoFixedData lacks id")
        record["NoFixedData_theorem_id"] = theorem_id; save()

    nfd_id = record["NoFixedData_theorem_id"]
    nfd = get("/theorems/" + nfd_id); exact_theorem(nfd, problem, nfd_id, "Open")
    a1_expected = read(stage.previous.A1_RECORD)["target_readback"]["body"]
    a1 = get("/theorems/" + A1_ID); exact_theorem(a1, a1_expected, A1_ID, "Proved")
    conditional_expected = read(stage.CONDITIONAL_READBACK)
    conditional = get("/theorems/" + CONDITIONAL_ID)
    exact_theorem(conditional, conditional_expected, CONDITIONAL_ID, "Open")
    for name, body in (("NoFixedData", nfd), ("A1", a1), ("conditional", conditional)):
        path = DEST / "pre-verify-readbacks" / (name + ".json")
        path.parent.mkdir(parents=True, exist_ok=True); path.write_bytes(encode(body))
        record.setdefault("pre_verify_readback_sha256", {})[name] = sha(path)
    save()

    if not record.get("verify_intent"):
        record["verify_intent"] = {"at_utc": datetime.now(timezone.utc).isoformat(),
            "endpoint": "/verify", "theorem_id": CONDITIONAL_ID,
            "A1_theorem_id": A1_ID, "NoFixedData_theorem_id": nfd_id,
            "multipart_sha256": pins["payload_sha256"]["verification-request.multipart"],
            "content_type": pins["multipart_content_type"],
            "solution_sha256": pins["solution_sha256"]}
        save()
        status, body = request("POST", "/verify", raw_body=multipart,
                               ctype=pins["multipart_content_type"])
        record["verify_response"] = {"http_status": status, "body": body}
        if status in (200, 202) and body.get("status") in VERIFY_STATUSES:
            record["submission_id"] = body.get("submission_id") or body.get("id")
        save()
        need(record.get("submission_id"), "Uncertain verify POST recorded; never repeat")
        if body.get("status") != "SKETCH_ACCEPTED": return record
    else:
        need(record.get("submission_id"), "Verify intent lacks known submission; never repeat")
        status, body = request("GET", "/verify?submission_id=" + record["submission_id"])
        record["last_verify_verdict"] = {"http_status": status, "body": body}; save()
        need(status == 200 and body.get("theorem_id") == CONDITIONAL_ID
             and body.get("status") in VERIFY_STATUSES, "Unknown conditional verify status")
        if body.get("status") != "SKETCH_ACCEPTED": return record

    conditional = get("/theorems/" + CONDITIONAL_ID)
    nfd = get("/theorems/" + nfd_id)
    a1 = get("/theorems/" + A1_ID)
    exact_theorem(conditional, conditional_expected, CONDITIONAL_ID, "Open")
    exact_theorem(nfd, problem, nfd_id, "Open")
    exact_theorem(a1, a1_expected, A1_ID, "Proved")
    graph = get("/theorems/" + CONDITIONAL_ID + "/graph")
    decompositions = get("/theorems/" + CONDITIONAL_ID + "/decompositions")
    local = graph_check(graph, decompositions, record["submission_id"], nfd_id)
    root_target = get("/theorems/" + ROOT_ID)
    exact_theorem(root_target, read(ROOT_READBACK), ROOT_ID, "Open")
    root_graph = get("/theorems/" + ROOT_ID + "/graph")
    root_path = root_path_check(root_graph, local["sketch_node"], nfd_id)
    docs = {"post-conditional-target.json": conditional, "post-NoFixedData.json": nfd,
            "post-A1.json": a1, "post-conditional-graph.json": graph,
            "post-conditional-decompositions.json": decompositions,
            "post-root-target.json": root_target, "post-root-graph.json": root_graph}
    for name, body in docs.items(): (DEST / name).write_bytes(encode(body))
    record["post_acceptance_readback_sha256"] = {name: sha(DEST / name) for name in docs}
    record["actual_two_child_edges"] = local
    record["actual_root_transitive_paths"] = root_path
    record["confirmed_SKETCH_ACCEPTED"] = True; save(); return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-pending", action="store_true")
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    if args.prepare_pending: result = prepare_pending()
    elif args.prepare_only: result = prepare()
    elif args.check_only:
        checked = check(); result = {"checked": True, "network_used": False,
            "Open_sketch": True, "closed_proof": False,
            "payload_sha256": checked[-2]["payload_sha256"]}
    else: result = advance()
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__": main()
