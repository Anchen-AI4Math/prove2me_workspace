"""Durable arithmetic Open publication and existing NoFixedData sketch wrapper.

Only --advance contacts the platform; it is reserved for the root agent.
--prepare-only is pure and requires the eight-preflight strict certificate.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import prepare_graph_no_fixed_data_five_children_publication as offline
import stage_graph_no_fixed_data_five_children as stage


TASK, STAGE, DEST = offline.TASK, offline.STAGE, offline.DEST
SELF = Path(__file__).resolve()
ENV = offline.ENV
TOOLCHAIN = "leanprover/lean4:v4.33.1"
PUBLISH_STATUSES = {"PENDING", "COMPILING", "PUBLISHED", "FAILED", "ERROR"}
VERIFY_STATUSES = {"PENDING", "COMPILING", "SKETCH_ACCEPTED", "ACCEPTED",
                   "CE", "WA", "SORRY", "FAILED", "ERROR"}
ROOT_ID = "e717eef2-11b1-4b14-9789-65f52c0502e1"
CONDITIONAL_ID = "cbe4fb5f-2db8-4484-b209-ecb4e4efea9a"
A1_ID = "fdcbce8c-d9e6-43dd-8587-cfe865e6e78a"
CONDITIONAL_RECORD = TASK / "verification/graph-conditional-route-20261011-v2/publication-v3/publication.json"
ROOT_RECORD = TASK / "verification/graph-source-root-20261011/publication-v2/publication.json"
ROOT_READBACK = TASK / "verification/graph-source-root-20261011/publication-v2/post-root-target.json"
CONDITIONAL_READBACK = TASK / "verification/graph-source-root-20261011/publication-v2/parent-readbacks/conditional.json"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def exact_theorem(actual, expected, theorem_id, status):
    need(actual.get("theorem_id") == theorem_id and
         actual.get("theorem_name") == expected["theorem_name"] and
         actual.get("preamble") == expected["preamble"] and
         actual.get("formal_statement") == expected["formal_statement"] and
         actual.get("status") == status and actual.get("mathlib_rev") == ENV and
         actual.get("visibility") == "public" and actual.get("deprecated_at") is None,
         "Fresh public theorem identity/type/wire differs: " + expected["theorem_name"])


def preparation():
    prep, problem, descriptor, payloads, pins, cert = offline.check()
    need(offline.sha(SELF) == pins["online_wrapper_sha256"] and
         offline.sha(offline.API) == pins["api_client_sha256"],
         "Online wrapper/API differ from frozen final preparation")
    return prep, problem, descriptor, payloads, pins, cert


def graph_check(graph, decompositions, submission_id, nfd_id, children):
    sketch = "sketch-" + submission_id
    edges = {(row.get("source"), row.get("target"), row.get("kind"))
             for row in graph.get("edges", [])}
    required = {(child, sketch, "sketch") for child in children}
    required.add((sketch, nfd_id, "sketch"))
    need(graph.get("root_id") == nfd_id and required <= edges,
         "Fresh NoFixedData graph lacks all five actual child-to-sketch-to-parent edges")
    rows = [row for row in decompositions.get("decompositions", [])
            if row.get("submission_id") == submission_id]
    got = {child.get("theorem_id") for child in rows[0].get("children", [])} if len(rows) == 1 else set()
    need(got >= children, "Fresh NoFixedData decomposition lacks the five actual children")
    return sketch, {"five_actual_children": sorted(children), "actual_sketch_node": sketch,
                    "NoFixedData_parent": nfd_id, "graph_edges": len(graph.get("edges", []))}


def root_path_check(graph, nfd_sketch, nfd_id, children):
    conditional = offline.read(CONDITIONAL_RECORD)
    source_root = offline.read(ROOT_RECORD)
    need(conditional.get("confirmed_SKETCH_ACCEPTED") is True and
         conditional.get("submission_id") and source_root.get("submission_id"),
         "Earlier conditional/root graph sketches are not durably accepted")
    conditional_sketch = "sketch-" + conditional["submission_id"]
    root_sketch = "sketch-" + source_root["submission_id"]
    edges = {(row.get("source"), row.get("target"), row.get("kind"))
             for row in graph.get("edges", [])}
    required = {(child, nfd_sketch, "sketch") for child in children}
    required |= {(nfd_sketch, nfd_id, "sketch"),
                 (A1_ID, conditional_sketch, "sketch"),
                 (nfd_id, conditional_sketch, "sketch"),
                 (conditional_sketch, CONDITIONAL_ID, "sketch"),
                 (CONDITIONAL_ID, root_sketch, "sketch"),
                 (root_sketch, ROOT_ID, "sketch")}
    need(graph.get("root_id") == ROOT_ID and required <= edges,
         "Fresh root graph lacks all five transitive source child paths")
    return {"five_children_to_root_transitive": True,
            "NoFixedData_sketch_node": nfd_sketch,
            "conditional_sketch_node": conditional_sketch,
            "root_sketch_node": root_sketch,
            "root_graph_edges": len(graph.get("edges", []))}


def advance():
    prep, problem, descriptor, payloads, pins, cert = preparation()
    online = DEST / "online-preparation-driver.json"
    need(online.is_file() and online.read_bytes() == offline.encode(pins),
         "Reviewed offline online-preparation descriptor differs")
    nfd_id = pins["NoFixedData_theorem_id"]
    children = pins["child_theorem_ids"]
    record_path = DEST / "publication.json"
    record = offline.read(record_path) if record_path.is_file() else {
        "NoFixedData_theorem_id": nfd_id, "arithmetic_source017_name": stage.ARITH,
        "environment": ENV, "preparation_sha256": offline.sha(DEST / "preparation.json")}
    need(record["NoFixedData_theorem_id"] == nfd_id and
         record["arithmetic_source017_name"] == stage.ARITH and
         record["environment"] == ENV and
         record["preparation_sha256"] == offline.sha(DEST / "preparation.json"),
         "Existing five-child durable record differs")

    def save():
        record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
        record_path.write_bytes(offline.encode(record))

    spec = importlib.util.spec_from_file_location("p2m_api", offline.API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = None

    def request(method, path, **kwargs):
        nonlocal token
        preparation()  # Full pure certificate, OLean, source, and payload hash gate per HTTP request.
        need(offline.sha(online) == offline.sha_bytes(offline.encode(pins)) and
             offline.sha(DEST / "preparation.json") == record["preparation_sha256"],
             "Frozen request descriptor changed")
        if token is None:
            token = api.get_token()
        status, raw = api._request(method, path, token=token, **kwargs)
        need(offline.sha(DEST / "preparation.json") == record["preparation_sha256"],
             "Frozen preparation changed during HTTP request")
        return status, json.loads(raw)

    def get(path):
        status, body = request("GET", path)
        need(status == 200 and isinstance(body, dict), "GET failed: " + path)
        return body

    if not record.get("arithmetic_theorem_id") and not record.get("arithmetic_publish_intent"):
        matches, offset = [], 0
        while True:
            status, body = request("GET", "/theorems?theorem_name=" + quote(stage.ARITH) +
                                   f"&env={ENV}&limit=100&offset={offset}")
            need(status == 200 and isinstance(body.get("theorems"), list),
                 "Fresh exact arithmetic theorem lookup failed")
            page = body["theorems"]
            matches += [row for row in page if row.get("theorem_name") == stage.ARITH]
            offset += len(page)
            if offset >= body["total"]:
                break
            need(bool(page), "Incomplete exact arithmetic theorem pagination")
        need(len(matches) <= 1, "Duplicate exact arithmetic source017 name")
        if matches:
            theorem_id = matches[0].get("theorem_id")
            need(isinstance(theorem_id, str) and theorem_id, "Existing arithmetic target lacks id")
            target = get("/theorems/" + theorem_id)
            exact_theorem(target, problem, theorem_id, "Open")
            record["arithmetic_theorem_id"] = theorem_id
            record["reused_exact_existing_arithmetic_Open"] = True
            save()
        else:
            envs = get("/environments")
            need(any(row.get("mathlib_rev") == ENV and row.get("toolchain") == TOOLCHAIN
                     for row in envs.get("environments", [])), "Pinned environment unavailable")
            record["arithmetic_publish_intent"] = {
                "at_utc": datetime.now(timezone.utc).isoformat(),
                "endpoint": "/submit-problem",
                "payload_sha256": pins["payload_sha256"]["arithmetic-publish-payload.json"]}
            save()
            status, body = request("POST", "/submit-problem",
                                   raw_body=payloads["arithmetic-publish-payload.json"])
            record["arithmetic_publish_response"] = {"http_status": status, "body": body}
            jobs = body.get("jobs", [])
            if (status == 202 and not body.get("errors") and len(jobs) == 1 and
                    jobs[0].get("name") == stage.ARITH and jobs[0].get("job_id")):
                record["arithmetic_publish_job_id"] = jobs[0]["job_id"]
            save()
            need(record.get("arithmetic_publish_job_id"),
                 "Uncertain arithmetic POST recorded; never repeat")
            return record
    if not record.get("arithmetic_theorem_id"):
        need(record.get("arithmetic_publish_job_id"),
             "Arithmetic publish intent lacks a known job; never repeat")
        status, body = request("GET", "/publish-jobs/" + record["arithmetic_publish_job_id"])
        record["last_arithmetic_publish_verdict"] = {"http_status": status, "body": body}
        save()
        need(status == 200 and body.get("status") in PUBLISH_STATUSES,
             "Unknown arithmetic publish status")
        if body["status"] != "PUBLISHED":
            return record
        theorem_id = body.get("theorem_id")
        need(isinstance(theorem_id, str) and theorem_id, "Published arithmetic target lacks id")
        record["arithmetic_theorem_id"] = theorem_id
        save()
    arith_id = record["arithmetic_theorem_id"]
    arith = get("/theorems/" + arith_id)
    exact_theorem(arith, problem, arith_id, "Open")
    nfd_expected_wire = (STAGE / stage.NFD_FILE).read_bytes()
    nfd_preamble = nfd_expected_wire.split(b"theorem ", 1)[0]
    nfd_expected = {"theorem_name": stage.NFD, "preamble": nfd_preamble.decode(),
                    "formal_statement": nfd_expected_wire[len(nfd_preamble):].decode()}
    nfd = get("/theorems/" + nfd_id)
    exact_theorem(nfd, nfd_expected, nfd_id, "Open")
    expected_children = {}
    for label, name, _source, _module, source_record, _stage_status in stage.CHILDREN:
        child_id = children[label]
        saved = offline.read(source_record)["target_readback"]["body"]
        child = get("/theorems/" + child_id)
        exact_theorem(child, saved, child_id, "Proved")
        expected_children[label] = child
    docs = {"arithmetic": arith, "NoFixedData": nfd, **expected_children}
    for label, body in docs.items():
        path = DEST / "pre-verify-readbacks" / (label + ".json")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(offline.encode(body))
        record.setdefault("pre_verify_readback_sha256", {})[label] = offline.sha(path)
    save()

    if not record.get("verify_intent"):
        record["verify_intent"] = {
            "at_utc": datetime.now(timezone.utc).isoformat(), "endpoint": "/verify",
            "theorem_id": nfd_id, "actual_five_child_theorem_ids": sorted([*children.values(), arith_id]),
            "multipart_sha256": pins["payload_sha256"]["verification-request.multipart"],
            "content_type": pins["multipart_content_type"],
            "solution_sha256": pins["solution_sha256"]}
        save()
        status, body = request("POST", "/verify",
                               raw_body=payloads["verification-request.multipart"],
                               ctype=pins["multipart_content_type"])
        record["verify_response"] = {"http_status": status, "body": body}
        if status in (200, 202) and body.get("status") in VERIFY_STATUSES:
            record["submission_id"] = body.get("submission_id") or body.get("id")
        save()
        need(record.get("submission_id"), "Uncertain NoFixedData verify POST recorded; never repeat")
        if body.get("status") != "SKETCH_ACCEPTED":
            return record
    else:
        need(record.get("submission_id"), "Verify intent lacks known submission; never repeat")
        status, body = request("GET", "/verify?submission_id=" + record["submission_id"])
        record["last_verify_verdict"] = {"http_status": status, "body": body}
        save()
        need(status == 200 and body.get("theorem_id") == nfd_id and
             body.get("status") in VERIFY_STATUSES, "Unknown NoFixedData verification status")
        if body["status"] != "SKETCH_ACCEPTED":
            return record

    # Acceptance alone is insufficient: re-read every theorem, decomposition,
    # and both local/root graphs from the API before recording graph closure.
    arith = get("/theorems/" + arith_id)
    nfd = get("/theorems/" + nfd_id)
    exact_theorem(arith, problem, arith_id, "Open")
    exact_theorem(nfd, nfd_expected, nfd_id, "Open")
    post_children = {}
    for label, saved in expected_children.items():
        child = get("/theorems/" + children[label])
        exact_theorem(child, saved, children[label], "Proved")
        post_children[label] = child
    local_graph = get("/theorems/" + nfd_id + "/graph")
    decompositions = get("/theorems/" + nfd_id + "/decompositions")
    child_ids = set(children.values()) | {arith_id}
    sketch, local = graph_check(local_graph, decompositions, record["submission_id"], nfd_id, child_ids)
    conditional = get("/theorems/" + CONDITIONAL_ID)
    exact_theorem(conditional, offline.read(CONDITIONAL_READBACK), CONDITIONAL_ID, "Open")
    root_target = get("/theorems/" + ROOT_ID)
    exact_theorem(root_target, offline.read(ROOT_READBACK), ROOT_ID, "Open")
    root_graph = get("/theorems/" + ROOT_ID + "/graph")
    root_paths = root_path_check(root_graph, sketch, nfd_id, child_ids)
    post = {"arithmetic.json": arith, "NoFixedData.json": nfd,
            **{label + ".json": body for label, body in post_children.items()},
            "NoFixedData-graph.json": local_graph,
            "NoFixedData-decompositions.json": decompositions,
            "conditional.json": conditional, "root.json": root_target,
            "root-graph.json": root_graph}
    for name, body in post.items():
        path = DEST / "post-acceptance-readbacks" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(offline.encode(body))
    record["post_acceptance_readback_sha256"] = {
        name: offline.sha(DEST / "post-acceptance-readbacks" / name) for name in post}
    record["actual_five_child_edges"] = local
    record["actual_root_transitive_paths"] = root_paths
    record["confirmed_SKETCH_ACCEPTED"] = True
    save()
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare-only", action="store_true")
    mode.add_argument("--check-only", action="store_true")
    mode.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        *_, pins, cert = preparation()
        offline.exact(DEST / "online-preparation-driver.json", offline.encode(pins))
        result = {"prepared": True, "network_used": False,
                  "NoFixedData_theorem_id": pins["NoFixedData_theorem_id"],
                  "Open_sketch": True, "closed_proof": False}
    elif args.check_only:
        *_, pins, cert = preparation()
        need((DEST / "online-preparation-driver.json").read_bytes() == offline.encode(pins),
             "Frozen online driver preparation differs")
        result = {"checked": True, "network_used": False,
                  "Open_sketch": True, "closed_proof": False}
    else:
        result = advance()
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
