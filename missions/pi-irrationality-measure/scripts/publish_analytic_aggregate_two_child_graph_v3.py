"""Publish two exact Open analytic children, then verify the existing parent."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import prepare_analytic_aggregate_two_child_publication_v3 as offline


SELF = Path(__file__).resolve()
PUB = offline.DEST
PREPARATION = PUB / "preparation.json"
ONLINE = PUB / "online-preparation-graph.json"
RECORD = PUB / "publication.json"
SOURCE_PUB = offline.STAGE / "publication-v3"
SOURCE_RECORD = SOURCE_PUB / "publication.json"
SOURCE_PREPARATION = SOURCE_PUB / "preparation.json"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
PUBLISH_STATES = {"PENDING", "COMPILING", "PUBLISHED", "FAILED", "ERROR"}
VERIFY_STATES = {"PENDING", "COMPILING", "SKETCH_ACCEPTED",
                 "CE", "WA", "SORRY", "FAILED", "ERROR"}


def descriptor():
    manifest, payloads, pins = offline.frozen()
    offline.need(offline.sha(SELF) == pins["online_wrapper_sha256"],
                 "AP19 reviewed online wrapper hash differs")
    value = {"schema_version": 1,
        "artifact_kind": "ap19-analyticAggregate-two-child-fast-online-preparation-v3",
        "parent_theorem_id": pins["parent_theorem_id"],
        "parent_theorem_name": pins["parent_theorem_name"],
        "child_names": pins["child_names"], "environment": pins["environment"],
        "offline_preparation_sha256": offline.sha(PREPARATION),
        "online_wrapper_sha256": offline.sha(SELF),
        "payload_sha256": pins["payload_sha256"],
        "new_child_POST_requires_fresh_zero_exact_name_environment_matches": True,
        "known_publish_jobs_and_verify_submission_are_polled_without_reposting": True,
        "official_publish_job_contract": {"id": "exact durable job id",
            "kind": "problem", "theorem_name": "exact child name"},
        "post_SKETCH_ACCEPTED_graph_and_decomposition_required": True,
        "hash_gate_before_and_after_every_HTTP": True,
        "Open_sketch": True, "closed_proof": False,
        "creates_campaign_proposal": False, "network_used": False,
        "API_used": False, "submission_ready": False, "proposal_status": "Draft"}
    return manifest, payloads, pins, value


def save(record):
    record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
    RECORD.write_bytes(offline.encode(record))


def adopt_known_terminal():
    manifest, payloads, pins, expected = descriptor()
    offline.need(ONLINE.is_file() and ONLINE.read_bytes() == offline.encode(expected),
                 "AP19 reviewed v4 online descriptor differs")
    offline.need(SOURCE_RECORD.is_file() and SOURCE_PREPARATION.is_file(),
                 "AP19 known terminal v3 record is missing")
    source = offline.read(SOURCE_RECORD)
    source_pins = offline.read(SOURCE_PREPARATION)
    offline.need(source.get("preparation_sha256") == offline.sha(SOURCE_PREPARATION)
                 and source_pins.get("payload_sha256") == pins["payload_sha256"]
                 and source.get("parent_theorem_id") == pins["parent_theorem_id"]
                 and source.get("parent_theorem_name") == pins["parent_theorem_name"]
                 and source.get("child_names") == pins["child_names"]
                 and source.get("environment") == pins["environment"]
                 and source.get("Open_sketch") is True
                 and source.get("closed_proof") is False
                 and source.get("confirmed_SKETCH_ACCEPTED") is True
                 and source.get("count_as_own_Accepted_proof") is False,
                 "AP19 known terminal v3 identity/state differs")
    submission_id = source.get("submission_id")
    child_ids = source.get("child_ids")
    verdict = source.get("last_verify_verdict", {}).get("body", {})
    edges = source.get("actual_two_Open_child_edges", {})
    offline.need(isinstance(submission_id, str) and bool(submission_id)
                 and isinstance(child_ids, dict)
                 and sorted(child_ids) == sorted(pins["child_names"])
                 and all(isinstance(x, str) and bool(x) for x in child_ids.values())
                 and verdict.get("id") == submission_id
                 and verdict.get("theorem_id") == pins["parent_theorem_id"]
                 and verdict.get("status") == "SKETCH_ACCEPTED"
                 and edges.get("sketch_node") == "sketch-" + submission_id
                 and edges.get("child_ids") == child_ids
                 and edges.get("two_child_edges") is True
                 and edges.get("sketch_to_parent") is True,
                 "AP19 known terminal v3 submission/edge evidence differs")
    for row in source.get("exact_child_readbacks", {}).values():
        offline.need(offline.sha(offline.resolved(row["path"])) == row["sha256"],
                     "AP19 known terminal child readback changed")
    for name, value in source.get("post_acceptance_readback_sha256", {}).items():
        offline.need(offline.sha(SOURCE_PUB / name) == value,
                     "AP19 known terminal graph/decomposition evidence changed: " + name)
    adopted = {
        "schema_version": 1,
        "artifact_kind": "ap19-analyticAggregate-two-child-known-terminal-adoption-v4",
        "parent_theorem_id": pins["parent_theorem_id"],
        "parent_theorem_name": pins["parent_theorem_name"],
        "child_names": pins["child_names"], "child_ids": child_ids,
        "submission_id": submission_id,
        "source_terminal_record": offline.stage.rel(SOURCE_RECORD),
        "source_terminal_record_sha256": offline.sha(SOURCE_RECORD),
        "source_terminal_preparation_sha256": offline.sha(SOURCE_PREPARATION),
        "stronger_historical_hash_preparation_sha256": offline.sha(PREPARATION),
        "stronger_online_descriptor_sha256": offline.sha(ONLINE),
        "payload_sha256": pins["payload_sha256"],
        "confirmed_SKETCH_ACCEPTED": True,
        "actual_two_Open_child_edges": edges,
        "count_as_own_Accepted_proof": False,
        "known_terminal_adopted_without_HTTP": True,
        "repeat_child_or_verify_POST_forbidden": True,
        "network_used": False, "API_used": False,
        "Open_sketch": True, "closed_proof": False}
    offline.exact(RECORD, offline.encode(adopted))
    return adopted


def advance():
    offline.need(not SOURCE_RECORD.is_file(),
                 "AP19 v3 is already terminal; adopt it without HTTP and never repeat POST")
    manifest, payloads, pins, expected = descriptor()
    offline.need(ONLINE.is_file() and ONLINE.read_bytes() == offline.encode(expected),
                 "AP19 reviewed online descriptor differs")
    problems = json.loads(payloads["publish-payload.json"])["problems"]
    problem_by_name = {row["theorem_name"]: row for row in problems}
    offline.need(sorted(problem_by_name) == sorted(pins["child_names"]),
                 "AP19 child payload names differ")
    record = offline.read(RECORD) if RECORD.exists() else {
        "parent_theorem_id": pins["parent_theorem_id"],
        "parent_theorem_name": pins["parent_theorem_name"],
        "child_names": pins["child_names"], "environment": pins["environment"],
        "visibility": "public", "preparation_sha256": offline.sha(PREPARATION),
        "Open_sketch": True, "closed_proof": False,
        "creates_campaign_proposal": False}
    offline.need(record.get("parent_theorem_id") == pins["parent_theorem_id"]
                 and record.get("parent_theorem_name") == pins["parent_theorem_name"]
                 and record.get("child_names") == pins["child_names"]
                 and record.get("environment") == pins["environment"]
                 and record.get("visibility") == "public"
                 and record.get("preparation_sha256") == offline.sha(PREPARATION)
                 and record.get("Open_sketch") is True
                 and record.get("closed_proof") is False
                 and record.get("creates_campaign_proposal") is False,
                 "AP19 durable graph publication identity differs")
    for field in ("submission_id",):
        if field in record:
            offline.need(isinstance(record[field], str) and bool(record[field]),
                         "AP19 durable " + field + " is not a nonempty string")
    for mapping in ("publish_jobs", "child_ids"):
        if mapping in record:
            offline.need(isinstance(record[mapping], dict)
                         and all(k in pins["child_names"] and isinstance(v, str) and v
                                 for k, v in record[mapping].items()),
                         "AP19 durable " + mapping + " differs")

    spec = importlib.util.spec_from_file_location("p2m_ap19_analytic_graph", offline.API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = None

    def request(method, path, **kwargs):
        nonlocal token
        current = descriptor()
        offline.need(current[:3] == (manifest, payloads, pins)
                     and ONLINE.read_bytes() == offline.encode(current[3]),
                     "AP19 frozen request inputs changed before HTTP")
        if token is None:
            token = api.get_token()
        status, raw = api._request(method, path, token=token, **kwargs)
        after = descriptor()
        offline.need(after[:3] == (manifest, payloads, pins)
                     and ONLINE.read_bytes() == offline.encode(after[3]),
                     "AP19 frozen request inputs changed after HTTP")
        try:
            body = json.loads(raw)
        except json.JSONDecodeError:
            body = {"raw_body": raw}
        return status, raw, body

    def evidence(status, raw, body):
        return {"http_status": status, "raw_body_utf8": raw,
                "raw_body_sha256": offline.sha_bytes(raw.encode("utf-8")), "body": body}

    def exact_theorem(theorem_id, expected_problem, label, statuses):
        status, raw, body = request("GET", "/theorems/" + quote(theorem_id, safe=""))
        record[label] = evidence(status, raw, body)
        save(record)
        offline.need(status == 200 and body.get("theorem_id") == theorem_id
                     and body.get("theorem_name") == expected_problem["theorem_name"]
                     and body.get("preamble") == expected_problem["preamble"]
                     and body.get("formal_statement") == expected_problem["formal_statement"]
                     and body.get("mathlib_rev") == pins["environment"]
                     and body.get("visibility") == "public"
                     and body.get("deprecated_at") is None
                     and body.get("status") in statuses,
                     "AP19 exact public theorem readback differs: "
                     + expected_problem["theorem_name"])
        return body

    save(record)
    if not record.get("child_ids") and not record.get("publish_intent"):
        found, lookups = {}, {}
        for problem in problems:
            pages, matches, offset = [], [], 0
            while True:
                route = ("/theorems?theorem_name=" + quote(problem["theorem_name"])
                         + "&env=" + pins["environment"]
                         + "&limit=100&offset=" + str(offset))
                status, raw, body = request("GET", route)
                offline.need(status == 200 and isinstance(body.get("theorems"), list)
                             and type(body.get("total")) is int and body["total"] >= 0,
                             "AP19 fresh exact child-name query failed")
                page = body["theorems"]
                pages.append({"route": route, **evidence(status, raw, body)})
                matches.extend(row for row in page
                               if row.get("theorem_name") == problem["theorem_name"]
                               and row.get("mathlib_rev") == pins["environment"])
                offset += len(page)
                if offset >= body["total"]:
                    break
                offline.need(bool(page), "AP19 exact child pagination ended early")
            offline.need(len(matches) <= 1, "AP19 duplicate exact child name exists")
            lookups[problem["theorem_name"]] = {"pages": pages, "matches": matches}
            if matches:
                theorem_id = matches[0].get("theorem_id")
                offline.need(isinstance(theorem_id, str) and theorem_id,
                             "AP19 exact child match lacks theorem ID")
                exact_theorem(theorem_id, problem,
                              "preexisting_child_readback_" + problem["theorem_name"], {"Open"})
                found[problem["theorem_name"]] = theorem_id
        record["fresh_exact_child_name_lookups"] = lookups
        save(record)
        offline.need(len(found) in {0, len(problems)},
                     "AP19 only part of the exact child batch already exists")
        if len(found) == len(problems):
            record["child_ids"] = found
            record["reused_exact_existing_Open_children"] = True
            save(record)
        else:
            status, raw, environments = request("GET", "/environments")
            record["environment_readback"] = evidence(status, raw, environments)
            save(record)
            offline.need(status == 200 and any(
                row.get("mathlib_rev") == pins["environment"]
                and row.get("toolchain") == TOOLCHAIN
                for row in environments.get("environments", [])),
                "AP19 pinned environment unavailable; no child POST sent")
            record["publish_intent"] = {
                "at_utc": datetime.now(timezone.utc).isoformat(),
                "endpoint": "/submit-problem", "problem_names": pins["child_names"],
                "environment": pins["environment"], "visibility": "public",
                "payload_sha256": pins["payload_sha256"]["publish-payload.json"]}
            save(record)
            status, raw, body = request("POST", "/submit-problem",
                                        raw_body=payloads["publish-payload.json"],
                                        ctype="application/json")
            record["publish_response"] = evidence(status, raw, body)
            jobs = body.get("jobs", [])
            if status == 202 and not body.get("errors") and len(jobs) == len(problems):
                offline.need({row.get("name") for row in jobs} == set(pins["child_names"]),
                             "AP19 child POST response names differ")
                mapped = {}
                for row in jobs:
                    job_id = row.get("job_id")
                    offline.need(isinstance(job_id, str) and job_id,
                                 "AP19 child POST response lacks a nonempty job ID")
                    mapped[row["name"]] = job_id
                offline.need(len(mapped) == len(problems), "AP19 child POST jobs are not unique")
                record["publish_jobs"] = mapped
            save(record)
            offline.need(len(record.get("publish_jobs", {})) == len(problems),
                         "AP19 child POST is uncertain; intent is durable and POST must not repeat")
            return record

    if not record.get("child_ids"):
        offline.need(record.get("publish_intent")
                     and len(record.get("publish_jobs", {})) == len(problems),
                     "AP19 durable child POST intent lacks known jobs; do not repeat POST")
        published = dict(record.get("published_child_ids", {}))
        verdicts = {}
        for name in pins["child_names"]:
            job_id = record["publish_jobs"][name]
            status, raw, body = request("GET", "/publish-jobs/" + quote(job_id, safe=""))
            verdicts[name] = evidence(status, raw, body)
            offline.need(status == 200 and isinstance(body.get("id"), str)
                         and body["id"] == job_id and body.get("kind") == "problem"
                         and body.get("theorem_name") == name
                         and body.get("status") in PUBLISH_STATES
                         and ("job_id" not in body or body["job_id"] == job_id),
                         "AP19 publish job id/kind/name/state differs: " + name)
            if body["status"] == "PUBLISHED":
                theorem_id = body.get("theorem_id")
                offline.need(isinstance(theorem_id, str) and theorem_id,
                             "AP19 Published child job lacks theorem ID")
                published[name] = theorem_id
        record["last_publish_verdicts"] = verdicts
        record["published_child_ids"] = published
        if len(published) == len(problems):
            record["child_ids"] = published
        save(record)
        if not record.get("child_ids"):
            return record

    child_readback_sha = {}
    for problem in problems:
        name = problem["theorem_name"]
        theorem_id = record["child_ids"].get(name)
        offline.need(isinstance(theorem_id, str) and theorem_id,
                     "AP19 saved child theorem ID differs: " + name)
        body = exact_theorem(theorem_id, problem, "current_child_readback_" + name, {"Open"})
        path = PUB / "child-readbacks" / (name.rsplit(".", 1)[1] + ".json")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(offline.encode(body))
        child_readback_sha[name] = {"path": offline.stage.rel(path),
                                    "sha256": offline.sha(path),
                                    "theorem_id": theorem_id, "status": "Open"}
    record["exact_child_readbacks"] = child_readback_sha
    save(record)

    parent_problem = {"theorem_name": manifest["parent_theorem_name"],
                      "preamble": manifest["parent_preamble"],
                      "formal_statement": manifest["parent_formal_statement"]}
    parent = exact_theorem(pins["parent_theorem_id"], parent_problem,
                           "pre_verify_parent_readback", {"Open"})
    if not record.get("verify_intent"):
        record["verify_intent"] = {
            "at_utc": datetime.now(timezone.utc).isoformat(), "endpoint": "/verify",
            "theorem_id": pins["parent_theorem_id"],
            "multipart_sha256": pins["payload_sha256"]["verification-request.multipart"],
            "content_type": pins["multipart_content_type"],
            "solution_sha256": offline.read(PUB / "verification-payload.json")["file"]["sha256"]}
        save(record)
        status, raw, body = request("POST", "/verify",
                                    raw_body=payloads["verification-request.multipart"],
                                    ctype=pins["multipart_content_type"])
        record["verify_response"] = evidence(status, raw, body)
        if status in (200, 202) and body.get("status") in VERIFY_STATES:
            submission_id = body.get("submission_id") or body.get("id")
            offline.need(isinstance(submission_id, str) and submission_id,
                         "AP19 verify response lacks a nonempty submission ID")
            record["submission_id"] = submission_id
        save(record)
        offline.need(record.get("submission_id"),
                     "AP19 verify POST is uncertain; intent is durable and POST must not repeat")
        if body.get("status") != "SKETCH_ACCEPTED":
            return record
    else:
        offline.need(record.get("submission_id"),
                     "AP19 verify intent lacks known submission; do not repeat POST")
        status, raw, body = request(
            "GET", "/verify?submission_id=" + quote(record["submission_id"], safe=""))
        record["last_verify_verdict"] = evidence(status, raw, body)
        save(record)
        returned_id = body.get("submission_id") or body.get("id")
        offline.need(status == 200 and body.get("theorem_id") == pins["parent_theorem_id"]
                     and body.get("status") in VERIFY_STATES
                     and isinstance(returned_id, str) and bool(returned_id)
                     and returned_id == record["submission_id"],
                     "AP19 known verify submission identity/status differs")
        if body["status"] != "SKETCH_ACCEPTED":
            return record

    post_parent = exact_theorem(pins["parent_theorem_id"], parent_problem,
                                "post_SKETCH_ACCEPTED_parent_readback", {"Open"})
    status, raw, graph = request(
        "GET", "/theorems/" + quote(pins["parent_theorem_id"], safe="") + "/graph")
    graph_evidence = evidence(status, raw, graph)
    offline.need(status == 200 and graph.get("root_id") == pins["parent_theorem_id"],
                 "AP19 refreshed parent graph differs")
    status, raw, decompositions = request(
        "GET", "/theorems/" + quote(pins["parent_theorem_id"], safe="") + "/decompositions")
    decomp_evidence = evidence(status, raw, decompositions)
    offline.need(status == 200 and isinstance(decompositions.get("decompositions"), list),
                 "AP19 refreshed parent decompositions differ")
    sketch = "sketch-" + record["submission_id"]
    edges = {(row.get("source"), row.get("target"), row.get("kind"))
             for row in graph.get("edges", [])}
    child_ids = set(record["child_ids"].values())
    offline.need((sketch, pins["parent_theorem_id"], "sketch") in edges
                 and all((theorem_id, sketch, "sketch") in edges for theorem_id in child_ids),
                 "AP19 refreshed graph lacks one of the two actual Open child edges")
    rows = [row for row in decompositions["decompositions"]
            if row.get("submission_id") == record["submission_id"]]
    offline.need(len(rows) == 1 and rows[0].get("deprecated_at") is None,
                 "AP19 refreshed decomposition lacks the actual sketch submission")
    theorem_children = [row for row in rows[0].get("children", []) if row.get("theorem_id")]
    offline.need(len(theorem_children) == 2
                 and {row["theorem_id"] for row in theorem_children} == child_ids
                 and all(row.get("status") == "Open" and row.get("deprecated_at") is None
                         and row.get("mathlib_rev") == pins["environment"]
                         for row in theorem_children),
                 "AP19 decomposition does not contain exactly the two actual Open children")
    artifacts = {"post-parent-target.json": post_parent,
                 "post-graph.json": graph, "post-decompositions.json": decompositions}
    for name, value in artifacts.items():
        (PUB / name).write_bytes(offline.encode(value))
    raw_artifacts = {"post-graph.raw.json": graph_evidence["raw_body_utf8"],
                     "post-decompositions.raw.json": decomp_evidence["raw_body_utf8"]}
    for name, value in raw_artifacts.items():
        (PUB / name).write_bytes(value.encode("utf-8"))
    record["post_acceptance_readback_sha256"] = {
        name: offline.sha(PUB / name) for name in [*artifacts, *raw_artifacts]}
    record["actual_two_Open_child_edges"] = {
        "sketch_node": sketch, "child_ids": record["child_ids"],
        "two_child_edges": True, "sketch_to_parent": True,
        "graph_nodes": len(graph.get("nodes", [])),
        "graph_edges": len(graph.get("edges", []))}
    record["confirmed_SKETCH_ACCEPTED"] = True
    record["count_as_own_Accepted_proof"] = False
    save(record)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--adopt-known-terminal", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        manifest, payloads, pins, value = descriptor()
        offline.exact(ONLINE, offline.encode(value))
        result = {"prepared": True, "network_used": False,
                  "strict_replay_reused_by_hash": True,
                  "Open_sketch": True, "closed_proof": False,
                  "payload_sha256": pins["payload_sha256"], "proposal_status": "Draft"}
    elif args.adopt_known_terminal:
        record = adopt_known_terminal()
        result = {"adopted": True, "network_used": False, "API_used": False,
                  "source_terminal_record_sha256": record["source_terminal_record_sha256"],
                  "submission_id": record["submission_id"],
                  "confirmed_SKETCH_ACCEPTED": True,
                  "count_as_own_Accepted_proof": False}
    else:
        record = advance()
        result = {"advanced": True,
                  "parent_theorem_id": record.get("parent_theorem_id"),
                  "child_ids": record.get("child_ids"),
                  "publish_jobs": record.get("publish_jobs"),
                  "submission_id": record.get("submission_id"),
                  "confirmed_SKETCH_ACCEPTED": record.get("confirmed_SKETCH_ACCEPTED", False),
                  "count_as_own_Accepted_proof": False}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
