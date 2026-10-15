"""Durably publish AP20's eleven interfaces and verify its two Open sketches.

The order is fixed: publish the norm parent and its seven children, verify that
sketch, publish the three remaining actual-minor children, then verify the
existing actual-minor target.  Every HTTP call is surrounded by the frozen
offline hash gate.  Unknown POST outcomes are never retried.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
from urllib.parse import quote

import prepare_analytic_translated_two_layer_publication_v2 as offline


SELF = Path(__file__).resolve()
PUB = offline.DEST
ONLINE = PUB / "online-preparation-graph.json"
RECORD = PUB / "publication.json"
ENV = offline.ENV
TOOLCHAIN = "leanprover/lean4:v4.33.1"
PUBLISH_STATES = {"PENDING", "COMPILING", "PUBLISHED", "FAILED", "ERROR"}
VERIFY_STATES = {"PENDING", "COMPILING", "SKETCH_ACCEPTED", "CE", "WA",
                 "SORRY", "FAILED", "ERROR"}


def descriptor():
    manifest, payloads, pins = offline.frozen()
    offline.need(offline.sha(SELF) == pins["online_wrapper_sha256"],
                 "AP20 two-layer online wrapper hash differs")
    value = {"schema_version": 1,
        "artifact_kind": "ap20-analytic-translated-two-layer-fast-online-preparation",
        "new_node_names": pins["new_node_names"],
        "norm_batch_names": pins["norm_batch_names"],
        "actual_batch_names": pins["actual_batch_names"],
        "existing_actual_parent_id": pins["existing_actual_parent_id"],
        "environment": pins["environment"],
        "full_strict_replay_preparation_sha256": offline.sha(PUB / "preparation.json"),
        "full_strict_replay_validation_sha256": pins["validation_sha256"],
        "online_wrapper_sha256": offline.sha(SELF),
        "manifest_sha256": offline.sha(PUB / "manifest.json"),
        "payload_sha256": pins["payload_sha256"],
        "publication_phases": manifest["publication_sequence"],
        "fresh_exact_name_environment_check_before_each_batch": True,
        "known_jobs_and_submissions_polled_without_reposting": True,
        "hash_gate_before_and_after_every_HTTP": True,
        "actual_graph_and_decomposition_required_after_each_SKETCH_ACCEPTED": True,
        "count_as_own_Accepted_proof": False,
        "network_used": False, "API_used": False,
        "submission_ready": False, "proposal_status": "Draft"}
    return manifest, payloads, pins, value


def save(record):
    record["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
    RECORD.write_bytes(offline.encode(record))


def dynamic_evidence_gate(record):
    for key, sketch in record.get("sketches", {}).items():
        if sketch.get("verify_intent"):
            path = PUB / ("verification-" + key + ".multipart")
            offline.need(path.is_file()
                         and offline.sha(path) == sketch["verify_intent"]["multipart_sha256"],
                         "Durable sketch multipart changed: " + key)


def advance():
    manifest, payloads, pins, expected = descriptor()
    offline.need(ONLINE.is_file() and ONLINE.read_bytes() == offline.encode(expected),
                 "Reviewed AP20 two-layer online descriptor differs")
    problems = {}
    for payload_name in ("publish-norm-batch.json", "publish-actual-siblings-batch.json"):
        for row in json.loads(payloads[payload_name])["problems"]:
            problems[row["theorem_name"]] = row
    verify_descriptors = {
        "norm": json.loads(payloads["verify-norm.json"]),
        "actual": json.loads(payloads["verify-actual.json"]),
    }
    record = offline.read(RECORD) if RECORD.exists() else {
        "artifact_kind": "ap20-analytic-translated-two-layer-durable-publication",
        "environment": ENV, "visibility": "public", "proposal_status": "Draft",
        "preparation_sha256": offline.sha(PUB / "preparation.json"),
        "theorem_ids": {offline.stage.ACTUAL: pins["existing_actual_parent_id"]},
        "batches": {}, "sketches": {},
        "count_as_own_Accepted_proof": False,
    }
    offline.need(record.get("artifact_kind") ==
                     "ap20-analytic-translated-two-layer-durable-publication"
                 and record.get("environment") == ENV
                 and record.get("visibility") == "public"
                 and record.get("preparation_sha256") == offline.sha(PUB / "preparation.json")
                 and record.get("theorem_ids", {}).get(offline.stage.ACTUAL) ==
                     pins["existing_actual_parent_id"]
                 and record.get("count_as_own_Accepted_proof") is False,
                 "Durable two-layer graph identity differs")
    dynamic_evidence_gate(record)

    spec = importlib.util.spec_from_file_location("p2m_ap20_two_layer_v2", offline.API)
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    token = None

    def request(method, path, **kwargs):
        nonlocal token
        dynamic_evidence_gate(record)
        current = descriptor()
        offline.need(current[0] == manifest and current[1] == payloads
                     and current[2] == pins
                     and ONLINE.read_bytes() == offline.encode(current[3]),
                     "Frozen two-layer inputs changed before HTTP")
        if token is None:
            token = api.get_token()
        status, raw = api._request(method, path, token=token, **kwargs)
        dynamic_evidence_gate(record)
        after = descriptor()
        offline.need(after[0] == manifest and after[1] == payloads
                     and after[2] == pins
                     and ONLINE.read_bytes() == offline.encode(after[3]),
                     "Frozen two-layer inputs changed after HTTP")
        try:
            body = json.loads(raw)
        except json.JSONDecodeError:
            body = {"raw_body": raw}
        return status, raw, body

    def evidence(status, raw, body):
        return {"http_status": status, "raw_body_utf8": raw,
                "raw_body_sha256": offline.sha_bytes(raw.encode("utf-8")), "body": body}

    def exact_theorem(name, theorem_id, problem, statuses, label):
        status, raw, body = request("GET", "/theorems/" + quote(theorem_id, safe=""))
        record.setdefault("readbacks", {})[label] = evidence(status, raw, body)
        save(record)
        offline.need(status == 200 and body.get("theorem_id") == theorem_id
                     and body.get("theorem_name") == name
                     and body.get("mathlib_rev") == ENV
                     and body.get("visibility") == "public"
                     and body.get("deprecated_at") is None
                     and body.get("preamble") == problem["preamble"]
                     and body.get("formal_statement") == problem["formal_statement"]
                     and body.get("status") in statuses,
                     "Exact public theorem readback differs: " + name)
        return body

    def query_exact(name):
        pages, matches, offset = [], [], 0
        while True:
            route = ("/theorems?theorem_name=" + quote(name) + "&env=" + ENV
                     + "&limit=100&offset=" + str(offset))
            status, raw, body = request("GET", route)
            offline.need(status == 200 and isinstance(body.get("theorems"), list)
                         and type(body.get("total")) is int and body["total"] >= 0,
                         "Fresh exact-name query failed: " + name)
            page = body["theorems"]
            pages.append({"route": route, **evidence(status, raw, body)})
            matches.extend(row for row in page
                           if row.get("theorem_name") == name and row.get("mathlib_rev") == ENV)
            offset += len(page)
            if offset >= body["total"]: break
            offline.need(bool(page), "Exact-name pagination ended early: " + name)
        offline.need(len(matches) <= 1, "Exact theorem name is ambiguous: " + name)
        return pages, matches

    def batch_complete(key, names, payload_name):
        batches = record.setdefault("batches", {})
        batch = batches.get(key)
        if batch is None:
            lookups, found = {}, {}
            for name in names:
                pages, matches = query_exact(name)
                lookups[name] = {"pages": pages, "matches": matches}
                if matches:
                    theorem_id = matches[0].get("theorem_id")
                    offline.need(isinstance(theorem_id, str) and theorem_id,
                                 "Exact match lacks theorem ID: " + name)
                    found[name] = theorem_id
            offline.need(len(found) in {0, len(names)},
                         "Publication batch is only partially present; no POST sent: " + key)
            batch = {"names": names, "fresh_exact_name_lookups": lookups,
                     "theorem_ids": {}, "publish_jobs": {}}
            batches[key] = batch
            if found:
                for name, theorem_id in found.items():
                    exact_theorem(name, theorem_id, problems[name], {"Open"},
                                  key + "-adopt-" + name)
                batch["theorem_ids"] = found
                record["theorem_ids"].update(found)
                batch["reused_exact_existing_batch"] = True
                save(record)
                return True
            status, raw, environments = request("GET", "/environments")
            batch["environment_readback"] = evidence(status, raw, environments)
            save(record)
            offline.need(status == 200 and any(row.get("mathlib_rev") == ENV
                         and row.get("toolchain") == TOOLCHAIN
                         for row in environments.get("environments", [])),
                         "Pinned environment unavailable; no POST sent")
            raw_payload = payloads[payload_name]
            batch["publish_intent"] = {
                "at_utc": datetime.now(timezone.utc).isoformat(),
                "endpoint": "/submit-problem", "names": names,
                "payload_name": payload_name, "payload_sha256": offline.sha_bytes(raw_payload)}
            save(record)
            status, raw, body = request("POST", "/submit-problem",
                                        raw_body=raw_payload, ctype="application/json")
            batch["publish_response"] = evidence(status, raw, body)
            jobs = body.get("jobs", [])
            if status == 202 and not body.get("errors") and len(jobs) == len(names):
                mapped = {}
                for job in jobs:
                    name, job_id = job.get("name"), job.get("job_id")
                    offline.need(name in names and isinstance(job_id, str) and job_id
                                 and name not in mapped,
                                 "Problem POST job identity differs: " + key)
                    mapped[name] = job_id
                offline.need(set(mapped) == set(names), "Problem POST jobs are incomplete: " + key)
                batch["publish_jobs"] = mapped
            save(record)
            offline.need(len(batch["publish_jobs"]) == len(names),
                         "Problem POST uncertain; durable intent forbids replay: " + key)
            return False

        offline.need(batch.get("names") == names, "Durable publication batch domain differs")
        if len(batch.get("theorem_ids", {})) == len(names):
            record["theorem_ids"].update(batch["theorem_ids"])
            return True
        offline.need(batch.get("publish_intent") and len(batch.get("publish_jobs", {})) == len(names),
                     "Durable batch intent lacks known jobs; do not repeat POST")
        for name in names:
            if name in batch["theorem_ids"]: continue
            job_id = batch["publish_jobs"][name]
            status, raw, body = request("GET", "/publish-jobs/" + quote(job_id, safe=""))
            batch.setdefault("last_publish_verdicts", {})[name] = evidence(status, raw, body)
            save(record)
            offline.need(status == 200 and body.get("id") == job_id
                         and body.get("kind") == "problem"
                         and body.get("theorem_name") == name
                         and body.get("status") in PUBLISH_STATES
                         and ("job_id" not in body or body["job_id"] == job_id),
                         "Known publish job identity/state differs: " + name)
            if body["status"] == "PUBLISHED":
                theorem_id = body.get("theorem_id")
                offline.need(isinstance(theorem_id, str) and theorem_id,
                             "Published job lacks theorem ID: " + name)
                exact_theorem(name, theorem_id, problems[name], {"Open"},
                              key + "-published-" + name)
                batch["theorem_ids"][name] = theorem_id
                record["theorem_ids"][name] = theorem_id
                save(record)
        return len(batch["theorem_ids"]) == len(names)

    def boundary_problem(name):
        row = manifest["boundary_nodes"][name]
        return {"preamble": row["preamble"], "formal_statement": row["formal_statement"]}

    def parent_problem(parent):
        row = manifest["parent_wires"][parent]
        return {"preamble": row["preamble"], "formal_statement": row["formal_statement"]}

    def graph_evidence(parent, parent_id, submission_id, child_ids, child_statuses, key):
        status, raw, graph = request("GET", "/theorems/" + quote(parent_id, safe="") + "/graph")
        graph_record = evidence(status, raw, graph)
        offline.need(status == 200 and graph.get("root_id") == parent_id,
                     "Refreshed sketch graph differs: " + parent)
        status, raw, decompositions = request(
            "GET", "/theorems/" + quote(parent_id, safe="") + "/decompositions")
        decomp_record = evidence(status, raw, decompositions)
        offline.need(status == 200 and isinstance(decompositions.get("decompositions"), list),
                     "Refreshed decompositions differ: " + parent)
        sketch = "sketch-" + submission_id
        edges = {(row.get("source"), row.get("target"), row.get("kind"))
                 for row in graph.get("edges", [])}
        offline.need((sketch, parent_id, "sketch") in edges
                     and all((child_id, sketch, "sketch") in edges
                             for child_id in child_ids.values()),
                     "Actual sketch graph lacks an expected child edge: " + parent)
        rows = [row for row in decompositions["decompositions"]
                if row.get("submission_id") == submission_id]
        offline.need(len(rows) == 1 and rows[0].get("deprecated_at") is None,
                     "Actual decomposition row differs: " + parent)
        children = [row for row in rows[0].get("children", []) if row.get("theorem_id")]
        by_id = {row["theorem_id"]: row for row in children}
        offline.need(set(by_id) == set(child_ids.values())
                     and all(by_id[child_ids[name]].get("status") == child_statuses[name]
                             and by_id[child_ids[name]].get("deprecated_at") is None
                             and by_id[child_ids[name]].get("mathlib_rev") == ENV
                             for name in child_ids),
                     "Decomposition children/statuses differ: " + parent)
        for filename, value in {
            key + "-post-graph.json": graph,
            key + "-post-decompositions.json": decompositions,
        }.items():
            offline.exact(PUB / filename, offline.encode(value))
        for filename, value in {
            key + "-post-graph.raw.json": graph_record["raw_body_utf8"],
            key + "-post-decompositions.raw.json": decomp_record["raw_body_utf8"],
        }.items():
            offline.exact(PUB / filename, value.encode("utf-8"))
        return {"graph_sha256": offline.sha(PUB / (key + "-post-graph.json")),
                "decompositions_sha256": offline.sha(PUB / (key + "-post-decompositions.json")),
                "actual_child_ids": child_ids,
                "actual_edge_count": len(child_ids), "confirmed": True}

    def sketch_complete(key, parent, accepted_leaf):
        state = record.setdefault("sketches", {}).setdefault(key, {"parent_name": parent})
        if state.get("confirmed_SKETCH_ACCEPTED_and_graph"):
            return True
        parent_id = record["theorem_ids"][parent]
        expected_names = manifest["expected_graph_edges"][parent]
        child_ids, child_statuses = {}, {}
        for name in expected_names:
            if name == accepted_leaf:
                row = manifest["boundary_nodes"][name]
                theorem_id = row["theorem_id"]
                exact_theorem(name, theorem_id, boundary_problem(name), {"Proved"},
                              key + "-boundary-" + name)
                child_statuses[name] = "Proved"
            else:
                theorem_id = record["theorem_ids"][name]
                exact_theorem(name, theorem_id, problems[name], {"Open"},
                              key + "-child-" + name)
                child_statuses[name] = "Open"
            child_ids[name] = theorem_id
        exact_theorem(parent, parent_id, parent_problem(parent), {"Open"}, key + "-parent")

        if not state.get("submission_id"):
            offline.need(not state.get("verify_intent"),
                         "Uncertain sketch POST intent recorded; do not repeat: " + key)
            verify = verify_descriptors[key]
            payload, ctype = api._multipart(
                {"theorem_id": parent_id, "proof_type": verify["proof_type"],
                 "explanation": verify["explanation"]},
                {"file": (verify["file"]["filename"], verify["file"]["utf8"].encode("utf-8"))})
            multipart = PUB / ("verification-" + key + ".multipart")
            multipart.write_bytes(payload)
            state["verify_intent"] = {
                "at_utc": datetime.now(timezone.utc).isoformat(),
                "endpoint": "/verify", "parent_name": parent, "theorem_id": parent_id,
                "content_type": ctype, "multipart_sha256": offline.sha_bytes(payload),
                "solution_sha256": verify["file"]["sha256"],
                "descriptor_sha256": pins["payload_sha256"]["verify-" + key + ".json"],
                "expected_child_ids": child_ids}
            save(record)
            status, raw, body = request("POST", "/verify", raw_body=payload, ctype=ctype)
            state["verify_response"] = evidence(status, raw, body)
            submission_id = body.get("submission_id")
            if status in (200, 202) and body.get("status") in VERIFY_STATES:
                offline.need(isinstance(submission_id, str) and submission_id
                             and ("id" not in body or body["id"] == submission_id),
                             "Sketch POST response lacks exact submission ID: " + key)
                state["submission_id"] = submission_id
            save(record)
            offline.need(state.get("submission_id"),
                         "Sketch POST uncertain; durable intent forbids replay: " + key)
            return False

        submission_id = state["submission_id"]
        status, raw, body = request("GET", "/verify?submission_id=" + quote(submission_id, safe=""))
        state["last_verify_verdict"] = evidence(status, raw, body)
        save(record)
        returned_id = body.get("id")
        offline.need(status == 200 and body.get("theorem_id") == parent_id
                     and body.get("status") in VERIFY_STATES
                     and isinstance(returned_id, str) and returned_id == submission_id
                     and ("submission_id" not in body or body["submission_id"] == submission_id),
                     "Known sketch submission identity/status differs: " + key)
        if body["status"] != "SKETCH_ACCEPTED":
            return False
        evidence_row = graph_evidence(parent, parent_id, submission_id,
                                      child_ids, child_statuses, key)
        state["post_acceptance_graph_evidence"] = evidence_row
        state["confirmed_SKETCH_ACCEPTED_and_graph"] = True
        save(record)
        return True

    save(record)
    if not batch_complete("norm", manifest["norm_batch_names"], "publish-norm-batch.json"):
        return record
    if not sketch_complete("norm", offline.stage.NORM, offline.stage.route.TRANSLATED):
        return record
    if not batch_complete("actual", manifest["actual_batch_names"],
                          "publish-actual-siblings-batch.json"):
        return record
    if not sketch_complete("actual", offline.stage.ACTUAL, offline.stage.route.LOGSUM):
        return record
    record["confirmed_two_SKETCH_ACCEPTED_with_actual_graphs"] = True
    record["new_node_count"] = 11
    record["count_as_own_Accepted_proof"] = False
    save(record)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--prepare-only", action="store_true")
    modes.add_argument("--advance", action="store_true")
    args = parser.parse_args()
    if args.prepare_only:
        _, _, pins, value = descriptor()
        offline.exact(ONLINE, offline.encode(value))
        result = {"prepared": True, "network_used": False,
                  "strict_replay_reused_by_hash": True,
                  "new_node_count": 11, "Open_sketch_only": True,
                  "closed_proof": False, "payload_sha256": pins["payload_sha256"],
                  "proposal_status": "Draft"}
    else:
        record = advance()
        result = {"advanced": True,
                  "theorem_ids": record.get("theorem_ids"),
                  "batches": {k: {"theorem_ids": v.get("theorem_ids"),
                                   "publish_jobs": v.get("publish_jobs")}
                              for k, v in record.get("batches", {}).items()},
                  "sketches": {k: {"submission_id": v.get("submission_id"),
                                    "verify_status": v.get("last_verify_verdict", {}).get("body", {}).get("status"),
                                    "confirmed": v.get("confirmed_SKETCH_ACCEPTED_and_graph", False)}
                               for k, v in record.get("sketches", {}).items()},
                  "confirmed_two_SKETCH_ACCEPTED_with_actual_graphs":
                      record.get("confirmed_two_SKETCH_ACCEPTED_with_actual_graphs", False),
                  "count_as_own_Accepted_proof": False}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

