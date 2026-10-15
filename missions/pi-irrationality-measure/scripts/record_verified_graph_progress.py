"""Record verified server graph connections separately from accepted leaf proofs."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
V = TASK / "verification"
sources = [
    ("campaign_epsilon_half_bridge", V / "graph-bridge-20261011/three-context-v2/verification-publication/publication.json"),
    ("source_main_three_parent_reduction", V / "graph-source-root-20261011/publication-v2/publication.json"),
    ("conditional_A1_NoFixedData_reduction", V / "graph-conditional-route-20261011-v2/publication-v3/publication.json"),
    ("NoFixedData_five_child_reduction", V / "graph-no-fixed-data-route-20261011-v2/publication-v3/publication.json"),
    ("analyticAggregate_two_child_reduction", V / "ap19/analytic-aggregate-two-child-reduction-final/publication-v3/publication.json")]
connections, pending = [], []
for label, path in sources:
    if not path.exists():
        continue
    record = json.loads(path.read_bytes())
    accepted = record.get("confirmed_SKETCH_ACCEPTED") is True
    entry = {"label": label, "publication_record": path.relative_to(TASK).as_posix(),
             "publication_record_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
             "submission_id": record.get("submission_id"),
             "root_id": record.get("root_id", record.get("target_theorem_id", record.get("conditional_theorem_id", record.get("NoFixedData_theorem_id", record.get("parent_theorem_id"))))),
             "verdict": record.get("last_verify_verdict", {}).get("body", {}).get("status"),
             "actual_edge_confirmation": record.get("actual_three_parent_edges", record.get("actual_five_child_edges", record.get("actual_two_child_edges", record.get("actual_parent_edge", record.get("actual_two_Open_child_edges"))))),
             "actual_root_transitive_paths": record.get("actual_root_transitive_paths"),
             "open_reduction_is_not_a_closed_final_proof": True}
    if accepted:
        if entry["verdict"] != "SKETCH_ACCEPTED" or not entry["actual_edge_confirmation"]:
            raise ValueError("Verified graph connection lacks its actual server verdict/edges")
        connections.append(entry)
    else:
        entry["known_publish_jobs"] = record.get("publish_jobs", {})
        if record.get("publish_job_id"):
            entry["known_publish_jobs"]["NoFixedData"] = record["publish_job_id"]
        if record.get("arithmetic_publish_job_id"):
            entry["known_publish_jobs"]["arithmetic_source017"] = record["arithmetic_publish_job_id"]
        entry["publish_statuses"] = {name: row["body"]["status"] for name, row in record.get("last_publish_verdicts", {}).items()}
        pending.append(entry)

# This one durable publication contains two independently verified sketches.
# Its absence, or an intent without a real job/submission identity, adds no count.
AP20_PUBLICATION = V / "ap20/analytic-translated-two-layer-reduction-final-v3/publication-v4/publication.json"
LITERAL = "OAI.PiExponent.LiteralAnalytic."
AP20_PARENTS = {"norm": LITERAL + "norm_actual_summand_le",
                "actual": LITERAL + "actual_minor_analytic_bound"}
AP20_CHILDREN = {
    "norm": [LITERAL + name for name in ["indexWeight_nonneg", "rowWeight_le_indexWeight_of_ne_zero",
        "sum_rowWeight_eq", "low_transverse_capacity", "lowIndexCount_pos", "norm_scalar_product_le",
        "norm_choiceMatrix_le"]] + ["OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound"],
    "actual": [LITERAL + name for name in ["actual_minor_expansion", "card_choiceFamily_le",
        "actualRowCount_pos", "norm_actual_summand_le"]] + ["OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le"]}
AP20_PROVED_CHILD_IDS = {
    "OAI.PiExponent.DeterminantAnalyticBound.translated_summand_bound": "4340823c-de0b-446e-9161-c7ddd0bcb17a",
    "OAI.PiExponent.DeterminantAnalyticBound.log_norm_sum_le": "10a08e49-5f89-4055-a254-59882a447190"}
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def nonempty_id(value):
    return isinstance(value, str) and bool(value)


if AP20_PUBLICATION.exists():
    raw = AP20_PUBLICATION.read_bytes()
    record = json.loads(raw)
    require(record.get("artifact_kind") == "ap20-analytic-translated-two-layer-durable-publication"
            and record.get("environment") == ENV and record.get("visibility") == "public"
            and record.get("count_as_own_Accepted_proof") is False,
            "Two-layer graph publication identity differs")
    for key, parent in AP20_PARENTS.items():
        sketch = record.get("sketches", {}).get(key, {})
        batch = record.get("batches", {}).get(key, {})
        jobs = batch.get("publish_jobs", {})
        submission_id = sketch.get("submission_id")
        parent_id = record.get("theorem_ids", {}).get(parent)
        if not (nonempty_id(submission_id) or (sketch and nonempty_id(parent_id))
                or any(nonempty_id(value) for value in jobs.values())):
            continue
        require(not sketch or sketch.get("parent_name") == parent,
                "Two-layer sketch parent identity differs")
        verdict = sketch.get("last_verify_verdict", {})
        evidence = sketch.get("post_acceptance_graph_evidence", {})
        entry = {"label": "analytic_translated_" + key + "_reduction",
            "publication_record": AP20_PUBLICATION.relative_to(TASK).as_posix(),
            "publication_record_sha256": hashlib.sha256(raw).hexdigest(),
            "publication_sketch_key": key, "submission_id": submission_id,
            "root_id": parent_id, "root_name": parent,
            "verdict": verdict.get("body", {}).get("status"),
            "actual_edge_confirmation": evidence,
            "open_reduction_is_not_a_closed_final_proof": True}
        confirmed = (sketch.get("confirmed_SKETCH_ACCEPTED_and_graph") is True
                     and entry["verdict"] == "SKETCH_ACCEPTED" and evidence.get("confirmed") is True)
        if confirmed:
            body = verdict.get("body", {})
            children = evidence.get("actual_child_ids", {})
            require(nonempty_id(submission_id) and nonempty_id(parent_id)
                    and verdict.get("http_status") == 200 and body.get("id") == submission_id
                    and body.get("theorem_id") == parent_id
                    and (key != "actual" or parent_id == "a08a3f36-e4a6-4a12-a77b-53e5c07f6ac9")
                    and ("submission_id" not in body or body["submission_id"] == submission_id)
                    and set(children) == set(AP20_CHILDREN[key])
                    and len(set(children.values())) == len(children)
                    and all(nonempty_id(value) for value in children.values())
                    and evidence.get("actual_edge_count") == len(children)
                    and sketch.get("verify_intent", {}).get("parent_name") == parent
                    and sketch.get("verify_intent", {}).get("theorem_id") == parent_id
                    and sketch.get("verify_intent", {}).get("expected_child_ids") == children,
                    "Confirmed sketch lacks its exact actual submission/child identity")
            for name, child_id in children.items():
                expected = AP20_PROVED_CHILD_IDS.get(name, record.get("theorem_ids", {}).get(name))
                require(child_id == expected, "Actual sketch child ID differs: " + name)
            graph_path = AP20_PUBLICATION.parent / (key + "-post-graph.json")
            decomp_path = AP20_PUBLICATION.parent / (key + "-post-decompositions.json")
            require(hashlib.sha256(graph_path.read_bytes()).hexdigest() == evidence.get("graph_sha256")
                    and hashlib.sha256(decomp_path.read_bytes()).hexdigest() == evidence.get("decompositions_sha256"),
                    "Actual graph/decomposition evidence changed")
            graph = json.loads(graph_path.read_bytes())
            decomposition = json.loads(decomp_path.read_bytes())
            edges = {(row.get("source"), row.get("target"), row.get("kind"))
                     for row in graph.get("edges", [])}
            sketch_id = "sketch-" + submission_id
            require(graph.get("root_id") == parent_id and (sketch_id, parent_id, "sketch") in edges
                    and all((child_id, sketch_id, "sketch") in edges for child_id in children.values()),
                    "Persisted server graph lacks an expected actual sketch edge")
            rows = [row for row in decomposition.get("decompositions", [])
                    if row.get("submission_id") == submission_id]
            require(len(rows) == 1 and rows[0].get("deprecated_at") is None,
                    "Persisted actual decomposition identity differs")
            child_rows = [row for row in rows[0].get("children", []) if row.get("theorem_id")]
            by_id = {row["theorem_id"]: row for row in child_rows}
            require(len(child_rows) == len(children) and set(by_id) == set(children.values())
                    and all(by_id[child_id].get("status") ==
                            ("Proved" if name in AP20_PROVED_CHILD_IDS else "Open")
                            and by_id[child_id].get("mathlib_rev") == ENV
                            and by_id[child_id].get("deprecated_at") is None
                            for name, child_id in children.items()),
                    "Persisted actual decomposition children/statuses differ")
            entry["actual_child_ids"] = children
            entry["actual_edge_count"] = len(children)
            entry["persisted_graph_and_decomposition_rechecked"] = True
            connections.append(entry)
        else:
            entry["known_publish_jobs"] = {name: value for name, value in jobs.items() if nonempty_id(value)}
            entry["publish_statuses"] = {name: row.get("body", {}).get("status")
                for name, row in batch.get("last_publish_verdicts", {}).items()}
            pending.append(entry)

two_layer_complete = all("analytic_translated_" + key + "_reduction" in
                         {row["label"] for row in connections} for key in AP20_PARENTS)
proof_checkpoint = json.loads((V / "verified-stage-progress.json").read_bytes())
own_proved_ids = {row["theorem_id"] for row in proof_checkpoint["proofs"]}
next_leaves = ([name for key in AP20_PARENTS for name in AP20_CHILDREN[key]
               if name not in AP20_PROVED_CHILD_IDS and name != AP20_PARENTS["norm"]
               and record["theorem_ids"][name] not in own_proved_ids]
              if two_layer_complete else [])
next_frontier = next_leaves + [LITERAL + "tendsto_analyticRemainder"] if two_layer_complete else []
report = {"updated_at_utc": datetime.now(timezone.utc).isoformat(), "verified_connection_count": len(connections),
          "connections": connections, "pending_connections": pending,
          "final_platform_dependency_closure_complete": False,
          "proof_checkpoint": "verification/verified-stage-progress.json",
          "AP20_two_independent_sketch_connections_complete": two_layer_complete,
          "next_Open_leaf_count": len(next_leaves) if two_layer_complete else None,
          "next_frontier": next_frontier,
          "next_actual_source_dependency":
              str(len(next_leaves)) + " source-faithful Open leaves and LiteralAnalytic.tendsto_analyticRemainder"
              if two_layer_complete else
              "verification/ap20/analytic-translated-two-layer-reduction-final-v3/preparation.json"}
dest = V / "verified-graph-progress.json"
dest.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
state_path = V / "run-state.json"
state = json.loads(state_path.read_bytes())
state["verified_graph_progress"] = dest.relative_to(TASK).as_posix()
state["verified_graph_progress_sha256"] = hashlib.sha256(dest.read_bytes()).hexdigest()
state["verified_graph_connection_count"] = len(connections)
state_path.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"verified_connection_count": len(connections), "pending_connection_count": len(pending)}))
