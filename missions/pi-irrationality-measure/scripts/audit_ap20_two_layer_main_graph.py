"""Confirm AP20's accepted analytic reductions on both freshly returned root graphs."""
import argparse
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
PUBLICATION = TASK / "verification/ap20/analytic-translated-two-layer-reduction-final-v3/publication-v4/publication.json"
ROOTS = ["406736ed-98ce-4177-b97f-24de96ba4188", "e717eef2-11b1-4b14-9789-65f52c0502e1"]


def need(condition, message):
    if not condition:
        raise ValueError(message)


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("refresh_directory")
args = parser.parse_args()
directory = (TASK / args.refresh_directory).resolve()
need(directory.is_relative_to(TASK / "verification"), "Refresh directory escapes current mission")
record = json.loads(PUBLICATION.read_bytes())
need(record.get("confirmed_two_SKETCH_ACCEPTED_with_actual_graphs") is True,
     "Both actual server sketch connections must be confirmed first")
results = []
for root in ROOTS:
    file = directory / (root + "-graph.json")
    graph = json.loads(file.read_bytes())
    need(graph.get("root_id") == root, "Actual root graph identity differs")
    nodes = {row.get("theorem_id") or row.get("id") or row.get("node_id") for row in graph["nodes"]}
    edges = {(row["source"], row["target"], row.get("kind")) for row in graph["edges"]}
    predecessors = {}
    for source, target, kind in edges:
        predecessors.setdefault(target, set()).add(source)
    ancestors, stack = set(), [root]
    while stack:
        item = stack.pop()
        if item in ancestors:
            continue
        ancestors.add(item)
        stack.extend(predecessors.get(item, []))
    sketches = []
    for key in ["norm", "actual"]:
        state = record["sketches"][key]
        need(state.get("confirmed_SKETCH_ACCEPTED_and_graph") is True
             and state["last_verify_verdict"]["body"]["status"] == "SKETCH_ACCEPTED",
             "Actual accepted sketch verdict differs")
        parent = state["verify_intent"]["theorem_id"]
        sketch = "sketch-" + state["submission_id"]
        children = state["post_acceptance_graph_evidence"]["actual_child_ids"]
        need(parent in nodes and sketch in nodes and parent in ancestors and sketch in ancestors,
             "Accepted AP20 reduction is absent from this returned main graph: " + key)
        need((sketch, parent, "sketch") in edges
             and all((child, sketch, "sketch") in edges and child in ancestors
                     for child in children.values()),
             "An expected AP20 child edge is absent from this returned main graph: " + key)
        sketches.append({"key": key, "parent_id": parent, "submission_id": state["submission_id"],
                         "actual_child_ids": children, "all_child_edges_confirmed": True,
                         "on_returned_child_to_root_paths": True})
    results.append({"root_id": root, "nodes": len(graph["nodes"]), "edges": len(graph["edges"]),
                    "graph_sha256": hashlib.sha256(file.read_bytes()).hexdigest(), "sketches": sketches,
                    "translated_summand_bound_on_returned_path": "4340823c-de0b-446e-9161-c7ddd0bcb17a" in ancestors})
output = directory / "ap20-two-layer-connected-main.json"
need(not output.exists(), "Preserve historical audit; output already exists")
report = {"read_only": True, "API_used": False,
          "publication_record": PUBLICATION.relative_to(TASK).as_posix(),
          "publication_record_sha256": hashlib.sha256(PUBLICATION.read_bytes()).hexdigest(),
          "both_new_sketches_on_both_returned_main_graphs": True, "roots": results,
          "final_platform_dependency_closure_complete": False}
output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"report": output.relative_to(TASK).as_posix(), "roots": [
    {key: row[key] for key in ["root_id", "nodes", "edges", "translated_summand_bound_on_returned_path"]}
    for row in results]}))
