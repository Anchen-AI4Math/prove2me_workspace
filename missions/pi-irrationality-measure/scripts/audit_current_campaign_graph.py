"""Compare fresh actual graph paths with this migration's published checkpoint."""
import argparse
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("refresh_directory")
args = parser.parse_args()
stage = (TASK / args.refresh_directory).resolve()
if not stage.is_relative_to((TASK / "verification").resolve()):
    raise ValueError("Graph directory escapes current mission")
progress = json.loads((TASK / "verification/verified-stage-progress.json").read_bytes())
reports = []
for identifier in ["406736ed-98ce-4177-b97f-24de96ba4188", "e717eef2-11b1-4b14-9789-65f52c0502e1"]:
    path = stage / (identifier + "-graph.json")
    graph = json.loads(path.read_bytes())
    nodes = {n.get("theorem_id") or n.get("id") or n.get("node_id"): n for n in graph["nodes"]}
    # The server's direction is child -> reduction sketch -> parent.
    predecessors = {}
    for e in graph["edges"]:
        predecessors.setdefault(e["target"], set()).add(e["source"])
    ancestors, stack = set(), [identifier]
    while stack:
        current = stack.pop()
        if current in ancestors:
            continue
        ancestors.add(current)
        stack.extend(predecessors.get(current, []))
    entries = []
    for kind, rows, key in [("own_accepted_proof", progress["proofs"], "theorem_id"),
                             ("published_definition", progress["definitions"], "definition_id")]:
        for row in rows:
            item_id = row[key]
            entries.append({"kind": kind, "id": item_id,
                "name": row.get("theorem_name", row.get("definition_name")),
                "present_in_returned_graph": item_id in nodes,
                "verified_child_to_parent_path_in_returned_graph": item_id in ancestors})
    reports.append({"root_id": identifier, "nodes": len(graph["nodes"]), "edges": len(graph["edges"]),
        "response_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "truncation_fields": [{"id": key, "has_more_children": n.get("has_more_children"),
            "has_more_parents": n.get("has_more_parents"), "missing_children": n.get("missing_children", [])}
            for key, n in nodes.items() if n.get("has_more_children") or n.get("has_more_parents")],
        "own_proofs_on_verified_returned_paths": sum(e["kind"] == "own_accepted_proof" and
            e["verified_child_to_parent_path_in_returned_graph"] for e in entries),
        "definitions_on_verified_returned_paths": sum(e["kind"] == "published_definition" and
            e["verified_child_to_parent_path_in_returned_graph"] for e in entries), "checkpoint_items": entries})
report = {"schema_version": 1, "graph_updated_by_this_audit": False,
    "edge_direction": "child -> reduction submission -> parent",
    "progress_checkpoint_sha256": hashlib.sha256((TASK / "verification/verified-stage-progress.json").read_bytes()).hexdigest(),
    "published_definition_count": progress["definition_count"], "own_accepted_proof_count": progress["proof_count"],
    "roots": reports, "limitations": [
        "An absent item is not a confirmed connection in the returned graph. Truncated child branches require a deeper query.",
        "Published items and proposal reference ordering do not create proof edges.",
        "Only saved accepted reductions with actual server edge readbacks count as graph connections."]}
out = stage / "migration-graph-audit.json"
if out.exists():
    raise ValueError("Audit output already exists; preserve historical snapshot")
out.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
lines = ["# π 移植依赖图核对", "", "服务器依赖方向为：子项 → 归约提交 → 父项。", "",
         f"当前已发布 {progress['definition_count']} 个定义包；本次移植已有 {progress['proof_count']} 个自己的 Accepted/Proved 证明。",
         "独立上传不自动连到主根；本次只读核对不产生新边。", ""]
for r in reports:
    lines.extend([f"- 根 `{r['root_id']}`：返回 {r['nodes']} 节点 / {r['edges']} 边；返回的真实依赖路径确认包含本次 {r['own_proofs_on_verified_returned_paths']} 个证明、{r['definitions_on_verified_returned_paths']} 个定义包。"])
lines.extend(["", "未展开邻接项和各项连接状态逐项保存在 migration-graph-audit.json。",
    "当前两个最终根均 Open，尚不能称整个 graph 已闭合。",
    "归约的服务器回执与实际依赖边另见 verification/verified-graph-progress.json；计划边不计入已验证边。", ""])
(stage / "migration-graph-audit.md").write_text("\n".join(lines), encoding="utf-8")
print(json.dumps({"report": str(out), "roots": [{k: r[k] for k in ("root_id", "nodes", "edges",
    "own_proofs_on_verified_returned_paths", "definitions_on_verified_returned_paths")} for r in reports]}))
