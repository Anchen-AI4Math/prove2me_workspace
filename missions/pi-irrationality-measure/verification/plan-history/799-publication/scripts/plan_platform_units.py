"""Plan command-sized platform units from sanctioned Lean graph/AST facts.

The default refuses incomplete extraction. --preview computes a provisional
classification only; it never authorizes generation or publication.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
DEST = TASK / "verification"


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def closure(roots, graph, edge_fields):
    todo = list(roots)
    seen = set()
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        row = graph.get(name)
        if row:
            for field in edge_fields:
                todo.extend(row[field])
    return seen


def make_plan(inventory, rows):
    graph = {row["name"]: row for row in rows}
    targets = set(inventory["source_targets"])
    instances = {row["name"] for row in rows if row["isInstance"]}
    # Local instance attributes disappear when their source scope closes. The
    # oracle's actual instance commands supplement the environment instance bit.
    instances |= {name for module in inventory["modules"] for unit in module["units"]
                  if unit["is_instance_command"] for name in unit["graph_names"]}
    all_edges = ("typeDeps", "valueDeps", "constructors")
    reachable = closure(targets | instances, graph, all_edges)

    # Keeping part of a mutual/structure command regenerates every declaration
    # in that command. Include their dependencies before classification.
    while True:
        atomic_roots = {name for module in inventory["modules"] for unit in module["units"]
                        if any(item in reachable for item in unit["graph_names"])
                        for name in unit["graph_names"]}
        expanded = closure(reachable | atomic_roots, graph, all_edges)
        if expanded == reachable:
            break
        reachable = expanded

    units = {}
    owner = {}
    generated = set()
    for module in inventory["modules"]:
        for command in module["generated_commands"]:
            generated.add(command["graph_name"])
        for source in module["units"]:
            key = module["module"] + ":" + str(source["start"]["offset"])
            names = [name for name in source["graph_names"] if name in reachable]
            if not names:
                continue
            unit = dict(source, id=key, module=module["module"], names=names,
                        source_sha256=module["source_sha256"])
            for name in source["graph_names"]:
                if name in owner:
                    raise ValueError(f"A graph declaration has two AST owners: {name}")
                owner[name] = key
            # A structure command owns its constructors, recursors, and accessors.
            # Classify the command, never each generated accessor independently.
            unit["definition_command"] = source["is_instance_command"] or any(
                graph[name]["kind"] != "theorem" or graph[name]["isInstance"]
                for name in source["graph_names"])
            unit["proof_lines"] = (source["end"]["line"] - source["valueStart"]["line"]
                                   if source["valueStart"] is not None else None)
            unit["private"] = source["privateTok"] is not None
            units[key] = unit

    missing = sorted(name for name in reachable if name in graph
                     and graph[name]["startLine"] > 0
                     and name not in owner and name not in generated)

    # Private constants needed in any statement cannot live only in solutions.
    statement_roots = {dep for name in reachable if name in graph
                       for dep in graph[name]["typeDeps"]}
    statement_needed = closure(statement_roots, graph, all_edges)
    definition_keys = {key for key, unit in units.items()
                       if unit["definition_command"] and
                       (not unit["private"] or any(name in statement_needed or name in instances
                                                  for name in unit["names"]))}
    # Follow the complete body/type closure. Every theorem encountered here must
    # be proved inside Definitions; importing its sorry-stub is forbidden.
    definition_roots = {name for key in definition_keys for name in units[key]["graph_names"]}
    definition_needed = closure(definition_roots, graph, all_edges)
    while True:
        kept_keys = {owner[name] for name in definition_needed if name in owner}
        whole_command_roots = {name for key in kept_keys for name in units[key]["graph_names"]}
        expanded = closure(definition_needed | whole_command_roots, graph, all_edges)
        if expanded == definition_needed:
            break
        definition_needed = expanded
    embedded_keys = {owner[name] for name in definition_needed if name in owner} - definition_keys
    definition_keys |= {key for key in embedded_keys if units[key]["definition_command"]}
    embedded_keys -= definition_keys
    deprivate_keys = {key for key, unit in units.items() if unit["private"]
                      and any(name in statement_needed or name in definition_needed or name in instances
                              for name in unit["names"])}

    theorem_keys = set(units) - definition_keys - embedded_keys
    target_keys = {owner[name] for name in targets if name in owner}
    if target_keys & (definition_keys | embedded_keys):
        raise ValueError("A target belongs to Definitions; review graph targets before publishing")
    users = defaultdict(set)
    for name in reachable:
        row = graph.get(name)
        if row:
            for dep in row["valueDeps"]:
                if dep in owner:
                    users[owner[dep]].add(row["module"])

    nodes = set(target_keys)
    reasons = {key: ["target"] for key in target_keys}
    for key in theorem_keys - target_keys:
        unit = units[key]
        if unit["private"] and key not in deprivate_keys:
            continue
        length = unit["proof_lines"]
        if length is None:
            raise ValueError(f"A theorem command has no proof range: {key}")
        signals = []
        if length > 40:
            signals.append("proof_over_40_lines")
        elif length > 10:
            if unit["docstring"] is not None:
                signals.append("docstring")
            if any(module != unit["module"] for module in users[key]):
                signals.append("cross_module_proof_use")
        if signals:
            nodes.add(key)
            reasons[key] = signals

    # A medium-sized helper shared by >=2 actual node proofs is promoted.
    # Traversal stops at a node or Definitions boundary, and includes dependency
    # edges through compiler-generated companions even though they own no span.
    changed = True
    while changed:
        changed = False
        consumers = defaultdict(set)
        for node_key in sorted(nodes):
            roots = [dep for name in units[node_key]["graph_names"] for dep in graph[name]["valueDeps"]]
            todo, seen = roots, set()
            while todo:
                name = todo.pop()
                if name in seen or name not in graph:
                    continue
                seen.add(name)
                key = owner.get(name)
                if key == node_key:
                    continue
                if key in definition_keys or key in embedded_keys or key in nodes:
                    continue
                if key is not None:
                    consumers[key].add(node_key)
                row = graph[name]
                todo.extend(row["typeDeps"] + row["valueDeps"] + row["constructors"])
        for key, consuming_nodes in consumers.items():
            if key not in theorem_keys or key in nodes:
                continue
            unit = units[key]
            length = unit["proof_lines"]
            if (length is not None and 10 < length <= 40 and len(consuming_nodes) >= 2
                    and (not unit["private"] or key in deprivate_keys)):
                nodes.add(key)
                reasons[key] = ["shared_by_at_least_two_node_proofs"]
                changed = True

    for key, unit in units.items():
        if key in definition_keys:
            category = "definition"
        elif key in embedded_keys:
            category = "definition_embedded"
        elif key in nodes:
            category = "node"
        else:
            category = "inline"
        unit["category"] = category
        unit["deprivate"] = key in deprivate_keys
        unit["promotion_reasons"] = reasons.get(key, [])
        todo = [dep for name in unit["graph_names"]
                for field in all_edges for dep in graph[name][field]]
        deps, visited = set(), set()
        while todo:
            name = todo.pop()
            if name in visited or name not in graph:
                continue
            visited.add(name)
            dependency_owner = owner.get(name)
            if dependency_owner is not None:
                if dependency_owner != key:
                    deps.add(dependency_owner)
                continue
            # No-span compiler companions and preserved notation commands are
            # transparent for dependency routing, rather than silently dropped.
            row = graph[name]
            todo.extend(row["typeDeps"] + row["valueDeps"] + row["constructors"])
        unit["direct_unit_dependencies"] = sorted(deps)
    definition_categories = {"definition", "definition_embedded"}
    for unit in units.values():
        if unit["category"] in definition_categories:
            escaped = [key for key in unit["direct_unit_dependencies"]
                       if units[key]["category"] not in definition_categories]
            if escaped:
                raise ValueError(f"Definitions dependency would escape into theorem stubs: {unit['id']}, {escaped}")
    counts = dict(sorted(Counter(unit["category"] for unit in units.values()).items()))
    return {"complete_extraction": inventory["complete_extraction"],
            "ready_for_generation": bool(inventory["complete_extraction"] and not missing),
            "source_targets": sorted(targets), "instance_roots": len(instances),
            "reachable_declarations": len(reachable & graph.keys()),
            "source_declarations_pending_ast": missing,
            "preserved_generated_commands": sorted(generated & reachable),
            "counts": counts, "deprivate_units": len(deprivate_keys),
            "local_instance_units": [key for key, unit in units.items() if unit["is_local_instance"]],
            "units": list(units.values())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview", action="store_true")
    args = parser.parse_args()
    state = read_json(DEST / "extraction-state.json")
    inventory = read_json(DEST / "ast-unit-inventory.json")
    if inventory["unmatched"]:
        raise SystemExit("Unmatched source declarations must be resolved first")
    if not state.get("complete") and not args.preview:
        raise SystemExit("Full Stage 2 extraction is required; use --preview for provisional counts")
    if inventory["complete_extraction"] != state.get("complete", False):
        raise SystemExit("Refresh the AST inventories after extraction changes")
    if state.get("complete") and len(inventory["modules"]) != len(state["stage2"]):
        raise SystemExit("Full planning requires inventories for every extracted source")
    for module in inventory["modules"]:
        relative = module["module"].replace(".", "/") + ".lean"
        entry = state["stage2"][relative]
        actual = hashlib.sha256((TASK / "port/lean" / relative).read_bytes()).hexdigest()
        if actual != module["source_sha256"] or actual != entry["preflight"]["source_sha256"]:
            raise SystemExit(f"Source changed after AST extraction: {relative}")
    graph_path = DEST / "decl_graph.jsonl"
    if hashlib.sha256(graph_path.read_bytes()).hexdigest() != state["stage1"]["facts_sha256"]:
        raise SystemExit("Declaration graph checksum differs from the validated extraction")
    rows = [json.loads(line) for line in graph_path.read_text(encoding="utf-8").splitlines()]
    plan = make_plan(inventory, rows)
    if not args.preview and not plan["ready_for_generation"]:
        raise SystemExit("Full plan still has declarations without AST owners")
    plan["provisional"] = args.preview
    # Even a complete preview cannot be mistaken for the reviewed final plan.
    if args.preview:
        plan["ready_for_generation"] = False
    name = "platform-unit-plan-preview.json" if args.preview else "platform-unit-plan.json"
    (DEST / name).write_text(json.dumps(plan, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in plan.items()
                      if key not in ("units", "preserved_generated_commands", "source_declarations_pending_ast")}
                     | {"pending_source_declarations": len(plan["source_declarations_pending_ast"])}))


if __name__ == "__main__":
    main()
