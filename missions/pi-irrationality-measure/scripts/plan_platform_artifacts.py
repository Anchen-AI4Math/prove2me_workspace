"""Plan Definitions bundles and node solution dependencies from the unit graph."""
import argparse
from collections import defaultdict
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
DEST = TASK / "verification"


def leaves_first(dependencies):
    pending = {key: set(value) for key, value in dependencies.items()}
    if any(dep not in pending for deps in pending.values() for dep in deps):
        raise ValueError("Artifact dependencies reference an unknown artifact")
    result = []
    while pending:
        ready = sorted(key for key, deps in pending.items() if not deps)
        if not ready:
            raise ValueError(f"Artifact dependency cycle: {sorted(pending)}")
        result.extend(ready)
        for key in ready:
            del pending[key]
        for deps in pending.values():
            deps.difference_update(ready)
    return result


def build_artifacts(plan, scope_inventory, reuse_candidates):
    units = {unit["id"]: unit for unit in plan["units"]}
    scopes = {module["source"].removesuffix(".lean").replace("/", "."):
              {decl["range"]["start"]["offset"]: decl for decl in module["declarations"]}
              for module in scope_inventory["modules"]}
    definitions = defaultdict(list)
    for key, unit in units.items():
        if unit["category"] in ("definition", "definition_embedded"):
            definitions[unit["module"]].append(key)
    definition_edges = {module: set() for module in definitions}
    for module, selected in definitions.items():
        for key in selected:
            for dep in units[key]["direct_unit_dependencies"]:
                target = units[dep]
                if target["category"] not in ("definition", "definition_embedded"):
                    raise ValueError("A Definitions bundle would depend on a theorem stub")
                if target["module"] != module:
                    definition_edges[module].add(target["module"])

    nodes = {}
    for key, unit in units.items():
        if unit["category"] != "node":
            continue
        name = scopes[unit["module"]][unit["start"]["offset"]]["verified_name"]
        if name is None:
            raise ValueError(f"Node command has no verified primary binding: {key}")
        todo = list(unit["direct_unit_dependencies"])
        seen, inline, child_nodes, def_modules = set(), set(), set(), set()
        while todo:
            dep = todo.pop()
            if dep in seen or dep == key:
                continue
            seen.add(dep)
            target = units[dep]
            category = target["category"]
            if category == "node":
                child_nodes.add(dep)
            elif category in ("definition", "definition_embedded"):
                def_modules.add(target["module"])
            else:
                inline.add(dep)
                todo.extend(target["direct_unit_dependencies"])
        components = defaultdict(list)
        for kept in inline | {key}:
            components[units[kept]["module"]].append(kept)
        nodes[key] = {"theorem_name_before_platform_renames": name,
                      "source_module": unit["module"], "node_dependencies": sorted(child_nodes),
                      "definition_modules": sorted(def_modules), "inline_units": sorted(inline),
                      "source_components": {module: sorted(selected) for module, selected in sorted(components.items())}}
    node_edges = {key: set(node["node_dependencies"]) for key, node in nodes.items()}
    pending_reuse = [candidate for candidate in reuse_candidates if not candidate["validated"]]
    pending_names = [node["theorem_name_before_platform_renames"] for node in nodes.values()
                     if not node["theorem_name_before_platform_renames"].isascii()
                     or any(not part.isidentifier() for part in node["theorem_name_before_platform_renames"].split("."))]
    return {"ready_for_generation": bool(plan["ready_for_generation"] and not pending_reuse and not pending_names),
            "complete_extraction": plan["complete_extraction"],
            "definition_bundles": {module: {"units": sorted(selected), "imports": sorted(definition_edges[module])}
                                   for module, selected in sorted(definitions.items())},
            "definition_order": leaves_first(definition_edges), "nodes": nodes,
            "node_order": leaves_first(node_edges), "definition_reuse_candidates": reuse_candidates,
            "pending_definition_reuse": [candidate["source_module"] for candidate in pending_reuse],
            "pending_platform_names": sorted(pending_names),
            "local_instance_units_requiring_scope_restoration": plan["local_instance_units"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview", action="store_true")
    args = parser.parse_args()
    name = "platform-unit-plan-preview.json" if args.preview else "platform-unit-plan.json"
    plan = json.loads((DEST / name).read_text(encoding="utf-8"))
    scopes = json.loads((DEST / "ast-scope-inventory.json").read_text(encoding="utf-8"))
    reuse = json.loads((TASK / "platform/definition-reuse-candidates.json").read_text(encoding="utf-8"))["reuse_candidates"]
    report = build_artifacts(plan, scopes, reuse)
    if not args.preview and not report["ready_for_generation"]:
        raise SystemExit("Final artifact planning requires complete facts, validated definition reuse and platform names")
    report["provisional"] = args.preview
    output = "platform-artifact-plan-preview.json" if args.preview else "platform-artifact-plan.json"
    (DEST / output).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"definition_bundles": len(report["definition_bundles"]), "nodes": len(report["nodes"]),
                      "definition_dag_acyclic": True, "solution_dag_acyclic": True,
                      "pending_definition_reuse": report["pending_definition_reuse"],
                      "ready_for_generation": report["ready_for_generation"], "provisional": args.preview}))


if __name__ == "__main__":
    main()
