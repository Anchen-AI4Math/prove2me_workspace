"""Report unsupported node hoisting contexts from the frozen AST plan, without Lean."""
import hashlib
import json
from collections import Counter
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]


def main():
    inputs = {}
    def read(relative):
        raw = (TASK / relative).read_bytes()
        inputs[relative] = hashlib.sha256(raw).hexdigest()
        return json.loads(raw)
    plan = read("verification/platform-unit-plan-preview.json")
    artifacts = read("verification/platform-artifact-plan-preview.json")
    scopes = read("verification/ast-scope-inventory.json")
    wrappers = read("verification/ast-wrapper-inventory.json")
    units = {row["id"]: row for row in plan["units"]}
    scope_by_binding = {}
    for module in scopes["modules"]:
        source_module = module["source"].removesuffix(".lean").replace("/", ".")
        for row in module["declarations"]:
            scope_by_binding[(source_module, row["range"]["start"]["offset"])] = row
    wrapper_by_binding = {}
    for module in wrappers["modules"]:
        for row in module["declarations"]:
            wrapper_by_binding[(module["module"], row["range"]["start"]["offset"])] = row
    allowed = {"Lean.Parser.Command." + suffix for suffix in
               ("open", "variable", "universe", "include", "omit")}
    wrapper_allowed = {"Lean.Parser.Command." + suffix for suffix in
                       ("open", "include", "omit")}
    counts, records = Counter(), []
    for key in artifacts["node_order"]:
        unit = units[key]
        identity = (unit["module"], unit["start"]["offset"])
        scope = scope_by_binding[identity]
        wrapper = wrapper_by_binding[identity]
        frame_kinds = [row["kind"] for row in scope["scope_stack"]]
        active_kinds = [row["syntaxKind"] for row in scope["context_commands"]]
        wrapper_kinds = [row["syntaxKind"] for row in wrapper["wrappers"]]
        problems = []
        if any(kind != "namespace" for kind in frame_kinds):
            problems.append("non_namespace_scope")
        if set(active_kinds) - allowed:
            problems.append("active_context")
        if set(wrapper_kinds) - wrapper_allowed:
            problems.append("scoped_wrapper")
        if unit["graph_kinds"] != ["theorem"] or len(unit["graph_names"]) != 1:
            problems.append("atomic_multi_declaration")
        counts.update(problems)
        if problems:
            records.append({"unit": key, "source_module": unit["module"],
                            "names": unit["graph_names"], "issues": problems,
                            "scope_kinds": frame_kinds, "active_context_kinds": active_kinds,
                            "wrapper_kinds": wrapper_kinds,
                            "source_range": {"start": unit["start"], "end": unit["end"]}})
    report = {"input_hashes": inputs, "provisional": True, "validated": False,
              "total_nodes": len(artifacts["node_order"]),
              "unsupported_node_count": len(records), "issue_counts": dict(counts),
              "nodes": records,
              "meaning": "Python structural coverage only; no elaboration or proof certification."}
    output = TASK / "verification/node-scope-coverage-audit.json"
    output.write_bytes((json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))
    print(json.dumps({key: report[key] for key in
                      ("total_nodes", "unsupported_node_count", "issue_counts")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
