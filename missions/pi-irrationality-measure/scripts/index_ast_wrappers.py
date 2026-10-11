"""Index declaration wrappers and theorem keyword ranges from actual parser trees."""
from collections import Counter
import hashlib
import json
from pathlib import Path
from validate_ast_facts import validate_facts

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"


def walk(node):
    yield node
    for child in node.get("children", []):
        yield from walk(child)


def unwrap(node):
    wrappers = []
    while node["syntaxKind"] == "Lean.Parser.Command.in":
        children = node.get("children", [])
        if (len(children) != 3 or children[1].get("atom") != "in"
                or children[1]["syntaxKind"] != "in"):
            raise ValueError("Unexpected parser structure for a scoped command")
        head, _, inner = children
        if not head.get("range") or not inner.get("range"):
            raise ValueError("A scoped command has no authoritative byte range")
        wrappers.append({"syntaxKind": head["syntaxKind"], "command_range": head["range"],
                         "prefix_range": {"start": node["range"]["start"],
                                          "end": inner["range"]["start"]}})
        node = inner
    return node, wrappers


def main():
    state = json.loads((DEST / "extraction-state.json").read_text(encoding="utf-8"))
    inventory = json.loads((DEST / "ast-unit-inventory.json").read_text(encoding="utf-8"))
    modules = []
    wrapper_counts = Counter()
    for module in inventory["modules"]:
        relative = module["module"].replace(".", "/") + ".lean"
        entry = state["stage2"][relative]
        path = ROOT / entry["facts"]
        if hashlib.sha256(path.read_bytes()).hexdigest() != entry["facts_sha256"]:
            raise ValueError(f"Oracle fact bytes changed: {relative}")
        facts = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]
        validate_facts(TASK / "port/lean" / relative, facts, module["source_sha256"])
        by_start = {unit["start"]["offset"]: unit for unit in module["units"]}
        declarations = []
        for fact in facts:
            if fact["kind"] != "command" or not fact["isDeclaration"]:
                continue
            syntax = fact["syntax"]
            unit = by_start[syntax["range"]["start"]["offset"]]
            inner, wrappers = unwrap(syntax)
            keywords = [{"keyword": node["atom"], "range": node["range"]}
                        for node in walk(inner) if node["syntaxKind"] in ("theorem", "lemma")
                        and node.get("atom") == node["syntaxKind"]]
            if (unit["graph_kinds"] == ["theorem"] and not unit["is_instance_command"]
                    and len(keywords) != 1):
                raise ValueError(f"The theorem keyword is ambiguous: {relative}, {unit['nameText']}")
            wrapper_counts.update(wrapper["syntaxKind"] for wrapper in wrappers)
            declarations.append({"range": syntax["range"], "nameText": unit["nameText"],
                                 "nameRange": unit["nameRange"], "wrappers": wrappers,
                                 "inner_syntaxKind": inner["syntaxKind"],
                                 "theorem_keyword_tokens": keywords})
        modules.append({"module": module["module"], "source_sha256": module["source_sha256"],
                        "declarations": declarations})
    report = {"complete_extraction": inventory["complete_extraction"],
              "extracted_modules": len(modules), "declarations": sum(len(m["declarations"]) for m in modules),
              "wrapper_counts": dict(sorted(wrapper_counts.items())), "modules": modules}
    (DEST / "ast-wrapper-inventory.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "modules"}))


if __name__ == "__main__":
    main()
