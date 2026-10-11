"""Recover declaration scopes from parsed commands for later namespace-safe generation."""
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"

def identifiers(node):
    result = []
    if node.get("identifier") is not None:
        result.append(node["identifier"])
    for child in node.get("children", []):
        result += identifiers(child)
    return result

def namespace_name(frames):
    name = ""
    for frame in frames:
        if frame["kind"] != "namespace":
            continue
        part = frame["name"]
        if part.startswith("_root_."):
            name = part.removeprefix("_root_.")
        else:
            name = part if not name else name + "." + part
    return name

def recover_scopes(relative, facts, actual_names):
    frames = [{"kind": "root", "name": None, "context": []}]
    declarations = []
    source_declarations = {fact["declStart"]["offset"]: fact for fact in facts if fact["kind"] == "decl"}
    for command in (fact for fact in facts if fact["kind"] == "command"):
        syntax = command["syntax"]
        kind = syntax["syntaxKind"]
        if command["isDeclaration"]:
            decl = source_declarations[syntax["range"]["start"]["offset"]]
            namespace = namespace_name(frames)
            expected_name = None
            if decl["nameText"]:
                if decl["nameText"].startswith("_root_."):
                    expected_name = decl["nameText"].removeprefix("_root_.")
                else:
                    expected_name = decl["nameText"] if not namespace else namespace + "." + decl["nameText"]
                if expected_name not in actual_names:
                    raise SystemExit(f"AST scope disagrees with the elaborated name: {expected_name}")
            declarations.append({"range": syntax["range"], "namespace": namespace,
                                 "verified_name": expected_name,
                                 "scope_stack": [{k: v for k, v in frame.items() if k != "context"}
                                                 for frame in frames[1:]],
                                 "context_commands": [item for frame in frames for item in frame["context"]]})
            continue
        if kind == "Lean.Parser.Command.namespace":
            names = identifiers(syntax)
            if len(names) != 1:
                raise SystemExit(f"Unexpected namespace command in {relative}")
            # BuiltinCommand.addScopes creates one scope per name component.
            for part in names[0].split("."):
                frames.append({"kind": "namespace", "name": part, "opening": syntax["range"], "context": []})
        elif kind == "Lean.Parser.Command.section":
            children = syntax.get("children", [])
            labels = identifiers(children[-1]) if children else []
            if len(labels) > 1:
                raise SystemExit(f"Unexpected section label in {relative}")
            for part in labels[0].split(".") if labels else [None]:
                frames.append({"kind": "section", "name": part,
                               "opening": syntax["range"], "context": []})
        elif kind == "Lean.Parser.Command.end":
            if len(frames) == 1:
                raise SystemExit(f"Unmatched scope end in {relative}")
            labels = identifiers(syntax)
            observed = labels[0].split(".") if labels else [None]
            if len(observed) >= len(frames):
                raise SystemExit(f"Too many scope components in {relative}: {labels}")
            expected = [frame["name"] for frame in frames[-len(observed):]]
            if expected != observed:
                raise SystemExit(f"Scope label mismatch in {relative}: {observed}, {expected}")
            del frames[-len(observed):]
        elif kind != "Lean.Parser.Command.eoi":
            frames[-1]["context"].append({"syntaxKind": kind, "range": syntax["range"]})
    if len(frames) != 1:
        raise SystemExit(f"Unclosed source scopes in {relative}")
    return declarations


def main():
    state = json.loads((DEST / "extraction-state.json").read_text(encoding="utf-8"))
    graph = [json.loads(line) for line in (DEST / "decl_graph.jsonl").read_text(encoding="utf-8").splitlines()]
    modules = []
    for relative, entry in sorted(state["stage2"].items()):
        facts = [json.loads(line) for line in (ROOT / entry["facts"]).read_text(encoding="utf-8").splitlines()]
        module_name = relative.removesuffix(".lean").replace("/", ".")
        actual_names = {row["userName"] for row in graph if row["module"] == module_name}
        declarations = recover_scopes(relative, facts, actual_names)
        modules.append({"source": relative, "source_sha256": entry["preflight"]["source_sha256"],
                        "declarations": declarations})
    report = {"complete_extraction": state.get("complete", False), "modules": modules,
              "extracted_modules": len(modules),
              "declarations": sum(len(module["declarations"]) for module in modules)}
    (DEST / "ast-scope-inventory.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "modules"}))


if __name__ == "__main__":
    main()
