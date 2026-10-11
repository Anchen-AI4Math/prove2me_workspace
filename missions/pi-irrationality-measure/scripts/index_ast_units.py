"""Join extracted source-command units to the elaborated graph; never split by text patterns."""
import hashlib
import argparse
import json
from pathlib import Path
from validate_ast_facts import validate_facts

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"
state = json.loads((DEST / "extraction-state.json").read_text(encoding="utf-8"))
graph_path = DEST / "decl_graph.jsonl"
if hashlib.sha256(graph_path.read_bytes()).hexdigest() != state["stage1"]["facts_sha256"]:
    raise SystemExit("The declaration graph changed during extraction")
rows = [json.loads(s) for s in graph_path.read_text(encoding="utf-8").splitlines()]
by_name = {row["name"]: row for row in rows}

def syntax_nodes(node):
    yield node
    for child in node.get("children", []):
        yield from syntax_nodes(child)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--target", action="append",
                    help="Explicit original proof target; default is the direct campaign root obligation")
args = parser.parse_args()
targets = args.target or ["OAI.PiExponent.pi_eventual_lower_bound"]
if any(name not in by_name for name in targets):
    raise SystemExit("An upload target must occur in the authoritative declaration graph")
todo = targets + [row["name"] for row in rows if row["isInstance"]]
reachable = set()
while todo:
    name = todo.pop()
    if name in reachable:
        continue
    reachable.add(name)
    row = by_name.get(name)
    if row:
        todo += row["typeDeps"] + row["valueDeps"] + row["constructors"]

inventory = []
unmatched = []
for relative, entry in sorted(state["stage2"].items()):
    module = relative.removesuffix(".lean").replace("/", ".")
    source = TASK / "port/lean" / relative
    facts_path = ROOT / entry["facts"]
    if hashlib.sha256(facts_path.read_bytes()).hexdigest() != entry["facts_sha256"]:
        raise SystemExit(f"Oracle facts changed: {relative}")
    facts = [json.loads(s) for s in facts_path.read_text(encoding="utf-8").splitlines()]
    validate_facts(source, facts, entry["preflight"]["source_sha256"])
    declarations = [fact for fact in facts if fact["kind"] == "decl"]
    commands = [fact for fact in facts if fact["kind"] == "command"]
    command_by_start = {fact["syntax"]["range"]["start"]["offset"]: fact["syntax"]
                        for fact in commands if fact["isDeclaration"]}
    module_rows = [row for row in rows if row["module"] == module and row["startLine"] > 0]
    units = []
    claimed = set()
    for decl in declarations:
        syntax = command_by_start[decl["declStart"]["offset"]]
        parsed_instance = any(node["syntaxKind"] == "Lean.Parser.Command.instance"
                              for node in syntax_nodes(syntax))
        local_modifiers = [node["range"] for instance in syntax_nodes(syntax)
                           if instance["syntaxKind"] == "Lean.Parser.Command.instance"
                           for attr_kind in syntax_nodes(instance)
                           if attr_kind["syntaxKind"] == "Lean.Parser.Term.attrKind"
                           for node in syntax_nodes(attr_kind)
                           if node["syntaxKind"] == "local" and node.get("atom") == "local"]
        contained = [row for row in module_rows
                     if decl["declStart"]["line"] <= row["startLine"] <= decl["declEnd"]["line"]]
        for row in contained:
            if row["name"] in claimed:
                raise SystemExit(f"Ambiguous declaration containment: {row['name']}")
            claimed.add(row["name"])
        units.append({"start": decl["declStart"], "end": decl["declEnd"],
                      "nameText": decl["nameText"], "nameRange": decl.get("nameRange"),
                      "valueStart": decl["valStart"], "docstring": decl["docstring"],
                      "privateTok": decl["privateTok"],
                      "graph_names": [row["name"] for row in contained],
                      "graph_kinds": sorted({row["kind"] for row in contained}),
                      "is_instance_command": parsed_instance or any(row["isInstance"] for row in contained),
                      "is_local_instance": parsed_instance and bool(local_modifiers),
                      "local_modifier_ranges": local_modifiers,
                      "reachable_names": [row["name"] for row in contained if row["name"] in reachable]})
    generated_commands = []
    for row in module_rows:
        if row["name"] in claimed:
            continue
        matches = [command for command in commands if not command["isDeclaration"]
                   and command["syntax"].get("range")
                   and command["syntax"]["range"]["start"]["line"] <= row["startLine"]
                   <= command["syntax"]["range"]["end"]["line"]]
        if len(matches) == 1:
            generated_commands.append({"graph_name": row["name"],
                                       "syntaxKind": matches[0]["syntax"]["syntaxKind"],
                                       "range": matches[0]["syntax"]["range"]})
        else:
            unmatched.append({"module": module, "name": row["name"], "line": row["startLine"],
                              "command_matches": len(matches)})
    inventory.append({"module": module, "source_sha256": entry["preflight"]["source_sha256"],
                      "units": units, "generated_commands": generated_commands})

# The elaborated global instance table omits local attributes after scope exit.
# Supplement roots from parsed instance commands, then refresh every unit's
# reachability rather than leave a stale global-only field for the generator.
todo = [name for module in inventory for unit in module["units"]
        if unit["is_instance_command"] for name in unit["graph_names"]]
while todo:
    name = todo.pop()
    if name in reachable:
        continue
    reachable.add(name)
    row = by_name.get(name)
    if row:
        todo += row["typeDeps"] + row["valueDeps"] + row["constructors"]
for module in inventory:
    for unit in module["units"]:
        unit["reachable_names"] = [name for name in unit["graph_names"] if name in reachable]
report = {"complete_extraction": state.get("complete", False), "source_targets": targets,
          "extracted_modules": len(inventory), "total_modules": 875,
          "reachable_declarations_with_source": sum(row["name"] in reachable and row["startLine"] > 0
                                                   for row in rows),
          "modules": inventory, "unmatched": unmatched}
(DEST / "ast-unit-inventory.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"extracted_modules": len(inventory),
                  "declaration_units": sum(len(module["units"]) for module in inventory),
                  "unmatched": len(unmatched), "complete_extraction": report["complete_extraction"]}))
