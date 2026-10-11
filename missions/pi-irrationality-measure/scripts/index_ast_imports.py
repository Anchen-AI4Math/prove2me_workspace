"""Read import edges and replacement ranges from parser facts, preserving external dependencies."""
import json
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"
state = json.loads((DEST / "extraction-state.json").read_text(encoding="utf-8"))
source_prefix = (TASK / "port/lean").relative_to(ROOT).as_posix() + "/"
owned_modules = {path.removeprefix(source_prefix).removesuffix(".lean").replace("/", ".")
                 for path in state["inputs"] if path.startswith(source_prefix)}

def walk(node):
    yield node
    for child in node.get("children", []):
        yield from walk(child)

modules = {}
for relative, entry in sorted(state["stage2"].items()):
    facts = [json.loads(line) for line in (ROOT / entry["facts"]).read_text(encoding="utf-8").splitlines()]
    header = next(fact["syntax"] for fact in facts if fact["kind"] == "header")
    imports = []
    for node in walk(header):
        if node["syntaxKind"] != "Lean.Parser.Module.import":
            continue
        identifiers = [child for child in walk(node) if child.get("identifier") is not None]
        if len(identifiers) != 1:
            raise SystemExit(f"Unsupported import syntax in {relative}")
        identifier = identifiers[0]
        name = identifier["identifier"]
        imports.append({"module": name, "project": name in owned_modules,
                        "command_range": node["range"], "name_range": identifier["range"]})
    name = relative.removesuffix(".lean").replace("/", ".")
    modules[name] = {"source": relative, "source_sha256": entry["preflight"]["source_sha256"],
                     "imports": imports}

closures = {}
for name in modules:
    todo = [name]
    seen = set()
    external = set()
    pending = set()
    while todo:
        current = todo.pop()
        if current in seen:
            continue
        seen.add(current)
        if current not in modules:
            pending.add(current)
            continue
        for dependency in modules[current]["imports"]:
            if dependency["project"]:
                todo.append(dependency["module"])
            else:
                external.add(dependency["module"])
    closures[name] = {"external_imports": sorted(external), "unextracted_project_modules": sorted(pending)}
report = {"complete_extraction": state.get("complete", False), "modules": modules,
          "transitive_external_imports": closures}
if report["complete_extraction"] and any(value["unextracted_project_modules"] for value in closures.values()):
    raise SystemExit("A full import inventory must have no missing project modules")
(DEST / "ast-import-inventory.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"extracted_modules": len(modules),
                  "direct_imports": sum(len(value["imports"]) for value in modules.values()),
                  "complete_extraction": report["complete_extraction"]}))
