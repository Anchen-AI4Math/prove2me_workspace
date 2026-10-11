"""Stage an independently closed source theorem from authoritative AST facts.

This does not bypass the full-tree gate: only a theorem with no other project
declaration in its complete kernel dependency closure may use this stage.
"""
import argparse
import hashlib
import json
from pathlib import Path
from platform_statement import statement_fragment, solution_fragment
from rewrite_ast_imports import external_import_union
from validate_ast_facts import validate_facts

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def runtime_pin():
    path = DEST / "lean-runtime.json"
    runtime = read(path)
    for name, expected in runtime["project_hashes"].items():
        if digest(ROOT / name) != expected:
            raise ValueError("Pinned workspace configuration changed")
    if digest(Path(runtime["executable"])) != runtime["executable_sha256"]:
        raise ValueError("Pinned Lean executable changed")
    return digest(path)


def snapshot_texts(stage, manifest):
    """Rebuild the snapshot inputs from the exact upload fragments."""
    core = (DEST / "TypedSnapshotCore.inc").read_text(encoding="utf-8")
    name, module = manifest["theorem_name"], manifest["source_module"]
    original_output = (stage / "original-type.json").relative_to(ROOT).as_posix()
    generated_output = (stage / "generated-type.json").relative_to(ROOT).as_posix()
    tail = ("\nset_option pp.universes true\nset_option pp.fullNames true\n"
            "set_option pp.explicit true\nrun_meta do\n")
    original = "import Lean\nimport " + module + "\n\n" + core + tail + (
        f"  PiExponentInterfaceSnapshot.exportSnapshot #[`{name}] \"{original_output}\"\n"
        f"#print axioms {name}\n")
    generated = "import Lean\n" + manifest["preamble"] + manifest["formal_statement"] + (
        "\n\n" + manifest["solution_fragment"] + "\n\n" + core + tail +
        f"  PiExponentInterfaceSnapshot.exportSnapshot #[`{name}, `solution] \"{generated_output}\"\n"
        "#print axioms solution\n")
    return {"SnapshotOriginal.lean": original, "SnapshotGenerated.lean": generated}


def check_stage_inputs(stage, manifest):
    if set(manifest["snapshot_sha256"]) != {"SnapshotOriginal.lean", "SnapshotGenerated.lean"}:
        raise ValueError("Both exact snapshot inputs must be pinned")
    for path_field, hash_field in (("source", "source_sha256"),
                                  ("original_source", "original_source_sha256"),
                                  ("statement", "statement_sha256"),
                                  ("solution", "solution_sha256"),
                                  ("source_graph", "source_graph_sha256"),
                                  ("facts", "facts_sha256")):
        if digest(ROOT / manifest[path_field]) != manifest[hash_field]:
            raise ValueError("Stage provenance changed: " + path_field)
    if digest(DEST / "TypedSnapshotCore.inc") != manifest["snapshot_core_sha256"]:
        raise ValueError("The kernel snapshot serializer changed")
    if runtime_pin() != manifest["runtime_sha256"]:
        raise ValueError("The pinned Lean runtime changed")
    expected = {Path(manifest["statement"]).name:
                manifest["preamble"] + manifest["formal_statement"] + "\n",
                Path(manifest["solution"]).name:
                manifest["preamble"] + manifest["solution_fragment"] +
                "\n\n#print axioms solution\n", **snapshot_texts(stage, manifest)}
    for filename, content in expected.items():
        path = stage / filename
        if path.read_bytes() != content.encode("utf-8"):
            raise ValueError("Staged text is not the exact reconstructed artifact: " + filename)
        if filename in manifest["snapshot_sha256"] and digest(path) != manifest["snapshot_sha256"][filename]:
            raise ValueError("A staged kernel snapshot changed: " + filename)


def generate(name):
    state = read(DEST / "extraction-state.json")
    graph_path = DEST / "decl_graph.jsonl"
    if digest(graph_path) != state["stage1"]["facts_sha256"]:
        raise ValueError("The original declaration graph changed")
    graph = {row["name"]: row for row in
             (json.loads(line) for line in graph_path.read_text(encoding="utf-8").splitlines())}
    row = graph[name]
    if row["kind"] != "theorem" or row["isPrivate"] or row["isInstance"]:
        raise ValueError("Independent staging is limited to public, ordinary theorems")
    todo, closure = [name], set()
    while todo:
        current = todo.pop()
        if current in closure or current not in graph:
            continue
        closure.add(current)
        item = graph[current]
        todo += item["typeDeps"] + item["valueDeps"] + item["constructors"]
    if closure != {name}:
        raise ValueError("Other project declarations are required; use the complete-tree generator")
    module = row["module"]
    relative = module.replace(".", "/") + ".lean"
    entry = state["stage2"][relative]
    facts_path = ROOT / entry["facts"]
    if digest(facts_path) != entry["facts_sha256"]:
        raise ValueError("Authoritative source AST changed")
    source = TASK / "port/lean" / relative
    data = source.read_bytes()
    facts = [json.loads(line) for line in facts_path.read_text(encoding="utf-8").splitlines()]
    validate_facts(source, facts, entry["preflight"]["source_sha256"])
    modules = read(DEST / "ast-unit-inventory.json")["modules"]
    unit_module = next(item for item in modules if item["module"] == module)
    unit = next(item for item in unit_module["units"] if name in item["graph_names"])
    if unit["graph_names"] != [name]:
        raise ValueError("The command owns other declarations; independent staging is not applicable")
    wrapper_module = next(item for item in read(DEST / "ast-wrapper-inventory.json")["modules"]
                          if item["module"] == module)
    wrapper = next(item for item in wrapper_module["declarations"]
                   if item["range"]["start"] == unit["start"])
    scope_module = next(item for item in read(DEST / "ast-scope-inventory.json")["modules"]
                        if item["source"] == relative)
    scope = next(item for item in scope_module["declarations"]
                 if item["range"]["start"] == unit["start"])
    if scope["verified_name"] != name:
        raise ValueError("The source scope does not match the elaborated declaration")
    imports = external_import_union(module, read(DEST / "ast-import-inventory.json"))
    preamble = "\n".join("import " + item for item in imports) + "\n\n"
    allowed = {"Lean.Parser.Command.open", "Lean.Parser.Command.variable",
               "Lean.Parser.Command.include", "Lean.Parser.Command.omit",
               "Lean.Parser.Command.universe", "Lean.Parser.Command.set_option"}
    for context in scope["context_commands"]:
        if context["syntaxKind"] not in allowed:
            raise ValueError("Independent staging needs explicit handling of this context command: "
                             + context["syntaxKind"])
        span = context["range"]
        preamble += data[span["start"]["offset"]:span["end"]["offset"]].decode("utf-8") + "\n"
    statement, hoisted, statement_edits = statement_fragment(
        data, unit, wrapper, name, entry["preflight"]["source_sha256"])
    solution, solution_hoisted, solution_edits = solution_fragment(
        data, unit, wrapper, entry["preflight"]["source_sha256"])
    if hoisted != solution_hoisted:
        raise ValueError("Statement and proof have different hoisted source contexts")
    preamble += "\n".join(item["text"] for item in hoisted) + "\n\n"
    slug = name.replace(".", "_")
    stage = DEST / "independent" / slug
    stage.mkdir(parents=True, exist_ok=True)
    statement_path = stage / ("Thm_" + slug + ".lean")
    solution_path = stage / ("Sol_" + slug + ".lean")
    statement_path.write_bytes((preamble + statement.decode("utf-8") + "\n").encode("utf-8"))
    solution_path.write_bytes((preamble + solution.decode("utf-8") +
                               "\n\n#print axioms solution\n").encode("utf-8"))
    core_path = DEST / "TypedSnapshotCore.inc"
    original = TASK / "source/lean" / relative
    manifest = {"theorem_name": name, "independently_closed_project_dependencies": sorted(closure),
                "full_main_tree_complete": state.get("complete", False),
                "source_module": module, "source": source.relative_to(ROOT).as_posix(),
                "source_sha256": digest(source), "original_source": original.relative_to(ROOT).as_posix(),
                "original_source_sha256": digest(original),
                "source_graph": graph_path.relative_to(ROOT).as_posix(),
                "source_graph_sha256": digest(graph_path),
                "facts": facts_path.relative_to(ROOT).as_posix(), "facts_sha256": digest(facts_path),
                "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
                "source_url": "https://github.com/openai/math/blob/"
                              "adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/" + relative +
                              f"#L{unit['start']['line']}-L{unit['end']['line']}",
                "preamble": preamble, "formal_statement": statement.decode("utf-8"),
                "solution_fragment": solution.decode("utf-8"),
                "statement_edits": statement_edits, "solution_edits": solution_edits,
                "statement": statement_path.relative_to(ROOT).as_posix(),
                "statement_sha256": digest(statement_path),
                "solution": solution_path.relative_to(ROOT).as_posix(),
                "solution_sha256": digest(solution_path),
                "snapshot_core_sha256": digest(core_path),
                "runtime_sha256": runtime_pin(),
                "validated": False, "pending": ["strict compilation", "kernel type comparison"]}
    manifest["snapshot_sha256"] = {}
    for filename, content in snapshot_texts(stage, manifest).items():
        path = stage / filename
        path.write_bytes(content.encode("utf-8"))
        manifest["snapshot_sha256"][filename] = digest(path)
    check_stage_inputs(stage, manifest)
    (stage / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"stage": stage.relative_to(TASK).as_posix(), "theorem_name": name,
                      "project_dependency_closure": 1, "external_imports": len(imports),
                      "validated": False}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name")
    generate(parser.parse_args().name)
