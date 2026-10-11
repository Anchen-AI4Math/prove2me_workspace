"""Stage source-faithful Thm/Sol node artifacts without compiling or publishing.

Preview has the same byte/provenance and dependency checks as final generation.
Final additionally requires complete reviewed plans and verified Definitions.
No output of this program is marked validated or ready for submission.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path

from generate_platform_bundles import Generator, DEFINITION_CATEGORIES, PRESERVED_CONTEXT
from generate_independent_node import runtime_pin
from plan_platform_artifacts import leaves_first
from platform_statement import declaration_fragment
from rename_bound_constant import rename_bound_constant
from rewrite_ast_imports import external_import_union, import_edits
from skeleton_subtract import declaration_edits
from span_edits import Edit, apply_edits, from_range
from validate_ast_facts import validate_facts

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_name(name):
    if not name or not name.isascii() or any(not part.isidentifier() for part in name.split(".")):
        raise ValueError("A node needs an explicit conservative ASCII public name")
    return name


def unique_edits(edits):
    result = {}
    for edit in edits:
        key = (edit.start, edit.end)
        if key in result and result[key].replacement != edit.replacement:
            raise ValueError("One authoritative reference range has conflicting constant rewrites")
        result[key] = edit
    return list(result.values())


def compose_fragment(data, unit, fragment, ledger, reference_edits):
    """Recover exact base replacement bytes from its ledger, then apply once."""
    source_start = unit["start"]["offset"]
    delta, edits = 0, []
    for item in sorted(ledger, key=lambda value: (value["start"], value["end"])):
        position = item["start"] - source_start + delta
        replacement = fragment[position:position + item["replacement_bytes"]]
        if len(replacement) != item["replacement_bytes"]:
            raise ValueError("A fragment ledger does not identify its replacement bytes")
        edits.append(Edit(item["start"], item["end"], replacement, item["reason"]))
        delta += len(replacement) - (item["end"] - item["start"])
    edits = unique_edits(edits + reference_edits)
    end = unit["end"]["offset"]
    if any(not source_start <= edit.start <= edit.end <= end for edit in edits):
        raise ValueError("A combined fragment edit escapes its source declaration")
    raw = data[source_start:end]
    local = [Edit(edit.start-source_start, edit.end-source_start, edit.replacement, edit.reason) for edit in edits]
    result = apply_edits(raw, local, hashlib.sha256(raw).hexdigest())
    return result, [{"start": edit.start, "end": edit.end, "reason": edit.reason,
                     "replacement_bytes": len(edit.replacement)} for edit in edits]


class NodeGenerator:
    def __init__(self, preview):
        self.preview = preview
        self.g = Generator(preview)
        self.runtime_sha = runtime_pin()
        self.core_path = DEST / "TypedSnapshotCore.inc"
        self.core_sha = sha(self.core_path)
        self.cache = {}

    def load_module(self, module):
        if module in self.cache:
            return self.cache[module]
        relative = module.replace(".", "/") + ".lean"
        entry = self.g.state["stage2"][relative]
        path = TASK / "port/lean" / relative
        data = path.read_bytes()
        source_sha = hashlib.sha256(data).hexdigest()
        if any(source_sha != expected for expected in (
            entry["preflight"]["source_sha256"], self.g.modules[module]["source_sha256"],
            self.g.scope_modules[module]["source_sha256"], self.g.imports["modules"][module]["source_sha256"])):
            raise ValueError("Source and AST inventories disagree: " + module)
        facts_path = ROOT / entry["facts"]
        if sha(facts_path) != entry["facts_sha256"]:
            raise ValueError("Source AST facts changed: " + module)
        facts = [json.loads(line) for line in facts_path.read_bytes().splitlines()]
        validate_facts(path, facts, source_sha)
        wrapper = {item["range"]["start"]["offset"]: item for item in self.g.wrapper_modules[module]["declarations"]}
        provenance = {"source_module": module, "source": path.relative_to(ROOT).as_posix(),
                      "source_sha256": source_sha, "facts": entry["facts"], "facts_sha256": entry["facts_sha256"],
                      "original_source": (TASK / "source/lean" / relative).relative_to(ROOT).as_posix(),
                      "original_source_sha256": sha(TASK / "source/lean" / relative)}
        self.cache[module] = (data, facts, wrapper, provenance)
        return self.cache[module]

    def node_name(self, key):
        unit = self.g.units[key]
        return safe_name(self.g.names.get(key) or self.g.scope_for(unit)["verified_name"])

    def definition_certificate(self, module):
        candidate = self.g.reuse_by_module.get(module)
        if candidate:
            return {"source_module": module, "platform_module": candidate["existing_module"],
                    "canonical_reuse": True, "source_sha256": candidate["existing_sha256"],
                    "ast_validation_sha256": candidate["ast_validation_sha256"]}
        target_module = self.g.platform_module(module)
        path = DEST / "bundles" / (target_module.replace(".", "/") + ".manifest.json")
        if not path.exists():
            raise ValueError("Required Definitions bundle has no final validation manifest: " + module)
        manifest = read(path)
        if "imports" not in manifest:
            raise ValueError("Definitions validation manifest has no independent-route import inventory")
        self.g.check_independent_imports(manifest["imports"])
        if (not manifest.get("validated") or manifest.get("provisional")
                or manifest.get("platform_module") != target_module
                or sha(ROOT / manifest["output"]) != manifest["output_sha256"]
                or sha(ROOT / manifest["source"]) != manifest["source_sha256"]
                or sha(ROOT / manifest["validation"]) != manifest["validation_sha256"]):
            raise ValueError("Required Definitions bundle is unverified or stale: " + module)
        validation = read(ROOT / manifest["validation"])
        if (not validation.get("validated") or not validation.get("kernel_types_equal")
                or not validation.get("standard_axioms_only") or not validation.get("preflights")):
            raise ValueError("Definitions bundle lacks its kernel/axiom certificate: " + module)
        for record in validation["preflights"].values():
            if (record["exit_code"] or record["timed_out"] or not record["source_unchanged"]
                    or not 0 < record["timeout_seconds"] <= 300 or not 0 < record["seconds"] <= 300
                    or sha(ROOT / record["source"]) != record["source_sha256"]
                    or record.get("runtime_sha256") != self.runtime_sha):
                raise ValueError("Definitions preflight is not a current strict 300-second certificate")
        return {"source_module": module, "platform_module": target_module,
                "manifest": path.relative_to(ROOT).as_posix(), "manifest_sha256": sha(path),
                "output_sha256": manifest["output_sha256"], "validation_sha256": manifest["validation_sha256"],
                "provided_elaboration_helpers": [item["theorem_name"] for item in manifest.get("elaboration_only_helpers", [])]}

    def generate(self, key):
        plan = self.g.artifact_plan["nodes"][key]
        target = self.g.units[key]
        name = self.node_name(key)
        source_name = self.g.scope_for(target)["verified_name"]
        if target["graph_names"] != [target["names"][0]] or target["graph_kinds"] != ["theorem"] or target["is_instance_command"]:
            raise ValueError("A node must own one ordinary source theorem")
        graph_name = target["graph_names"][0]
        source_module = target["module"]
        data, facts, wrappers, source_provenance = self.load_module(source_module)
        wrapper = wrappers[target["start"]["offset"]]
        scope = self.g.scope_for(target)
        def_modules = set(plan["definition_modules"])
        local_instances = []
        target_frames = scope["scope_stack"]
        for unit in self.g.units.values():
            if unit["module"] not in plan["source_components"] or not unit["is_local_instance"]:
                continue
            frames = self.g.scope_for(unit)["scope_stack"]
            consumers = [self.g.units[item] for item in plan["source_components"][unit["module"]]]
            active = any(unit["start"]["offset"] < consumer["start"]["offset"]
                         and frames == self.g.scope_for(consumer)["scope_stack"][:len(frames)]
                         for consumer in consumers)
            if not active:
                continue
            if unit["category"] not in DEFINITION_CATEGORIES or len(unit["graph_names"]) != 1:
                raise ValueError("Active local instance has no atomic Definitions owner")
            public = self.g.names.get(unit["id"]) or self.g.graph[unit["graph_names"][0]]["userName"]
            local_instances.append((unit, "attribute [local instance] " + safe_name(public)))
            def_modules.add(unit["module"])
        todo = list(def_modules)
        while todo:
            module = todo.pop()
            if module in self.g.reuse_by_module:
                continue
            for dependency in self.g.artifact_plan["definition_bundles"][module]["imports"]:
                if dependency not in def_modules:
                    def_modules.add(dependency)
                    todo.append(dependency)
        certificates = [self.definition_certificate(module) for module in sorted(def_modules)]
        child_names = {child: self.node_name(child) for child in plan["node_dependencies"]}
        generated_imports = {item["platform_module"] for item in certificates}
        generated_imports.update("Theorems.Thm_" + child.replace(".", "_") for child in child_names.values())
        components = plan["source_components"]
        edges = {module: {self.g.units[dep]["module"] for item in units
                          for dep in self.g.units[item]["direct_unit_dependencies"]
                          if self.g.units[dep]["module"] in components and self.g.units[dep]["module"] != module}
                 for module, units in components.items()}
        component_order = leaves_first(edges)
        # Inline declarations that share a user name across original source files
        # would acquire a different private identity in the concatenated module.
        public_bindings = defaultdict(list)
        for unit_key in plan["inline_units"]:
            unit = self.g.units[unit_key]
            if unit["private"] or unit["deprivate"]:
                raise ValueError("Private inline component needs an explicit validated name correspondence: " + unit_key)
            for declaration in unit["graph_names"]:
                public_bindings[self.g.graph[declaration]["userName"]].append(declaration)
        if any(len(set(names)) != 1 for names in public_bindings.values()):
            raise ValueError("Source components have conflicting inline declaration names")
        inline_names = set(public_bindings)
        for child in child_names:
            child_inline = {self.g.graph[n]["userName"] for item in self.g.artifact_plan["nodes"][child]["inline_units"]
                            for n in self.g.units[item]["graph_names"]}
            if inline_names & child_inline:
                raise ValueError("An imported child theorem would export a conflicting inline helper: " +
                                 str(sorted(inline_names & child_inline)))
        available_names = {n for unit in self.g.units.values()
                           if unit["module"] in def_modules and unit["category"] in DEFINITION_CATEGORIES
                           for n in unit["graph_names"]}
        available_names.update(self.g.units[child]["graph_names"][0] for child in child_names)
        available_names.update(name for item in certificates for name in item.get("provided_elaboration_helpers", []))
        available_names.update(n for item in plan["inline_units"] for n in self.g.units[item]["graph_names"])
        provenance, ledgers, skeletons, helper_records = [], [], [], []
        replay_edits = []
        for module in component_order:
            raw, module_facts, module_wrappers, origin = self.load_module(module)
            generated_imports.update(external_import_union(module, self.g.imports))
            kept = [self.g.units[item] for item in components[module] if item != key]
            reference_consumers = kept + ([target] if module == source_module else [])
            samefile_defs = [unit for unit in self.g.units.values() if unit["module"] == module
                             and module in def_modules and unit["category"] in DEFINITION_CATEGORIES]
            # Imported same-file Definitions are accessible to a helper, but their
            # proof syntax is not being copied into this node.
            filtered = [fact for fact in module_facts if fact["kind"] != "ref" or
                        (fact["const"] not in available_names and not any(
                            unit["start"]["offset"] <= fact["start"]["offset"] <= fact["end"]["offset"] <= unit["end"]["offset"]
                            for unit in samefile_defs))]
            helpers, records = self.g.elaboration_helpers(module, raw, filtered, self.g.modules[module],
                                                          reference_consumers + samefile_defs, def_modules | set(components))
            kept += helpers
            helper_records.extend(records)
            offsets = {unit["start"]["offset"] for unit in kept}
            edits = declaration_edits(self.g.modules[module]["units"], offsets)
            edits += import_edits(self.g.imports["modules"][module]["imports"], [])
            # Replace moved local instances at the original position and scope.
            restored = {unit["start"]["offset"]: command for unit, command in local_instances if unit["module"] == module}
            edits = [type(edit)(edit.start, edit.end, restored[edit.start].encode("utf-8"),
                                "restore moved instance as a local attribute at its original command")
                     if edit.reason == "subtract unselected declaration command" and edit.start in restored else edit for edit in edits]
            removed = [(unit["start"]["offset"], unit["end"]["offset"])
                       for unit in self.g.modules[module]["units"] if unit["start"]["offset"] not in offsets]
            body_allowed = available_names | {n for unit in helpers for n in unit["graph_names"]}
            binding_map = self.g.samefile_binding_map(module, module_facts)
            samefile_renames = set()
            for unit in kept:
                if unit["id"] not in self.g.names:
                    continue
                renamed, _ = rename_bound_constant(unit, module_facts, self.g.scope_for(unit)["verified_name"], self.g.names[unit["id"]])
                for edit in renamed:
                    if not any(left <= edit.start <= edit.end <= right for left, right in removed):
                        edits.append(edit)
                        samefile_renames.add((edit.start, edit.end))
            for fact in module_facts:
                if fact["kind"] == "command" and not fact["isDeclaration"] and fact["syntax"]["syntaxKind"] not in PRESERVED_CONTEXT:
                    raise ValueError("Unsupported retained source context: " + fact["syntax"]["syntaxKind"])
                if fact["kind"] != "ref":
                    continue
                a, b = fact["start"]["offset"], fact["end"]["offset"]
                erased = any(left <= a <= b <= right for left, right in removed)
                in_target = module == source_module and target["start"]["offset"] <= a <= b <= target["end"]["offset"]
                # Inspect the target proof as well as the preserved skeleton.
                if erased and not in_target:
                    continue
                constant = binding_map.get(fact["const"], fact["const"])
                if (in_target and target["nameRange"] and fact["start"] == target["nameRange"]["start"]
                        and fact["end"] == target["nameRange"]["end"]):
                    continue
                if constant in self.g.graph and constant not in body_allowed:
                    if constant == graph_name and module == source_module and fact["start"] == target["nameRange"]["start"] and fact["end"] == target["nameRange"]["end"]:
                        continue
                    raise ValueError("Retained source syntax depends on an unavailable project declaration: " + constant)
                if constant.startswith("_private.") and constant not in self.g.owner:
                    raise ValueError("A private syntax reference lacks a validated full-name correspondence")
                mapped = self.g.mapped_name(constant)
                if mapped != constant and (a, b) not in samefile_renames:
                    rename = from_range({"start": fact["start"], "end": fact["end"]}, mapped,
                                        "rewrite verified source binding to its stable platform name")
                    if in_target or module == source_module and any(
                            context["range"]["start"]["offset"] <= a <= b <= context["range"]["end"]["offset"]
                            for context in scope["context_commands"]):
                        replay_edits.append(rename)
                    if not in_target:
                        edits.append(rename)
            skeleton = apply_edits(raw, unique_edits(edits), origin["source_sha256"])
            skeletons.append(b"section\n" + skeleton + b"\nend\n")
            provenance.append(origin)
            ledgers.append({"source_module": module, "edits": [{"start": edit.start, "end": edit.end,
                              "replacement": edit.replacement.decode("utf-8"), "reason": edit.reason} for edit in edits]})
        # Hoist the target after all component scopes. Only namespace-only source
        # scopes and simple active commands have a reviewed top-level restoration.
        if any(frame["kind"] != "namespace" for frame in target_frames):
            raise ValueError("Original section scope needs an explicit top-level restoration review")
        allowed_active = {"Lean.Parser.Command.open", "Lean.Parser.Command.variable",
                          "Lean.Parser.Command.universe", "Lean.Parser.Command.include", "Lean.Parser.Command.omit"}
        if any(item["syntaxKind"] not in allowed_active for item in scope["context_commands"]):
            raise ValueError("Complex active source context cannot yet be safely hoisted to theorem solution")
        # Qualify only oracle constant references; fvars are never present in the
        # ref facts used here. All edits remain on the original byte coordinates.
        header_ranges = [(target["start"]["offset"], target["valueStart"]["offset"])]
        header_ranges += [(item["range"]["start"]["offset"], item["range"]["end"]["offset"])
                          for item in scope["context_commands"]]
        target_binding_map = self.g.samefile_binding_map(source_module, facts)
        for fact in facts:
            if fact["kind"] != "ref":
                continue
            constant = target_binding_map.get(fact["const"], fact["const"])
            if constant not in self.g.graph:
                continue
            a, b = fact["start"]["offset"], fact["end"]["offset"]
            if fact["start"] == target["nameRange"]["start"] and fact["end"] == target["nameRange"]["end"]:
                continue
            if any(left <= a <= b <= right for left, right in header_ranges):
                public_name = self.g.mapped_name(constant)
                if public_name.startswith("_private."):
                    raise ValueError("Project header/context private reference has no public mapping")
                if data[a:b].decode("utf-8") not in {public_name, "_root_." + public_name}:
                    replay_edits.append(from_range({"start": fact["start"], "end": fact["end"]}, public_name,
                                                   "qualify authoritative project constant in hoisted header/context"))
        replay_edits = unique_edits(replay_edits)
        # Active variable/open/include/omit commands stay at root, in source order.
        contexts = {item["range"]["start"]["offset"]: item["range"] for item in scope["context_commands"]}
        replay_by_offset = {}
        for offset, span in sorted(contexts.items()):
            a, b = span["start"]["offset"], span["end"]["offset"]
            fragment = data[a:b]
            local_edits = [type(edit)(edit.start-a, edit.end-a, edit.replacement, edit.reason)
                           for edit in replay_edits if a <= edit.start <= edit.end <= b]
            replay_by_offset[offset] = apply_edits(fragment, local_edits, hashlib.sha256(fragment).hexdigest()).decode("utf-8")
        for unit, command in local_instances:
            if unit["module"] != source_module:
                continue
            frames = self.g.scope_for(unit)["scope_stack"]
            if unit["start"]["offset"] >= target["start"]["offset"] or frames != target_frames[:len(frames)]:
                continue
            replay_by_offset[unit["start"]["offset"]] = command
        replay = [text for _, text in sorted(replay_by_offset.items())]
        statement, hoisted, statement_ledger = declaration_fragment(data, target, wrapper, name,
                                                                    source_provenance["source_sha256"], stub=True)
        solution, proof_hoisted, proof_ledger = declaration_fragment(data, target, wrapper, "solution",
                                                                    source_provenance["source_sha256"], stub=False)
        if hoisted != proof_hoisted:
            raise ValueError("The statement and proof have different wrapper contexts")
        target_start, target_end = target["start"]["offset"], target["end"]["offset"]
        target_rewrites = [edit for edit in replay_edits if target_start <= edit.start <= edit.end <= target_end]
        header_rewrites = [edit for edit in target_rewrites if edit.end <= target["valueStart"]["offset"]]
        statement, statement_ledger = compose_fragment(data, target, statement, statement_ledger, header_rewrites)
        solution, proof_ledger = compose_fragment(data, target, solution, proof_ledger, target_rewrites)
        replay.extend(item["text"] for item in hoisted)
        active_context = "\n".join(replay) + "\n"
        closing = "\n"
        namespace = scope["namespace"]
        prefixes = [safe_name(".".join(namespace.split(".")[:index]))
                    for index in range(1, len(namespace.split(".")) + 1)] if namespace else []
        namespace_open = "open " + " ".join(prefixes) + " in" if prefixes else ""
        if namespace_open:
            # Translate the authoritative valueStart into the edited fragment.
            # This is not a text search: every preceding edit is in the AST ledger.
            value_start = target["valueStart"]["offset"]
            position = value_start - target["start"]["offset"] + sum(
                edit["replacement_bytes"] - (edit["end"] - edit["start"])
                for edit in proof_ledger if edit["end"] <= value_start)
            if solution[position:position+2] != b":=":
                raise ValueError("The edited proof lost its authoritative := boundary")
            solution = solution[:position+2] + (" " + namespace_open).encode("utf-8") + solution[position+2:]
        imports_text = "\n".join("import " + module for module in sorted(generated_imports)) + "\n\n"
        self.g.check_independent_imports(generated_imports)
        common = imports_text + b"\n".join(skeletons).decode("utf-8") + "\n"
        preamble = common + active_context
        formal = statement.decode("utf-8") + closing
        proof = preamble + solution.decode("utf-8") + closing + "\n#print axioms solution\n"
        slug = name.replace(".", "_")
        stage = DEST / ("nodes-preview" if self.preview else "nodes") / slug
        stage.mkdir(parents=True, exist_ok=True)
        theorem_path, solution_path = stage / ("Thm_" + slug + ".lean"), stage / ("Sol_" + slug + ".lean")
        theorem_path.write_bytes((preamble + formal).encode("utf-8"))
        solution_path.write_bytes(proof.encode("utf-8"))
        core = self.core_path.read_text(encoding="utf-8")
        tail = "\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\nrun_meta do\n"
        original_json = (stage / "original-type.json").relative_to(ROOT).as_posix()
        generated_json = (stage / "generated-type.json").relative_to(ROOT).as_posix()
        original = "import Lean\nimport " + source_module + "\n\n" + core + tail + (
            f"  PiExponentInterfaceSnapshot.exportSnapshot #[`{graph_name}] \"{original_json}\"\n#print axioms {graph_name}\n")
        generated = "import Lean\n" + preamble + formal + "\n" + solution.decode("utf-8") + closing + core + tail + (
            f"  PiExponentInterfaceSnapshot.exportSnapshot #[`{name}, `solution] \"{generated_json}\"\n#print axioms solution\n")
        snapshot_hashes = {}
        for filename, text in (("SnapshotOriginal.lean", original), ("SnapshotGenerated.lean", generated)):
            path = stage / filename
            path.write_bytes(text.encode("utf-8"))
            snapshot_hashes[filename] = sha(path)
        manifest = {"node": key, "theorem_name": name, "source_graph_name": graph_name,
                    "source_user_name": source_name, "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
                    "source_graph_sha256": self.g.input_hashes["verification/decl_graph.jsonl"],
                    "source_components": provenance, "component_order": component_order,
                    "definition_certificates": certificates, "child_nodes": child_names,
                    "source_to_platform_constant_names": {n: self.g.names[unit["id"]]
                    for unit in self.g.units.values() if unit["id"] in self.g.names and unit["module"] in def_modules
                    for n in unit["graph_names"]},
                    "imports": sorted(generated_imports), "preamble": preamble, "formal_statement": formal,
                    "solution_fragment": solution.decode("utf-8"), "active_context": active_context,
                    "source_namespace_open_in_proof_term": namespace_open,
                    "top_level_literal_theorem_solution": True,
                    "scope_closing": closing, "restored_local_instances": [{"unit": unit["id"], "command": command,
                    "source_range": {"start": unit["start"], "end": unit["end"]}} for unit, command in local_instances],
                    "elaboration_only_helpers": helper_records, "source_edits": ledgers,
                    "statement_edits": statement_ledger, "solution_edits": proof_ledger,
                    "project_reference_rewrites": [{"start": edit.start, "end": edit.end,
                    "replacement": edit.replacement.decode("utf-8"), "reason": edit.reason} for edit in replay_edits],
                    "statement": theorem_path.relative_to(ROOT).as_posix(), "statement_sha256": sha(theorem_path),
                    "solution": solution_path.relative_to(ROOT).as_posix(), "solution_sha256": sha(solution_path),
                    "snapshot_sha256": snapshot_hashes, "snapshot_core_sha256": self.core_sha,
                    "runtime_sha256": self.runtime_sha, "input_hashes": self.g.input_hashes,
                    "generator_sha256": sha(Path(__file__)),
                    "provisional": self.preview, "validated": False, "submission_ready": False,
                    "pending": ["all four files compiled within 300 seconds", "source/generated kernel type comparison",
                                "axiom audit with exact planned child theorem dependencies"]}
        if runtime_pin() != self.runtime_sha or sha(self.core_path) != self.core_sha:
            raise ValueError("Runtime/core changed during staging")
        for origin in provenance:
            if sha(ROOT / origin["source"]) != origin["source_sha256"] or sha(ROOT / origin["facts"]) != origin["facts_sha256"]:
                raise ValueError("Source/AST changed during staging")
        (stage / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        return {"node": key, "theorem_name": name, "stage": stage.relative_to(TASK).as_posix(),
                "components": len(components), "inline_units": len(plan["inline_units"]),
                "validated": False, "submission_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview", action="store_true")
    parser.add_argument("--node", action="append", help="Artifact-plan node key or its source theorem name")
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()
    if args.limit is not None and (not args.preview or args.limit <= 0):
        parser.error("--limit must be positive and is preview-only")
    generator = NodeGenerator(args.preview)
    nodes = generator.g.artifact_plan["nodes"]
    keys = []
    for selection in args.node or generator.g.artifact_plan["node_order"]:
        matches = [key for key, node in nodes.items() if key == selection or node["theorem_name_before_platform_renames"] == selection]
        if len(matches) != 1:
            raise ValueError("Node selection is absent or ambiguous: " + selection)
        keys.append(matches[0])
    if args.limit:
        keys = keys[:args.limit]
    generated, rejected = [], []
    for key in keys:
        try:
            generated.append(generator.generate(key))
        except (ValueError, KeyError, StopIteration) as error:
            if not args.preview:
                raise
            rejected.append({"node": key, "reason": str(error) or type(error).__name__})
    report = {"generated": generated, "rejected": rejected, "provisional": args.preview,
              "validated": False, "submission_ready": False, "input_hashes": generator.g.input_hashes}
    destination = DEST / ("nodes-preview" if args.preview else "nodes")
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "generation-report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "input_hashes"}, ensure_ascii=False))


if __name__ == "__main__":
    main()
