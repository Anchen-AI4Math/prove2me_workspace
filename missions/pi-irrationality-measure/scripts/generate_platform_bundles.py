"""Mechanically subtract Definitions bundles at original parser byte ranges.

Generation preserves the entire surrounding source skeleton, including scopes,
local instances and notation. No theorem body is replaced by sorry. Generated
files still require strict compilation, axiom auditing and consumer type checks.
Preview outputs are deliberately isolated and never authorized for publication.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path

from plan_platform_units import make_plan
from plan_platform_artifacts import build_artifacts
from rename_bound_constant import rename_bound_constant
from rename_anonymous_instance import rename_anonymous_instance
from rewrite_ast_imports import external_import_union, import_edits
from skeleton_subtract import declaration_edits
from span_edits import apply_edits, from_range
from validate_ast_facts import validate_facts

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification"
DEFINITION_CATEGORIES = {"definition", "definition_embedded"}
PRESERVED_CONTEXT = {
    "Lean.Parser.Command.namespace", "Lean.Parser.Command.section",
    "Lean.Parser.Command.end", "Lean.Parser.Command.eoi",
    "Lean.Parser.Command.open", "Lean.Parser.Command.variable",
    "Lean.Parser.Command.universe", "Lean.Parser.Command.include",
    "Lean.Parser.Command.omit", "Lean.Parser.Command.set_option",
    "Lean.Parser.Command.attribute", "Lean.Parser.Command.notation",
    "Lean.Parser.Command.infix", "Lean.Parser.Command.infixl",
    "Lean.Parser.Command.infixr", "Lean.Parser.Command.prefix",
    "Lean.Parser.Command.postfix", "Lean.Parser.Command.localNotation",
}


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bundle_module(source_module):
    if not source_module.isascii() or any(not part.isidentifier() for part in source_module.split(".")):
        raise ValueError("Bundle source module needs an ASCII identifier")
    return "Definitions.Def_" + source_module.replace(".", "_")


def comparable(plan):
    return {key: value for key, value in plan.items() if key not in {"provisional", "ready_for_generation"}}


class Generator:
    def __init__(self, preview):
        self.preview = preview
        self.input_hashes = {}

        def load(relative):
            path = TASK / relative
            raw = path.read_bytes()
            self.input_hashes[relative] = hashlib.sha256(raw).hexdigest()
            return json.loads(raw)

        self.state = load("verification/extraction-state.json")
        if not preview and (not self.state.get("complete") or len(self.state["stage2"]) != 875):
            raise ValueError("Final generation requires complete extraction of all 875 modules")
        self.inventory = load("verification/ast-unit-inventory.json")
        self.scopes = load("verification/ast-scope-inventory.json")
        self.wrappers = load("verification/ast-wrapper-inventory.json")
        self.imports = load("verification/ast-import-inventory.json")
        self.reuse = load("platform/definition-reuse-candidates.json")["reuse_candidates"]
        self.overrides = load("platform/deprivate-name-overrides.json")
        self.source_overrides = load("platform/source-theorem-name-overrides.json")
        self.route = load("platform/upload-route.json")
        suffix = "-preview" if preview else ""
        self.unit_plan = load("verification/platform-unit-plan" + suffix + ".json")
        self.artifact_plan = load("verification/platform-artifact-plan" + suffix + ".json")
        if (self.route["source_targets"] != [self.source_overrides["root_source_target"]]
                or self.unit_plan["source_targets"] != self.route["source_targets"]):
            raise ValueError("The plan must follow the fixed original pi_eventual_lower_bound upload route")
        graph_path = DEST / "decl_graph.jsonl"
        raw = graph_path.read_bytes()
        graph_sha = hashlib.sha256(raw).hexdigest()
        self.input_hashes["verification/decl_graph.jsonl"] = graph_sha
        if graph_sha != self.state["stage1"]["facts_sha256"]:
            raise ValueError("The source declaration graph changed")
        if self.overrides["source_graph_sha256"] != graph_sha:
            raise ValueError("Rename overrides describe a different declaration graph")
        if self.source_overrides["source_graph_sha256"] != graph_sha:
            raise ValueError("Source theorem overrides describe a different declaration graph")
        self.graph = {row["name"]: row for row in (json.loads(line) for line in raw.splitlines())}
        current_plan = make_plan(self.inventory, list(self.graph.values()))
        if comparable(current_plan) != comparable(self.unit_plan):
            raise ValueError("Unit plan is stale; refresh it from the current AST inventories")
        current_artifacts = build_artifacts(self.unit_plan, self.scopes, self.reuse)
        if comparable(current_artifacts) != comparable(self.artifact_plan):
            raise ValueError("Artifact plan is stale; refresh it from the current unit plan")
        if self.inventory["unmatched"]:
            raise ValueError("Unmatched declaration owners remain")
        self.units = {unit["id"]: unit for unit in self.unit_plan["units"]}
        self.modules = {item["module"]: item for item in self.inventory["modules"]}
        self.scope_modules = {item["source"].removesuffix(".lean").replace("/", "."): item
                              for item in self.scopes["modules"]}
        self.wrapper_modules = {item["module"]: item for item in self.wrappers["modules"]}
        self.reuse_by_module = {item["source_module"]: item for item in self.reuse}
        self.overrides_by_unit = {item["unit"]: item for item in self.overrides["proposed_overrides"]}
        self.names = {}
        self.name_errors = {}
        self.anonymous_instance_units = set()
        self.owner = {name: key for key, unit in self.units.items() for name in unit["graph_names"]}
        self.public_name_by_constant = {}
        for override in self.source_overrides["planned_overrides"]:
            source_name, public_name = override["source_name"], override["public_name"]
            row = self.graph[source_name]
            if (source_name == self.source_overrides["root_source_target"]
                    or source_name in self.route["source_targets"]
                    or row["module"] != override["source_module"]
                    or row["kind"] != "theorem" or row["isPrivate"] or row["isInstance"]
                    or source_name.rpartition(".")[0] != public_name.rpartition(".")[0]
                    or not public_name.isascii() or any(not part.isidentifier() for part in public_name.split("."))):
                raise ValueError("Source override must rename one ordinary public theorem in the same namespace")
            if source_name in self.public_name_by_constant:
                raise ValueError("A source theorem has duplicate name overrides")
            self.public_name_by_constant[source_name] = public_name
        seen = defaultdict(list)
        for key, unit in self.units.items():
            if not unit["deprivate"]:
                continue
            scope = self.scope_for(unit)
            name = scope["verified_name"]
            if not name or not unit["nameRange"]:
                if (unit["nameRange"] is None and unit["nameText"] is None
                        and unit["is_instance_command"] and unit["is_local_instance"]
                        and len(unit["graph_names"]) == 1
                        and self.graph[unit["graph_names"][0]]["kind"] == "theorem"
                        and self.graph[unit["graph_names"][0]]["isPrivate"]):
                    name = self.graph[unit["graph_names"][0]]["userName"]
                    if name.rpartition(".")[0] != scope["namespace"]:
                        self.name_errors[key] = "Anonymous instance namespace disagrees with the source scope: " + key
                        continue
                    self.anonymous_instance_units.add(key)
                else:
                    self.name_errors[key] = "A required private declaration has no explicit source binding: " + key
                    continue
            override = self.overrides_by_unit.get(key)
            if override:
                if override["source_name"] not in unit["graph_names"]:
                    raise ValueError("Rename override does not identify this source declaration")
                name = override["public_name"]
            if not name.isascii() or any(not part.isidentifier() for part in name.split(".")):
                self.name_errors[key] = "A deprivatized binding needs an explicit ASCII name: " + key
                continue
            self.names[key] = name
            seen[name].append(key)
        public = {row["userName"] for row in self.graph.values() if not row["isPrivate"]}
        for source_name, public_name in self.public_name_by_constant.items():
            if public_name in public or public_name in seen:
                raise ValueError("A source theorem override collides with another source declaration")
            key = self.owner.get(source_name)
            if key is not None:
                unit = self.units[key]
                if unit["graph_names"] != [source_name] or not unit["nameRange"]:
                    raise ValueError("A renamed source theorem does not have one explicit atomic binding")
                self.names[key] = public_name
                seen[public_name].append(key)
        if len(set(self.public_name_by_constant.values())) != len(self.public_name_by_constant):
            raise ValueError("Public source theorem override names are not distinct")
        for name, keys in seen.items():
            if len(keys) != 1 or name in public:
                for key in keys:
                    self.name_errors[key] = "Deprivatized name collides with another source binding: " + name
        if not preview:
            if self.name_errors:
                raise ValueError("Final generation has unresolved source bindings: " + str(self.name_errors))
            if (not self.state.get("complete") or len(self.state["stage2"]) != 875
                    or len(self.inventory["modules"]) != 875
                    or not self.unit_plan["ready_for_generation"]
                    or not self.artifact_plan["ready_for_generation"]
                    or self.unit_plan.get("provisional") or self.artifact_plan.get("provisional")):
                raise ValueError("Final generation requires all 875 modules and reviewed final plans")
            for override in self.overrides["proposed_overrides"]:
                if (not override["binding_and_reference_rewrite_validated"]
                        or not override["kernel_type_comparison_validated"]):
                    raise ValueError("Final generation requires validated private binding/reference renames")
            if any(not override["lean_or_type_validated"] for override in self.source_overrides["planned_overrides"]):
                raise ValueError("Final generation requires validated source theorem binding/reference renames")
        for candidate in self.reuse:
            if (not candidate["validated"] or not candidate["kernel_validated"]
                    or digest(ROOT / candidate["source"]) != candidate["source_sha256"]
                    or digest(ROOT / candidate["existing_source"]) != candidate["existing_sha256"]
                    or digest(ROOT / candidate["ast_validation"]) != candidate["ast_validation_sha256"]):
                raise ValueError("Canonical definition reuse is not currently validated")

    def scope_for(self, unit):
        return next(item for item in self.scope_modules[unit["module"]]["declarations"]
                    if item["range"]["start"] == unit["start"])

    def platform_module(self, source_module):
        candidate = self.reuse_by_module.get(source_module)
        return candidate["existing_module"] if candidate else bundle_module(source_module)

    def check_independent_imports(self, imports):
        excluded = set(self.route["community_adapter_modules_excluded_from_independent_source_imports"])
        forbidden = excluded & set(imports)
        if forbidden:
            raise ValueError("Independent source artifacts cannot import community adapter modules: " + str(sorted(forbidden)))

    def mapped_name(self, graph_name):
        key = self.owner.get(graph_name)
        return self.names.get(key, self.public_name_by_constant.get(graph_name, graph_name))

    def samefile_binding_map(self, module, facts):
        """Resolve abbreviated private IDs only by their own source bindings."""
        bindings = {}
        for unit in self.modules[module]["units"]:
            if not unit["nameRange"]:
                continue
            scope = self.scope_for(dict(unit, module=module))
            candidates = [name for name in unit["graph_names"] if self.graph[name]["userName"] == scope["verified_name"]]
            if len(candidates) != 1:
                continue
            span = unit["nameRange"]
            constants = {fact["const"] for fact in facts if fact["kind"] == "ref"
                         and fact["start"] == span["start"] and fact["end"] == span["end"]}
            if len(constants) != 1:
                raise ValueError("Source binding does not resolve to one same-file oracle identity")
            identity = next(iter(constants))
            if identity in bindings and bindings[identity] != candidates[0]:
                raise ValueError("Oracle identity is ambiguous within the source module")
            bindings[identity] = candidates[0]
        return bindings

    def elaboration_helpers(self, module, data, facts, inventory, selected_units, accessible_modules):
        """Keep only same-file atomic public := rfl lemmas needed by source syntax.

        Such a lemma can disappear from kernel dependency edges after reflexive
        rewriting, while the original proof still requires its name to elaborate.
        This never changes the authoritative planning classification.
        """
        by_name = {name: unit for unit in inventory["units"] for name in unit["graph_names"]}
        selected_offsets = {unit["start"]["offset"] for unit in selected_units}
        retained_names = {name for unit in selected_units for name in unit["graph_names"]}
        accessible_names = set(retained_names)
        for unit in self.units.values():
            if unit["module"] != module and unit["module"] in accessible_modules and unit["category"] in DEFINITION_CATEGORIES:
                accessible_names.update(unit["graph_names"])
        accessible_names.update(name for name in self.unit_plan["preserved_generated_commands"]
                                if self.graph[name]["module"] in accessible_modules)
        references = defaultdict(list)
        for fact in facts:
            if fact["kind"] != "ref" or fact["const"] not in by_name or fact["const"] in retained_names:
                continue
            a, b = fact["start"]["offset"], fact["end"]["offset"]
            consumers = [unit for unit in selected_units if unit["start"]["offset"] <= a <= b <= unit["end"]["offset"]]
            if consumers:
                references[fact["const"]].append({"reference_range": {"start": fact["start"], "end": fact["end"]},
                                                   "consumer_unit": consumers[0]["id"]})
        helpers, records = [], []
        for name, uses in sorted(references.items()):
            unit = by_name[name]
            row = self.graph[name]
            if unit["start"]["offset"] in selected_offsets:
                continue
            if (row["module"] != module or row["kind"] != "theorem" or row["isPrivate"]
                    or row["isInstance"] or unit["graph_names"] != [name]
                    or unit["graph_kinds"] != ["theorem"] or unit["privateTok"]
                    or unit["is_instance_command"] or unit["is_local_instance"]
                    or not unit["nameRange"] or unit["valueStart"] is None):
                raise ValueError("Removed syntactic dependency is not an atomic public rfl helper: " + name)
            scoped = dict(unit, module=module)
            if self.scope_for(scoped)["verified_name"] != row["userName"]:
                raise ValueError("Elaboration helper binding disagrees with its source scope: " + name)
            binding = unit["nameRange"]
            binding_constants = {fact["const"] for fact in facts if fact["kind"] == "ref"
                                 and fact["start"] == binding["start"] and fact["end"] == binding["end"]}
            if binding_constants != {name}:
                raise ValueError("Elaboration helper has no unique source binding identity: " + name)
            wrapper = next(item for item in self.wrapper_modules[module]["declarations"]
                           if item["range"]["start"] == unit["start"])
            if (wrapper["range"]["end"] != unit["end"] or wrapper["nameRange"] != binding or wrapper["wrappers"]):
                raise ValueError("Elaboration helper has a complex or inconsistent wrapper: " + name)
            a, value, b = unit["start"]["offset"], unit["valueStart"]["offset"], unit["end"]["offset"]
            if not a <= value < b or " ".join(data[value:b].decode("utf-8").split()) != ":= rfl":
                raise ValueError("Removed syntactic dependency is not exactly := rfl at its AST value range: " + name)
            dependencies, todo = set(), row["typeDeps"] + row["valueDeps"] + row["constructors"]
            while todo:
                dependency = todo.pop()
                if dependency == name or dependency in dependencies or dependency not in self.graph:
                    continue
                dependencies.add(dependency)
                current = self.graph[dependency]
                todo.extend(current["typeDeps"] + current["valueDeps"] + current["constructors"])
            if not dependencies <= accessible_names:
                raise ValueError("rfl helper has project kernel dependencies outside the Definitions closure: " +
                                 name + "; " + str(sorted(dependencies - accessible_names)))
            key = module + ":" + str(a)
            helpers.append(dict(unit, module=module, id=key, deprivate=False))
            records.append({"unit": key, "theorem_name": name, "range": {"start": unit["start"], "end": unit["end"]},
                            "value_range": {"start": unit["valueStart"], "end": unit["end"]},
                            "normalized_exact_value": ":= rfl", "project_kernel_dependencies": sorted(dependencies),
                            "source_references": uses, "classification_changed": False})
        return helpers, records

    def generate(self, module):
        if module in self.reuse_by_module:
            return {"source_module": module, "reused": True,
                    "platform_module": self.platform_module(module), "generated": False}
        bundle = self.artifact_plan["definition_bundles"][module]
        inventory = self.modules[module]
        relative = module.replace(".", "/") + ".lean"
        entry = self.state["stage2"][relative]
        source = TASK / "port/lean" / relative
        data = source.read_bytes()
        source_sha = hashlib.sha256(data).hexdigest()
        if (source_sha != inventory["source_sha256"]
                or source_sha != entry["preflight"]["source_sha256"]
                or source_sha != self.scope_modules[module]["source_sha256"]
                or source_sha != self.imports["modules"][module]["source_sha256"]):
            raise ValueError("Source/inventory provenance differs: " + module)
        facts_path = ROOT / entry["facts"]
        if digest(facts_path) != entry["facts_sha256"]:
            raise ValueError("Authoritative AST facts changed: " + module)
        facts = [json.loads(line) for line in facts_path.read_bytes().splitlines()]
        validate_facts(source, facts, source_sha)
        selected_units = [self.units[key] for key in bundle["units"]]
        for unit in selected_units:
            if unit["id"] in self.name_errors:
                raise ValueError(self.name_errors[unit["id"]])
            if unit["module"] != module or unit["category"] not in DEFINITION_CATEGORIES:
                raise ValueError("Definitions bundle contains an invalid planned unit")
            if any(self.units[dep]["category"] not in DEFINITION_CATEGORIES
                   for dep in unit["direct_unit_dependencies"]):
                raise ValueError("Definitions cannot import a theorem placeholder")
            wrapper = next(item for item in self.wrapper_modules[module]["declarations"]
                           if item["range"]["start"] == unit["start"])
            if wrapper["range"]["end"] != unit["end"] or wrapper["nameRange"] != unit["nameRange"]:
                raise ValueError("Wrapper facts differ from the retained source command")
        imports = external_import_union(module, self.imports)
        imports += [self.platform_module(dep) for dep in bundle["imports"]]
        self.check_independent_imports(imports)
        accessible_modules, todo = {module}, list(bundle["imports"])
        while todo:
            dependency = todo.pop()
            if dependency in accessible_modules:
                continue
            accessible_modules.add(dependency)
            if dependency not in self.reuse_by_module:
                todo.extend(self.artifact_plan["definition_bundles"][dependency]["imports"])
        helpers, helper_records = self.elaboration_helpers(module, data, facts, inventory,
                                                           selected_units, accessible_modules)
        selected_units += helpers
        kept_offsets = {unit["start"]["offset"] for unit in selected_units}
        removed = [(unit["start"]["offset"], unit["end"]["offset"])
                   for unit in inventory["units"] if unit["start"]["offset"] not in kept_offsets]

        def retained(start, end):
            for left, right in removed:
                if left <= start <= end <= right:
                    return False
                if max(start, left) < min(end, right):
                    raise ValueError("A reference/rename straddles a removed source command")
            return True

        # Keep scopes, attributes and notation exactly; reject unhandled command
        # forms instead of guessing whether their elaboration side effects matter.
        for fact in facts:
            if fact["kind"] != "command" or fact["isDeclaration"]:
                continue
            if fact["syntax"]["syntaxKind"] not in PRESERVED_CONTEXT:
                raise ValueError("Unsupported preserved context command: " + fact["syntax"]["syntaxKind"])
        edits = declaration_edits(inventory["units"], kept_offsets)
        edits += import_edits(self.imports["modules"][module]["imports"], imports)
        rename_records = []
        rename_constants = set()
        for unit in selected_units:
            if unit["id"] not in self.names:
                continue
            anonymous_record = None
            if unit["id"] in self.anonymous_instance_units:
                wrapper = next(item for item in self.wrapper_modules[module]["declarations"]
                               if item["range"]["start"] == unit["start"])
                renamed, constant, anonymous_record = rename_anonymous_instance(
                    unit, facts, self.graph[unit["graph_names"][0]], module, data,
                    self.names[unit["id"]], wrapper)
            else:
                renamed, constant = rename_bound_constant(
                    unit, facts, self.scope_for(unit)["verified_name"], self.names[unit["id"]])
            edits.extend(edit for edit in renamed if retained(edit.start, edit.end))
            rename_constants.add(constant)
            rename_records.append({"unit": unit["id"], "oracle_binding_identity": constant,
                                   "public_name": self.names[unit["id"]],
                                   "source_binding_range": unit["nameRange"],
                                   "anonymous_instance_binding": anonymous_record})
        # A retained notation/attribute may still refer to a declaration removed
        # by subtraction. It has to be imported as a proved definition or rejected.
        removed_constants = {name for unit in inventory["units"]
                             if unit["start"]["offset"] not in kept_offsets for name in unit["graph_names"]}
        allowed_constants = {name for unit in selected_units for name in unit["graph_names"]}
        # The oracle abbreviates private names. Resolve them exclusively through
        # binding ranges in this file, never through their cross-file spelling.
        local_binding_owners = {}
        for unit in inventory["units"]:
            if not unit["nameRange"]:
                continue
            binding = unit["nameRange"]
            constants = {fact["const"] for fact in facts if fact["kind"] == "ref"
                         and fact["start"] == binding["start"] and fact["end"] == binding["end"]}
            for constant in constants:
                previous = local_binding_owners.get(constant)
                if previous is not None and previous != unit["start"]["offset"]:
                    raise ValueError("An oracle binding identity is ambiguous within the source file")
                local_binding_owners[constant] = unit["start"]["offset"]
        for record in rename_records:
            if record["anonymous_instance_binding"] is not None:
                local_binding_owners[record["oracle_binding_identity"]] = self.units[record["unit"]]["start"]["offset"]
        foreign_ranges = set()
        for fact in facts:
            if fact["kind"] != "ref" or not retained(fact["start"]["offset"], fact["end"]["offset"]):
                continue
            if fact["const"] in removed_constants and fact["const"] not in allowed_constants:
                raise ValueError("Retained context references a removed declaration: " + fact["const"])
            owner_offset = local_binding_owners.get(fact["const"])
            if owner_offset is not None and owner_offset not in kept_offsets:
                raise ValueError("Retained context references a removed local binding: " + fact["const"])
            target_key = self.owner.get(fact["const"])
            if target_key is not None and self.units[target_key]["module"] != module:
                target = self.units[target_key]
                if target["category"] not in DEFINITION_CATEGORIES or target["module"] not in accessible_modules:
                    raise ValueError("Retained syntax references an unplanned project dependency: " + fact["const"])
            if target_key in self.names and self.units[target_key]["module"] != module:
                if target_key in self.name_errors:
                    raise ValueError(self.name_errors[target_key])
                span = (fact["start"]["offset"], fact["end"]["offset"])
                if span not in foreign_ranges:
                    edits.append(from_range({"start": fact["start"], "end": fact["end"]},
                                            self.names[target_key], "rename exact foreign graph constant reference"))
                    foreign_ranges.add(span)
            elif fact["const"].startswith("_private.") and owner_offset is None and target_key is None:
                raise ValueError("Private reference has no unambiguous file binding or full graph identity: " + fact["const"])
        result = apply_edits(data, edits, source_sha)
        # Independently rebuild left-to-right as a structural check on the edits.
        cursor, chunks = 0, []
        for edit in sorted(edits, key=lambda item: (item.start, item.end)):
            chunks.extend([data[cursor:edit.start], edit.replacement])
            cursor = edit.end
        chunks.append(data[cursor:])
        if result != b"".join(chunks):
            raise ValueError("Independent byte reconstruction disagrees")
        target_module = self.platform_module(module)
        destination = DEST / ("bundles-preview" if self.preview else "bundles")
        path = destination / (target_module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(result)
        report = {"source_module": module, "platform_module": target_module,
                  "source": source.relative_to(ROOT).as_posix(), "source_sha256": source_sha,
                  "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
                  "original_source": (TASK / "source/lean" / relative).relative_to(ROOT).as_posix(),
                  "original_source_sha256": digest(TASK / "source/lean" / relative),
                  "facts": entry["facts"], "facts_sha256": entry["facts_sha256"],
                  "output": path.relative_to(ROOT).as_posix(), "output_sha256": digest(path),
                  "selected_units": bundle["units"], "imports": sorted(set(imports)),
                  "elaboration_only_helpers": helper_records,
                  "renames": rename_records,
                  "kept_local_instances": [unit["id"] for unit in selected_units if unit["is_local_instance"]],
                  "source_skeleton_preserved": True, "full_definition_proofs_preserved": True,
                  "independent_byte_reconstruction_equal": True,
                  "source_unchanged": digest(source) == source_sha,
                  "provisional": self.preview, "validated": False, "submission_ready": False,
                  "pending": ["strict compilation within 300 seconds", "standard axiom audit",
                              "definition and consumer kernel type comparison"],
                  "input_hashes": self.input_hashes,
                  "edits": [{"start": edit.start, "end": edit.end, "reason": edit.reason,
                             "replacement": edit.replacement.decode("utf-8")} for edit in edits]}
        if not report["source_unchanged"]:
            raise ValueError("Source changed during mechanical generation")
        path.with_suffix(".manifest.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview", action="store_true")
    parser.add_argument("--module", action="append", help="Generate only named source modules")
    parser.add_argument("--limit", type=int, help="Limit the number of preview bundles")
    args = parser.parse_args()
    if args.limit is not None and (not args.preview or args.limit <= 0):
        parser.error("--limit is a positive preview-only option")
    generator = Generator(args.preview)
    modules = args.module or generator.artifact_plan["definition_order"]
    if args.limit:
        modules = modules[:args.limit]
    reports, rejected = [], []
    for module in modules:
        try:
            reports.append(generator.generate(module))
        except (ValueError, KeyError, StopIteration) as error:
            if not args.preview:
                raise
            rejected.append({"source_module": module, "reason": str(error) or type(error).__name__})
    report = {"provisional": args.preview, "validated": False, "submission_ready": False,
              "generated": reports, "rejected": rejected, "input_hashes": generator.input_hashes}
    destination = DEST / ("bundles-preview" if args.preview else "bundles")
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "generation-report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"provisional": args.preview, "generated_bundles": sum(not item.get("reused") for item in reports),
                      "reused_bundles": sum(bool(item.get("reused")) for item in reports),
                      "rejected": rejected, "validated": False, "submission_ready": False}))


if __name__ == "__main__":
    main()
