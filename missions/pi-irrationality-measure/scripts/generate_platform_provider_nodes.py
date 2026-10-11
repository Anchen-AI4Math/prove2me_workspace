"""Stage provider-plan nodes without Lean, network, or submission readiness.

Imports are planned witnesses, never certificates. Source scopes are restored
by the authoritative AST context adapter. Private copies have binding-specific
aliases and actual OwnModule CI collectors; no private kernel number is guessed.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path

from generate_platform_nodes import NodeGenerator, compose_fragment, safe_name, unique_edits
from generate_platform_provider_bundles import ProviderGenerator, resolve_recorded_input
from generate_platform_bundles import DEFINITION_CATEGORIES, PRESERVED_CONTEXT
from generate_independent_node import runtime_pin
from plan_platform_artifacts import leaves_first
from private_node_binding import isolate_private_binding, collector_code, source_inline_snapshot_code
from restore_node_context import restore_context
from platform_statement import declaration_fragment
from rename_bound_constant import rename_bound_constant
from rewrite_ast_imports import external_import_union, import_edits
from skeleton_subtract import declaration_edits
from span_edits import Edit, apply_edits, from_range

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification/provider-nodes-preview"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def edit_record(edit):
    return {"start": edit.start, "end": edit.end,
            "replacement": edit.replacement.decode("utf-8"), "reason": edit.reason}


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def public_inline_snapshot_code(records, output, *, generated):
    """Request every ordinary/derived public CI by its graph identity.

    A source macro is preserved atomically. Its companion identities come from
    the graph, not a guessed suffix; the actual environment must contain each.
    """
    requests = ", ".join("(" + json.dumps(r["generated_name"] if generated else r["source_graph_name"]) +
                         ", " + json.dumps(r["source_module"]) + ")" for r in records)
    owner_check = '''
    unless (env.getModuleIdxFor? actualName).isNone do
      throwError "Generated public inline binding was inherited instead of retained: {actualName}"
''' if generated else '''
    let some idx := env.getModuleIdxFor? actualName
      | throwError "Original public helper is not imported: {actualName}"
    unless env.header.moduleNames[idx.toNat]?.map Lean.Name.toString == some sourceModule do
      throwError "Original public helper owner differs from graph module: {actualName}"
'''
    return '''
open Lean Meta in
run_meta do
  let requests : Array (String × String) := #[REQUESTS]
  let env ← Lean.getEnv
  let mut actualNames : Array Lean.Name := #[]
  for (graphName, sourceModule) in requests do
    let names := env.constants.toList.filterMap fun (name, _) =>
      if name.toString == graphName then some name else none
    unless names.length == 1 do
      throwError "Expected one public inline CI for {graphName}, found {names.length}"
    let actualName := names.head!
    let some ci := env.find? actualName | throwError "Missing public inline CI"
    match ci with
    | .thmInfo _ => pure ()
    | _ => throwError "Public inline companion is not a theorem: {actualName}"
    if ci.type.hasMVar || ci.type.hasFVar || ci.type.hasLooseBVars then
      throwError "Public inline type is not closed: {actualName}"
OWNER
    let axioms ← Lean.collectAxioms actualName
    unless axioms.all (fun n => n == `propext || n == `Classical.choice || n == `Quot.sound) do
      throwError "Public inline helper has nonstandard axioms: {actualName}"
    actualNames := actualNames.push actualName
  PiExponentInterfaceSnapshot.exportSnapshot actualNames OUTPUT
'''.replace("REQUESTS", requests).replace("OWNER", owner_check).replace("OUTPUT",json.dumps(output))


class ProviderNodeGenerator(NodeGenerator):
    def __init__(self):
        self.preview = True
        self.g = ProviderGenerator()
        self.runtime_sha = runtime_pin()
        self.core_path = TASK / "verification/TypeOnlyTheoremSnapshotCore.inc"
        self.core_sha = sha(self.core_path)
        self.cache = {}
        self.layout_cache = {}
        self.inventory_cache = {}

    def definition_closure(self, roots):
        todo, seen = list(roots), set()
        while todo:
            module = todo.pop()
            if module in seen:
                continue
            seen.add(module)
            if module not in self.g.reuse_by_module:
                todo.extend(self.g.artifact_plan["definition_bundles"][module]["imports"])
        return seen

    def node_layout(self, key):
        """Compute actual retained commands, including elaboration-only rfl.

        This is also used for imported node witnesses, so the collision check
        examines what each source skeleton exports rather than just plan names.
        """
        if key in self.layout_cache:
            return self.layout_cache[key]
        g, plan = self.g, self.g.artifact_plan["nodes"][key]
        target = g.units[key]
        def_modules = set(plan["definition_modules"])
        local_instances = []
        for unit in g.units.values():
            if unit["module"] not in plan["source_components"] or not unit["is_local_instance"]:
                continue
            frames = g.scope_for(unit)["scope_stack"]
            consumers = [g.units[item] for item in plan["source_components"][unit["module"]]]
            if not any(unit["start"]["offset"] < consumer["start"]["offset"]
                       and frames == g.scope_for(consumer)["scope_stack"][:len(frames)]
                       for consumer in consumers):
                continue
            if unit["category"] not in DEFINITION_CATEGORIES or len(unit["graph_names"]) != 1:
                raise ValueError("Active local instance has no atomic proved Definition owner: " + unit["id"])
            name = safe_name(g.names.get(unit["id"]) or g.graph[unit["graph_names"][0]]["userName"])
            local_instances.append((unit, "attribute [local instance] " + name))
            def_modules.add(unit["module"])
        def_modules = self.definition_closure(def_modules)
        available = {n for u in g.units.values() if u["module"] in def_modules
                     and u["category"] in DEFINITION_CATEGORIES for n in u["graph_names"]}
        available.update(n for child in plan["node_dependencies"] for n in g.units[child]["graph_names"])
        available.update(n for h in plan["inline_units"] for n in g.units[h]["graph_names"])
        kept_by_module, records = {}, []
        for module, component in plan["source_components"].items():
            raw, facts, _, _ = self.load_module(module)
            kept = [g.units[item] for item in component if item != key]
            samefile_defs = [u for u in g.units.values() if u["module"] == module
                             and module in def_modules and u["category"] in DEFINITION_CATEGORIES]
            filtered = [f for f in facts if f["kind"] != "ref" or
                        (f["const"] not in available and not any(
                            u["start"]["offset"] <= f["start"]["offset"] <= f["end"]["offset"] <= u["end"]["offset"]
                            for u in samefile_defs))]
            try:
                helpers, evidence = g.elaboration_helpers(module, raw, filtered, g.modules[module],
                                                           kept + ([target] if module == target["module"] else []) + samefile_defs,
                                                           def_modules | set(plan["source_components"]))
            except ValueError as error:
                raise ValueError("Node " + key + " component " + module + ": " + str(error)) from error
            for unit in kept + helpers:
                if unit["private"] and (len(unit["graph_names"]) != 1 or unit["graph_kinds"] not in [["theorem"],["def"]]
                                        or unit["is_instance_command"] or unit["is_local_instance"]):
                    raise ValueError("Pending: private inline command is not one ordinary theorem/def/abbrev: " + unit["id"] +
                                     "; kinds=" + str(unit["graph_kinds"]))
                if not unit["private"] and (not unit["graph_names"] or unit["graph_kinds"] != ["theorem"]):
                    raise ValueError("Pending: public inline command is not a complete theorem-only atomic unit: " + unit["id"])
            kept_by_module[module] = kept + helpers
            records.extend(evidence)
        result = {"definitions": def_modules, "local_instances": local_instances,
                  "kept": kept_by_module, "elaboration_only_helpers": records}
        self.layout_cache[key] = result
        return result

    def provider_inventory(self, kind, key):
        cache_key = (kind, key)
        if cache_key in self.inventory_cache:
            return self.inventory_cache[cache_key]
        g = self.g
        if kind == "definition":
            if key in g.reuse_by_module:
                units = [u for u in g.units.values() if u["module"] == key and u["category"] in DEFINITION_CATEGORIES]
                helpers, records = [], []
            else:
                units = [g.units[u] for u in g.artifact_plan["definition_bundles"][key]["units"]]
                raw, facts, _, _ = self.load_module(key)
                try:
                    helpers, records = g.elaboration_helpers(key, raw, facts, g.modules[key], units,
                                                             self.definition_closure([key]))
                except ValueError as error:
                    raise ValueError("Definition provider " + key + ": " + str(error)) from error
            selected = units + helpers
        else:
            layout = self.node_layout(key)
            selected = [g.units[key]] + [u for items in layout["kept"].values() for u in items]
            records = layout["elaboration_only_helpers"]
        result = []
        for unit in selected:
            for name in unit["graph_names"]:
                # Private inline copies are locally isolated by this variant.
                if g.graph[name]["isPrivate"] and unit["id"] not in g.names:
                    continue
                result.append({"name": g.mapped_name(name), "source_graph_name": name,
                               "unit": unit["id"], "provider_kind": kind, "provider": key,
                               "elaboration_only": any(r["unit"] == unit["id"] for r in records)})
        self.inventory_cache[cache_key] = result
        return result

    def import_collision_inventory(self, key):
        nodes, todo, definitions = set(), [key], set()
        while todo:
            node = todo.pop()
            if node in nodes:
                continue
            nodes.add(node)
            layout = self.node_layout(node)
            definitions.update(layout["definitions"])
            todo.extend(self.g.artifact_plan["nodes"][node]["node_dependencies"])
        by_name = defaultdict(list)
        for kind, keys in (("node", nodes), ("definition", definitions)):
            for item in sorted(keys):
                try:
                    bindings = self.provider_inventory(kind, item)
                except ValueError as error:
                    raise ValueError("Import closure of " + key + ", " + kind + " provider " + item + ": " + str(error)) from error
                for binding in bindings:
                    by_name[binding["name"]].append(binding)
        collisions = {name: rows for name, rows in by_name.items()
                      if len({(r["provider_kind"], r["provider"]) for r in rows}) > 1}
        report = {"nodes": sorted(nodes), "definitions": sorted(definitions),
                  "public_bindings": dict(sorted(by_name.items())), "collisions": collisions,
                  "includes_elaboration_only_helpers": True,
                  "actual_environment_validated": False, "planned_source_witness_only": True}
        if collisions:
            error = ValueError("Public retained helper collision in whole import closure: " + str(sorted(collisions)))
            error.collision_report = report
            raise error
        return report

    def dependency_witness(self, module):
        g = self.g
        units = [u for u in g.units.values() if u["module"] == module and u["category"] in DEFINITION_CATEGORIES]
        origin = self.load_module(module)[3]
        return {"source_module": module, "platform_module": g.platform_module(module),
                "selected_units": [u["id"] for u in units], "source_witness": origin,
                "canonical_reuse": module in g.reuse_by_module,
                "validated": False, "planned_dependency_only": True,
                "actual_olean_and_certificate_required": True}

    def generate(self, key):
        g, plan = self.g, self.g.artifact_plan["nodes"][key]
        target, name = g.units[key], self.node_name(key)
        if (target["graph_kinds"] != ["theorem"] or len(target["graph_names"]) != 1
                or target["is_instance_command"]):
            raise ValueError("Pending: target is mixed/macro/instance rather than one ordinary theorem")
        graph_name, module = target["graph_names"][0], target["module"]
        data, facts, wrappers, origin = self.load_module(module)
        scope, wrapper = g.scope_for(target), wrappers[target["start"]["offset"]]
        layout = self.node_layout(key)
        collision_inventory = self.import_collision_inventory(key)
        certificates = [self.dependency_witness(m) for m in sorted(layout["definitions"])]
        child_names = {child: self.node_name(child) for child in plan["node_dependencies"]}
        child_witnesses = {child: {"theorem_name": child_names[child],
                                  "source_witness": self.load_module(g.units[child]["module"])[3],
                                  "source_unit": g.units[child], "validated": False,
                                  "planned_dependency_only": True} for child in child_names}
        imports = {c["platform_module"] for c in certificates}
        imports.update("Theorems.Thm_" + n.replace(".", "_") for n in child_names.values())
        imports.add("Lean")
        available = {n for rows in collision_inventory["public_bindings"].values() for r in rows
                     for n in [r["source_graph_name"]]}
        available.update(n for u in g.units.values() if u["module"] in layout["definitions"]
                         and u["category"] in DEFINITION_CATEGORIES for n in u["graph_names"])
        available.update(n for items in layout["kept"].values() for u in items for n in u["graph_names"])
        available.discard(graph_name)
        components = plan["source_components"]
        edges = {m: {g.units[d]["module"] for u in units for d in g.units[u]["direct_unit_dependencies"]
                     if g.units[d]["module"] in components and g.units[d]["module"] != m}
                 for m, units in components.items()}
        order = leaves_first(edges)
        records, structural_by_module = [], defaultdict(list)
        public_records = [{"source_graph_name": n, "source_module": u["module"],
                           "source_unit": u["id"], "generated_name": g.mapped_name(n),
                           "source_command_range": {"start": u["start"], "end": u["end"]},
                           "generated_companion": g.graph[n]["startLine"] == 0}
                          for items in layout["kept"].values() for u in items if not u["private"]
                          for n in u["graph_names"]]
        for m in order:
            raw, fs, ws, _ = self.load_module(m)
            for unit in layout["kept"][m]:
                if not unit["private"]:
                    continue
                exported_type_roots = {graph_name} | {r["source_graph_name"] for r in public_records}
                todo = [dep for n in exported_type_roots for dep in g.graph[n]["typeDeps"]]
                type_constants = set()
                while todo:
                    dep = todo.pop()
                    if dep in type_constants or dep not in g.graph:
                        continue
                    type_constants.add(dep)
                    todo.extend(g.graph[dep]["typeDeps"])
                if any(n in type_constants for n in unit["graph_names"]):
                    raise ValueError("Pending: exported target/public inline interface type requires a private inline helper")
                edits, record = isolate_private_binding(unit, fs, g.graph[unit["graph_names"][0]],
                    g.scope_for(unit), ws[unit["start"]["offset"]], m, raw, name)
                # A dotted declId must retain its namespace-relative prefix.
                ns = g.scope_for(unit)["namespace"]
                prefix = ns + "." if ns else ""
                if not record["source_user_name"].startswith(prefix):
                    raise ValueError("Private helper binding is outside its verified namespace")
                relative = record["source_user_name"][len(prefix):]
                safe_name(relative)
                binding = unit["nameRange"]
                if raw[binding["start"]["offset"]:binding["end"]["offset"]].decode("utf-8") != relative:
                    raise ValueError("Pending: root-qualified/quoted private helper binding")
                relative_alias = record["node_generated_name"][len(prefix):]
                edits = [Edit(e.start, e.end, relative_alias.encode("utf-8"), e.reason)
                         if e.reason == "bind per-node private inline helper alias" else e for e in edits]
                structural_by_module[m].extend(e for e in edits if e.reason != "rewrite same-file bound inline helper reference")
                records.append(record)
        aliases = {r["source_graph_name"]: r["node_generated_name"] for r in records}
        if len(set(aliases.values())) != len(records):
            raise ValueError("Private inline aliases collide")
        provenance, ledgers, skeletons, target_refs = [], [], [], []
        context_spans = [item["range"] for item in scope["context_commands"]]
        for m in order:
            raw, fs, _, source = self.load_module(m)
            imports.update(external_import_union(m, g.imports))
            kept = layout["kept"][m]
            offsets = {u["start"]["offset"] for u in kept}
            removed = [(u["start"]["offset"], u["end"]["offset"]) for u in g.modules[m]["units"]
                       if u["start"]["offset"] not in offsets]
            edits = declaration_edits(g.modules[m]["units"], offsets) + import_edits(g.imports["modules"][m]["imports"], [])
            restoration = {u["start"]["offset"]: command for u, command in layout["local_instances"] if u["module"] == m}
            edits = [Edit(e.start, e.end, restoration[e.start].encode("utf-8"),
                          "restore moved instance as a local attribute at its original command")
                     if e.reason == "subtract unselected declaration command" and e.start in restoration else e for e in edits]
            binding_map = g.samefile_binding_map(m, fs)
            edits.extend(structural_by_module[m])
            binding_pairs = {(u["nameRange"]["start"]["offset"], u["nameRange"]["end"]["offset"])
                             for u in kept if u["nameRange"] and u["private"]}
            for u in kept:
                if u["id"] in g.names:
                    rename_edits, _ = rename_bound_constant(u, fs, g.scope_for(u)["verified_name"], g.names[u["id"]])
                    edits.extend(e for e in rename_edits if not any(a <= e.start <= e.end <= b for a,b in removed))
            refs = []
            for f in fs:
                if f["kind"] == "command" and not f["isDeclaration"] and f["syntax"]["syntaxKind"] not in PRESERVED_CONTEXT:
                    raise ValueError("Pending: unsupported source command/macro " + f["syntax"]["syntaxKind"])
                if f["kind"] != "ref":
                    continue
                a, b = f["start"]["offset"], f["end"]["offset"]
                in_target = m == module and target["start"]["offset"] <= a <= b <= target["end"]["offset"]
                erased = any(left <= a <= b <= right for left,right in removed)
                if erased and not in_target:
                    continue
                if in_target and f["start"] == target["nameRange"]["start"] and f["end"] == target["nameRange"]["end"]:
                    continue
                constant = binding_map.get(f["const"], f["const"])
                if constant in g.graph and constant not in available:
                    raise ValueError("Pending: erased non-rfl syntax dependency has no proved provider: " + constant)
                if constant.startswith("_private.") and constant not in g.owner:
                    raise ValueError("Pending: private reference lacks a unique source binding/FQN owner")
                mapped = aliases.get(constant, g.mapped_name(constant))
                hoisted = m == module and (in_target or any(s["start"]["offset"] <= a <= b <= s["end"]["offset"] for s in context_spans))
                if (a,b) in binding_pairs:
                    continue
                if constant in g.graph and (mapped != constant or hoisted):
                    if mapped.startswith("_private."):
                        raise ValueError("Pending: private provider reference has no public certified binding")
                    e = from_range({"start":f["start"],"end":f["end"]}, mapped,
                                   "rewrite authority-bound project reference to generated FQN")
                    refs.append(e)
                    if not in_target:
                        edits.append(e)
                    if hoisted:
                        target_refs.append(e)
            edits = unique_edits(edits)
            skeleton = apply_edits(raw, edits, source["source_sha256"])
            skeletons.append(b"section\n" + skeleton + b"\nend\n")
            provenance.append(source)
            ledgers.append({"source_module": m, "edits": [edit_record(e) for e in edits],
                            "retained_units": [u["id"] for u in kept]})
        target_refs = unique_edits(target_refs)
        extra = []
        for u, command in layout["local_instances"]:
            frames = g.scope_for(u)["scope_stack"]
            if u["module"] == module and u["start"]["offset"] < target["start"]["offset"] and frames == scope["scope_stack"][:len(frames)]:
                extra.append((u["start"]["offset"], command))
        restored = restore_context(data, facts, scope, origin["source_sha256"], target_refs, extra)
        statement, hoisted, stmt_ledger = declaration_fragment(data, target, wrapper, name, origin["source_sha256"], stub=True)
        solution, proof_hoisted, sol_ledger = declaration_fragment(data, target, wrapper, "solution", origin["source_sha256"], stub=False)
        if hoisted != proof_hoisted:
            raise ValueError("Statement and proof wrapper restoration differs")
        proof_refs = [e for e in target_refs if target["start"]["offset"] <= e.start <= e.end <= target["end"]["offset"]]
        header_refs = [e for e in proof_refs if e.end <= target["valueStart"]["offset"]]
        if any(e.replacement.decode("utf-8") in aliases.values() for e in header_refs):
            raise ValueError("Pending: exported target header exposes an isolated private helper")
        statement, stmt_ledger = compose_fragment(data, target, statement, stmt_ledger, header_refs)
        solution, sol_ledger = compose_fragment(data, target, solution, sol_ledger, proof_refs)
        opens = restored["namespace_opens"]
        namespace_open = "open " + " ".join(opens) + " in" if opens else ""
        if namespace_open:
            v = target["valueStart"]["offset"]
            pos = v-target["start"]["offset"] + sum(e["replacement_bytes"]-(e["end"]-e["start"]) for e in sol_ledger if e["end"] <= v)
            if solution[pos:pos+2] != b":=":
                raise ValueError("Proof no longer has its authoritative value boundary")
            solution = solution[:pos+2] + (" " + namespace_open).encode("utf-8") + solution[pos+2:]
        g.check_independent_imports(imports)
        common = "\n".join("import " + i for i in sorted(imports)) + "\n\n" + b"\n".join(skeletons).decode("utf-8")
        active = restored["preamble"] + "\n".join(h["text"] for h in hoisted) + "\n"
        preamble, closing = common + active, restored["closing"]
        formal, proof = statement.decode("utf-8") + "\n", solution.decode("utf-8") + "\n"
        stage = DEST / name.replace(".", "_")
        stage.mkdir(parents=True, exist_ok=True)
        slug = name.replace(".", "_")
        files = {"Thm_"+slug+".lean": preamble + collector_code(records,"Thm") + formal + closing,
                 "Sol_"+slug+".lean": preamble + collector_code(records,"Sol") + proof + closing + "\n#print axioms solution\n"}
        core = self.core_path.read_text(encoding="utf-8")
        tail = "\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\nrun_meta do\n"
        original_json, generated_json = [(stage/f).relative_to(ROOT).as_posix() for f in ("original-type.json","generated-type.json")]
        original_inline, generated_inline = [(stage/f).relative_to(ROOT).as_posix() for f in ("original-inline-types.json","generated-inline-types.json")]
        original_public, generated_public = [(stage/f).relative_to(ROOT).as_posix() for f in ("original-public-inline-types.json","generated-public-inline-types.json")]
        files["SnapshotOriginal.lean"] = "import Lean\nimport " + module + "\n\n" + core + tail + (
            f"  PiExponentInterfaceSnapshot.exportSnapshot #[`{graph_name}] {json.dumps(original_json)}\n#print axioms {graph_name}\n") + source_inline_snapshot_code(records,original_inline) + public_inline_snapshot_code(public_records,original_public,generated=False)
        files["SnapshotGenerated.lean"] = preamble + collector_code(records,"SnapshotGenerated") + formal + proof + closing + core + tail + (
            f"  PiExponentInterfaceSnapshot.exportSnapshot #[`{name}, `solution] {json.dumps(generated_json)}\n#print axioms solution\n") + collector_code(records,"SnapshotGenerated",emit=False,inline_types_output=generated_inline) + public_inline_snapshot_code(public_records,generated_public,generated=True)
        implementation = ["generate_platform_provider_nodes.py","generate_platform_provider_bundles.py","generate_platform_nodes.py",
                          "generate_platform_bundles.py","restore_node_context.py","private_inline_binding.py","private_node_binding.py","platform_statement.py",
                          "span_edits.py","plan_platform_units_providers.py"]
        manifest = {"schema_version":1,"variant":"all-shared-public-provider-nodes-preview","node":key,"theorem_name":name,
                    "source_graph_name":graph_name,"source_commit":"adc7f1241b42e322a6451854ab7e4b4c146bf78a",
                    "source_components":provenance,"component_order":order,"definition_dependency_witnesses":certificates,
                    "definition_certificates":[],"child_nodes":child_names,"child_dependency_witnesses":child_witnesses,
                    "imports":sorted(imports),"whole_import_closure_inventory":collision_inventory,
                    "preamble":preamble+collector_code(records,"Thm"),"mathematical_preamble":preamble,
                    "solution_preamble":preamble+collector_code(records,"Sol"),
                    "formal_statement":formal+closing,"solution_fragment":proof,
                    "top_level_literal_theorem_solution":True,"restored_target_context":restored,"scope_closing":closing,
                    "restored_local_instances":[{"unit":u["id"],"command":c,"source_range":{"start":u["start"],"end":u["end"]}} for u,c in layout["local_instances"]],
                    "node_generated_names":records,"source_to_generated_private_kernel_names":None,
                    "private_ci_comparison_policy":{"map_required":"source Graph private Name to actual generated CI Name from certified per-artifact environment maps",
                        "type_comparison":"structural kernel Expr JSON with explicit constant Name mapping and universe binder name normalization only",
                        "def_value_comparison":"complete structural kernel Expr JSON; required nonnull for every def/abbrev source and generated row",
                        "theorem_value_comparison":"proof value null; CI type/closed proof/Std3 required",
                        "pretty_string_rewriting_forbidden":True,"validated":False},
                    "public_inline_ci_requests":public_records,
                    "private_map_log_marker":"PI_ISOLATED_PRIVATE_MAP ","kernel_name_mapping_validated":False,
                    "elaboration_only_helpers":layout["elaboration_only_helpers"],"source_edits":ledgers,
                    "statement_edits":stmt_ledger,"solution_edits":sol_ledger,
                    "project_reference_rewrites":[edit_record(e) for e in target_refs],
                    "source_graph_sha256":g.graph_sha,"snapshot_core":self.core_path.relative_to(TASK).as_posix(),
                    "snapshot_core_sha256":self.core_sha,"runtime_sha256":self.runtime_sha,
                    "input_hashes":dict(g.input_hashes),"implementation_sha256":{f:sha(TASK/"scripts"/f) for f in implementation},
                    "inline_type_json_outputs":{"original":original_inline,"generated":generated_inline},
                    "public_inline_type_json_outputs":{"original":original_public,"generated":generated_public},
                    "provisional":True,"validated":False,"submission_ready":False,"full_tree_ready":False,
                    "theorem_proof_values_exported":False,"lean_started":False,"api_used":False,
                    "pending":["actual imported Def OLeans and exact certificates","actual child node statements and certificates",
                               "four exact files compiled within 300 seconds","actual private CI maps, types and proofStd",
                               "original/generated kernel types with only universe-name normalization","publication flow review"]}
        # Check all input pins before committing any stage files.
        for relative, expected in g.input_hashes.items():
            if sha(resolve_recorded_input(relative)) != expected:
                raise ValueError("Input changed during preview; regenerate after extraction hold: " + relative)
        if runtime_pin() != self.runtime_sha or sha(self.core_path) != self.core_sha:
            raise ValueError("Runtime/snapshot core changed during preview")
        for source in provenance + [c["source_witness"] for c in certificates] + [c["source_witness"] for c in child_witnesses.values()]:
            for p,h in (("source","source_sha256"),("facts","facts_sha256"),("original_source","original_source_sha256")):
                if sha(ROOT/source[p]) != source[h]:
                    raise ValueError("Selected source witness changed: " + source[p])
        hashes = {}
        for filename,text in files.items():
            path = stage/filename
            path.write_bytes(text.encode("utf-8"))
            hashes[filename] = sha(path)
        manifest["outputs_sha256"] = hashes
        manifest["statement"] = (stage/("Thm_"+slug+".lean")).relative_to(ROOT).as_posix()
        manifest["solution"] = (stage/("Sol_"+slug+".lean")).relative_to(ROOT).as_posix()
        manifest["statement_sha256"] = hashes["Thm_"+slug+".lean"]
        manifest["solution_sha256"] = hashes["Sol_"+slug+".lean"]
        manifest["snapshot_sha256"] = {f:hashes[f] for f in ("SnapshotOriginal.lean","SnapshotGenerated.lean")}
        write_json(stage/"manifest.json",manifest)
        return {"node":key,"theorem_name":name,"stage":stage.relative_to(TASK).as_posix(),"components":len(order),
                "private_inline_helpers":len(records),"definition_dependencies":len(certificates),"child_dependencies":len(child_names),
                "validated":False,"submission_ready":False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview",action="store_true",required=True)
    parser.add_argument("--theorem",action="append",required=True)
    args = parser.parse_args()
    generator = ProviderNodeGenerator()
    nodes = generator.g.artifact_plan["nodes"]
    reports = []
    for requested in args.theorem:
        keys = [k for k in nodes if k == requested or
                (generator.g.names.get(k) or generator.g.scope_for(generator.g.units[k])["verified_name"]) == requested
                or requested in generator.g.units[k]["graph_names"]]
        if len(keys) != 1:
            reports.append({"requested":requested,"generated":False,"reason":"Theorem is not a unique provider-plan node"})
            continue
        try:
            reports.append(generator.generate(keys[0]))
        except (ValueError, KeyError) as error:
            record = {"requested":requested,"node":keys[0],"generated":False,"reason":str(error),"submission_ready":False}
            if hasattr(error,"collision_report"):
                record["collision_evidence"] = error.collision_report
            reports.append(record)
    report = {"variant":"all-shared-public","input_hashes":generator.g.input_hashes,
              "generator_sha256":sha(Path(__file__)),"results":reports,"lean_started":False,"api_used":False,
              "provisional":True,"full_tree_ready":False,"submission_ready":False}
    write_json(DEST/"generation-report.json",report)
    print(json.dumps({"report":(DEST/"generation-report.json").relative_to(TASK).as_posix(),
                      "results":[{k:v for k,v in r.items() if k != "collision_evidence"} for r in reports]},ensure_ascii=False))


if __name__ == "__main__":
    main()
