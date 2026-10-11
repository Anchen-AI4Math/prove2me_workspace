"""Generate a narrow, unvalidated standalone variant with private inline copies.

Existing generators, accepted stages and global plans are never modified.
Only --preview is supported; Def/child/rename/mixed/interface-dependent cases
remain explicit refusals. Compilation and actual private-name maps are pending.
"""
import argparse
import hashlib
import json
from pathlib import Path

from generate_platform_nodes import NodeGenerator, compose_fragment, safe_name, unique_edits
from generate_platform_bundles import PRESERVED_CONTEXT, DEFINITION_CATEGORIES
from private_inline_binding import isolate_inline_binding, collector_code, source_inline_snapshot_code
from platform_statement import declaration_fragment
from rewrite_ast_imports import external_import_union, import_edits
from skeleton_subtract import declaration_edits
from span_edits import Edit, apply_edits, from_range
from validate_standalone_platform_node import kernel_closure

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
DEST = TASK / "verification/nodes-isolated-preview"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class IsolatedGenerator:
    def __init__(self, context_restorer=None):
        self.base = NodeGenerator(True)
        self.g = self.base.g
        # Future AST restorer hook: callback(raw, target, scope, wrapper,
        # reference_edits) -> {"commands": [str], "namespace_open": str,
        # "closing": str (optional, default newline), "evidence": JSON}.
        # Commands restore active context; wrapper hoists are added below.
        # No shared or accepted generator is modified.
        self.context_restorer = context_restorer
        roots = {dep for unit in self.g.units.values() if unit["category"] == "node"
                 for name in unit["graph_names"] for dep in self.g.graph[name]["typeDeps"]}
        roots |= {name for unit in self.g.units.values() if unit["category"] in DEFINITION_CATEGORIES
                  for name in unit["graph_names"]}
        self.interface_needed = kernel_closure(self.g.graph, roots)

    def generate(self, key):
        g, base = self.g, self.base
        plan = g.artifact_plan["nodes"][key]
        target = g.units[key]
        if plan["definition_modules"] or plan["node_dependencies"]:
            raise ValueError("Pending: isolated variant supports no Definitions or child-node imports")
        module = target["module"]
        if set(plan["source_components"]) != {module}:
            raise ValueError("Pending: cross-file components require an isolation correspondence review")
        if (target["private"] or target["deprivate"] or target["is_instance_command"]
                or target["graph_kinds"] != ["theorem"] or len(target["graph_names"]) != 1
                or key in g.names):
            raise ValueError("Pending: target is not one unchanged public ordinary theorem")
        name = safe_name(g.scope_for(target)["verified_name"])
        if name != target["graph_names"][0]:
            raise ValueError("Pending: source target needs a global rename")
        helpers = [g.units[h] for h in plan["inline_units"]]
        provided = {name, *(n for h in helpers for n in h["graph_names"])}
        missing = kernel_closure(g.graph, provided) - provided
        if missing:
            raise ValueError("Pending: project kernel dependencies have no retained theorem owner: " + str(sorted(missing)))
        raw, facts, wrappers, origin = base.load_module(module)
        scope = g.scope_for(target)
        if self.context_restorer is None and any(frame["kind"] != "namespace" for frame in scope["scope_stack"]):
            raise ValueError("Pending: target section scope cannot yet be hoisted safely")
        allowed_active = {"Lean.Parser.Command.open", "Lean.Parser.Command.variable", "Lean.Parser.Command.universe",
                          "Lean.Parser.Command.include", "Lean.Parser.Command.omit"}
        if self.context_restorer is None and any(item["syntaxKind"] not in allowed_active for item in scope["context_commands"]):
            raise ValueError("Pending: complex active target context")
        records, helper_edits = [], []
        for helper in helpers:
            if helper["module"] != module or helper["id"] in g.names:
                raise ValueError("Pending: helper needs a cross-file/global rename")
            if len(helper["graph_names"]) != 1:
                raise ValueError("Pending: mixed or macro-generated companion theorem command")
            graph_name = helper["graph_names"][0]
            if graph_name in self.interface_needed:
                raise ValueError("Pending: statement/Definitions-required helper needs a public proved provider: " + graph_name)
            edits, record = isolate_inline_binding(helper, facts, g.graph[graph_name], g.scope_for(helper),
                                                   wrappers[helper["start"]["offset"]], module, raw, name)
            if any(row["userName"] == record["node_generated_name"] for row in g.graph.values()):
                raise ValueError("Generated helper alias collides with the original source graph")
            helper_edits.extend(edits)
            records.append(record)
        if len({r["node_generated_name"] for r in records}) != len(records):
            raise ValueError("Generated helper aliases collide")
        retained = helpers + [target]
        spans = [(u["start"]["offset"], u["end"]["offset"]) for u in retained]
        removed = [(u["start"]["offset"], u["end"]["offset"]) for u in g.modules[module]["units"]
                   if u["start"]["offset"] not in {h["start"]["offset"] for h in helpers}]
        bindings = g.samefile_binding_map(module, facts)
        aliases = {r["source_graph_name"]: r["node_generated_name"] for r in records}
        extra_refs = []
        for fact in facts:
            if fact["kind"] == "command" and not fact["isDeclaration"] and fact["syntax"]["syntaxKind"] not in PRESERVED_CONTEXT:
                raise ValueError("Pending: unsupported retained source context: " + fact["syntax"]["syntaxKind"])
            if fact["kind"] != "ref":
                continue
            a, b = fact["start"]["offset"], fact["end"]["offset"]
            in_target = target["start"]["offset"] <= a <= b <= target["end"]["offset"]
            in_helper = any(h["start"]["offset"] <= a <= b <= h["end"]["offset"] for h in helpers)
            if any(left <= a <= b <= right for left, right in removed) and not in_target:
                continue
            if fact["start"] == target["nameRange"]["start"] and fact["end"] == target["nameRange"]["end"]:
                continue
            constant = bindings.get(fact["const"], fact["const"])
            if constant in g.graph and constant not in aliases:
                raise ValueError("Pending: retained syntax uses an unavailable project declaration: " + constant)
            if constant.startswith("_private.") and constant not in g.owner:
                raise ValueError("Pending: unresolved same-file private reference")
            if constant in aliases:
                # Binding occurrences receive the leaf from isolate_inline_binding.
                if any(fact["start"] == h["nameRange"]["start"] and fact["end"] == h["nameRange"]["end"] for h in helpers):
                    continue
                extra_refs.append(from_range({"start": fact["start"], "end": fact["end"]}, aliases[constant],
                                             "rewrite verified project helper reference to node-private alias"))
        all_refs = unique_edits([e for e in helper_edits if e.reason == "rewrite same-file bound inline helper reference"] + extra_refs)
        structural = [e for e in helper_edits if e.reason != "rewrite same-file bound inline helper reference"]
        skeleton_refs = [e for e in all_refs if not any(left <= e.start <= e.end <= right for left, right in removed)]
        structural += skeleton_refs
        edits = declaration_edits(g.modules[module]["units"], {h["start"]["offset"] for h in helpers})
        edits += import_edits(g.imports["modules"][module]["imports"], []) + structural
        skeleton = apply_edits(raw, unique_edits(edits), origin["source_sha256"])
        replay = []
        for item in scope["context_commands"]:
            a, b = item["range"]["start"]["offset"], item["range"]["end"]["offset"]
            fragment = raw[a:b]
            local = [Edit(e.start-a, e.end-a, e.replacement, e.reason) for e in all_refs if a <= e.start <= e.end <= b]
            replay.append(apply_edits(fragment, local, hashlib.sha256(fragment).hexdigest()).decode("utf-8"))
        wrapper = wrappers[target["start"]["offset"]]
        statement, hoisted, statement_ledger = declaration_fragment(raw, target, wrapper, name, origin["source_sha256"], stub=True)
        solution, proof_hoisted, proof_ledger = declaration_fragment(raw, target, wrapper, "solution", origin["source_sha256"], stub=False)
        if hoisted != proof_hoisted:
            raise ValueError("Statement/proof wrapper replay differs")
        restored_context = None
        if self.context_restorer is not None:
            restored_context = self.context_restorer(raw, target, scope, wrapper, all_refs)
            if (not isinstance(restored_context, dict) or not isinstance(restored_context.get("commands"), list)
                    or any(not isinstance(cmd, str) for cmd in restored_context["commands"])
                    or not isinstance(restored_context.get("namespace_open"), str)
                    or not isinstance(restored_context.get("closing", "\n"), str)
                    or "evidence" not in restored_context):
                raise ValueError("AST context restorer has no complete explicit restoration evidence")
            replay = restored_context["commands"]
        target_refs = [e for e in all_refs if target["start"]["offset"] <= e.start <= e.end <= target["end"]["offset"]]
        header_refs = [e for e in target_refs if e.end <= target["valueStart"]["offset"]]
        if header_refs:
            raise ValueError("Pending: exported target header refers to an isolated helper")
        solution, proof_ledger = compose_fragment(raw, target, solution, proof_ledger, target_refs)
        replay.extend(h["text"] for h in hoisted)
        active = "\n".join(replay) + "\n"
        namespace = scope["namespace"]
        prefixes = [safe_name(".".join(namespace.split(".")[:i])) for i in range(1, len(namespace.split("."))+1)] if namespace else []
        namespace_open = "open " + " ".join(prefixes) + " in" if prefixes else ""
        context_closing = "\n"
        if restored_context is not None:
            namespace_open = restored_context["namespace_open"]
            context_closing = restored_context.get("closing", "\n")
        if namespace_open:
            value_start = target["valueStart"]["offset"]
            pos = value_start-target["start"]["offset"] + sum(e["replacement_bytes"]-(e["end"]-e["start"])
                                                              for e in proof_ledger if e["end"] <= value_start)
            if solution[pos:pos+2] != b":=":
                raise ValueError("Authoritative proof boundary changed")
            solution = solution[:pos+2] + (" " + namespace_open).encode("utf-8") + solution[pos+2:]
        imports = sorted(set(external_import_union(module, g.imports)) | {"Lean"})
        g.check_independent_imports(imports)
        common = "\n".join("import " + m for m in imports) + "\n\nsection\n" + skeleton.decode("utf-8") + "\nend\n"
        mathematical_preamble = common + active
        formal = statement.decode("utf-8") + "\n"
        solution_text = solution.decode("utf-8") + "\n"
        stage = DEST / name.replace(".", "_")
        stage.mkdir(parents=True, exist_ok=True)
        slug = name.replace(".", "_")
        theorem_file, solution_file = "Thm_"+slug+".lean", "Sol_"+slug+".lean"
        theorem_preamble = mathematical_preamble + collector_code(records, "Thm")
        proof_preamble = mathematical_preamble + collector_code(records, "Sol")
        source = {
            theorem_file: theorem_preamble + formal + context_closing,
            solution_file: proof_preamble + solution_text + context_closing + "\n#print axioms solution\n"}
        core = base.core_path.read_text(encoding="utf-8")
        tail = "\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\nrun_meta do\n"
        original_json = (stage/"original-type.json").relative_to(ROOT).as_posix()
        generated_json = (stage/"generated-type.json").relative_to(ROOT).as_posix()
        original_inline = (stage/"original-inline-types.json").relative_to(ROOT).as_posix()
        generated_inline = (stage/"generated-inline-types.json").relative_to(ROOT).as_posix()
        source["SnapshotOriginal.lean"] = "import Lean\nimport " + module + "\n\n" + core + tail + (
            f"  PiExponentInterfaceSnapshot.exportSnapshot #[`{name}] {json.dumps(original_json)}\n#print axioms {name}\n")
        source["SnapshotOriginal.lean"] += source_inline_snapshot_code(records, original_inline)
        source["SnapshotGenerated.lean"] = mathematical_preamble + collector_code(records, "SnapshotGenerated") + formal + solution_text + context_closing + core + tail + (
            f"  PiExponentInterfaceSnapshot.exportSnapshot #[`{name}, `solution] {json.dumps(generated_json)}\n#print axioms solution\n")
        source["SnapshotGenerated.lean"] += collector_code(records, "SnapshotGenerated", emit=False, inline_types_output=generated_inline)
        outputs = {}
        for filename, text in source.items():
            path = stage/filename
            path.write_bytes(text.encode("utf-8"))
            outputs[filename] = sha(path)
        manifest = {"schema_version": 1, "variant": "isolated-standalone-preview", "node": key,
                    "theorem_name": name, "source_graph_name": name, "source_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a",
                    "source_components": [origin], "definition_certificates": [], "child_nodes": {},
                    "imports": imports, "preamble": theorem_preamble, "mathematical_preamble": mathematical_preamble,
                    "formal_statement": formal + context_closing, "declaration_statement": formal,
                    "solution_fragment": solution_text,
                    "top_level_literal_theorem_solution": True, "node_generated_names": records,
                    "restored_target_context": restored_context,
                    "scope_closing": context_closing,
                    "private_map_log_marker": "PI_ISOLATED_PRIVATE_MAP ",
                    "expected_map_artifacts": ["Thm", "Sol", "SnapshotGenerated"],
                    "source_to_generated_private_kernel_names": None,
                    "kernel_name_mapping_validated": False, "core_sha256": base.core_sha,
                    "runtime_sha256": base.runtime_sha, "source_graph_sha256": g.input_hashes["verification/decl_graph.jsonl"],
                    "input_hashes": g.input_hashes,
                    "implementation_sha256": {f: sha(TASK/"scripts"/f) for f in
                       ["generate_platform_nodes_isolated.py", "private_inline_binding.py", "generate_platform_nodes.py",
                        "generate_platform_bundles.py", "platform_statement.py", "span_edits.py"]},
                    "source_edits": [{"start": e.start, "end": e.end, "replacement": e.replacement.decode("utf-8"), "reason": e.reason} for e in edits],
                    "solution_edits": proof_ledger, "statement_edits": statement_ledger,
                    "statement": (stage/theorem_file).relative_to(ROOT).as_posix(), "statement_sha256": outputs[theorem_file],
                    "solution": (stage/solution_file).relative_to(ROOT).as_posix(), "solution_sha256": outputs[solution_file],
                    "snapshot_sha256": {f: outputs[f] for f in ["SnapshotOriginal.lean", "SnapshotGenerated.lean"]},
                    "outputs_sha256": outputs,
                    "inline_type_json_outputs": {"original": original_inline, "generated": generated_inline},
                    "collector_output_is_stdout_only_in_upload_text": True,
                    "provisional": True, "validated": False, "submission_ready": False, "full_tree_ready": False,
                    "pending": ["four exact files compiled within 300 seconds", "parse unique OwnModule helper maps from three logs",
                                "original/generated target and helper kernel types", "proof-only name correspondence and Std3 audits",
                                "isolated publication flow review"]}
        for f,h in g.input_hashes.items():
            if sha(TASK/f) != h:
                raise ValueError("Global input changed during isolation preview; regenerate after extraction hold")
        if sha(base.core_path) != base.core_sha:
            raise ValueError("Snapshot core changed")
        for f,h in ((origin["source"],origin["source_sha256"]),(origin["facts"],origin["facts_sha256"]),
                    (origin["original_source"],origin["original_source_sha256"])):
            if sha(ROOT/f) != h:
                raise ValueError("Source/facts changed")
        (stage/"manifest.json").write_text(json.dumps(manifest,indent=2)+"\n",encoding="utf-8")
        return {"theorem_name": name, "stage": stage.relative_to(TASK).as_posix(), "isolated_helpers": len(records),
                "validated": False, "full_tree_ready": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preview", action="store_true", required=True)
    parser.add_argument("--node", action="append", required=True)
    args = parser.parse_args()
    generator = IsolatedGenerator()
    generated, rejected = [], []
    for selection in args.node:
        matches = [k for k,n in generator.g.artifact_plan["nodes"].items()
                   if selection == k or selection == n["theorem_name_before_platform_renames"]]
        if len(matches) != 1:
            rejected.append({"selection": selection, "reason": "Node is absent or ambiguous"})
            continue
        try:
            generated.append(generator.generate(matches[0]))
        except (ValueError, KeyError) as error:
            rejected.append({"selection": selection, "reason": str(error)})
    DEST.mkdir(parents=True, exist_ok=True)
    report = {"generated": generated, "rejected": rejected, "provisional": True,
              "validated": False, "full_tree_ready": False, "input_hashes": generator.g.input_hashes}
    (DEST/"generation-report.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:v for k,v in report.items() if k != "input_hashes"}))


if __name__ == "__main__":
    main()
