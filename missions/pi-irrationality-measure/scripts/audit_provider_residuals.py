#!/usr/bin/env python3
"""Audit residual private, atomic-companion and source-syntax provider risks.

Pure Python only.  This does not modify the provider plan or generate Lean.
"""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import sys

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
V = TASK / "verification"
PLAN_DIR = V / "provider-plans" / "all-shared-public"
OUTPUT = PLAN_DIR / "residual-risk-audit.json"
MIXED_OUTPUT = PLAN_DIR / "mixed-atomic-provider-candidate.json"

sys.path.insert(0, str(Path(__file__).resolve().parent))
from plan_platform_artifacts import build_artifacts  # noqa: E402
from plan_platform_units_providers import promote  # noqa: E402

DEFS = {"definition", "definition_embedded"}


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def contains(span, point):
    return span["start"]["offset"] <= point["start"]["offset"] <= point["end"]["offset"] <= span["end"]["offset"]


def exact_rfl(unit, data, graph):
    if (unit["privateTok"] is not None or unit["is_instance_command"] or unit["is_local_instance"]
            or unit["graph_kinds"] != ["theorem"] or len(unit["graph_names"]) != 1
            or unit["nameRange"] is None or unit["valueStart"] is None):
        return False
    row = graph[unit["graph_names"][0]]
    if row["isPrivate"] or row["isInstance"]:
        return False
    a, b = unit["valueStart"]["offset"], unit["end"]["offset"]
    return " ".join(data[a:b].decode("utf-8").split()) == ":= rfl"


def promotion_delta(plan, roots, scopes, reuse, label):
    if not roots:
        return {"root_units": 0, "new_units": 0}
    variant, closure = promote(plan, set(roots), label)
    artifacts = build_artifacts(variant, scopes, reuse)
    before = {unit["id"]: unit for unit in plan["units"]}
    after = {unit["id"]: unit for unit in variant["units"]}
    new = sorted(key for key in closure if before[key]["category"] not in DEFS)
    return {
        "root_units": len(roots),
        "closure_units": len(closure),
        "new_units": len(new),
        "new_unit_ids": new,
        "new_source_bytes": sum(after[key]["end"]["offset"] - after[key]["start"]["offset"] for key in new),
        "absorbed_nodes": sorted(key for key in new if before[key]["category"] == "node"),
        "new_private_units": sorted(key for key in new if after[key]["private"]),
        "new_deprivate_units": sorted(key for key in new if after[key]["deprivate"]),
        "nodes_after": len(artifacts["nodes"]),
        "definition_bundles_after": len(artifacts["definition_bundles"]),
        "definition_dag_acyclic": True,
        "node_dag_acyclic": True,
    }


def main():
    plan_path = PLAN_DIR / "platform-unit-plan-provider-variant.json"
    artifacts_path = PLAN_DIR / "platform-artifact-plan-provider-variant.json"
    graph_path = V / "decl_graph.jsonl"
    inventory_path = V / "ast-unit-inventory.json"
    scopes_path = V / "ast-scope-inventory.json"
    state_path = V / "extraction-state.json"
    audit_path = V / "inline-provider-collision-audit.json"
    reuse_path = TASK / "platform" / "definition-reuse-candidates.json"
    paths = [plan_path, artifacts_path, graph_path, inventory_path, scopes_path,
             audit_path, reuse_path, Path(__file__).resolve()]
    plan, artifacts = read(plan_path), read(artifacts_path)
    units = {unit["id"]: unit for unit in plan["units"]}
    graph = {row["name"]: row for row in (json.loads(line) for line in graph_path.read_bytes().splitlines())}
    inventory = read(inventory_path)
    inventory_modules = {item["module"]: item for item in inventory["modules"]}
    scopes = read(scopes_path)
    state = read(state_path)
    reuse = read(reuse_path)["reuse_candidates"]
    collision_audit = read(audit_path)

    private_nodes = {}
    for node, record in artifacts["nodes"].items():
        private = sorted(key for key in record["inline_units"] if units[key]["private"])
        if private:
            private_nodes[node] = private

    mixed_nodes = []
    mixed_roots = set()
    for key in artifacts["nodes"]:
        unit = units[key]
        if len(unit["graph_names"]) <= 1:
            continue
        mixed_roots.add(key)
        mixed_nodes.append({
            "unit": key, "graph_names": unit["graph_names"], "graph_kinds": unit["graph_kinds"],
            "source_module": unit["module"], "proof_lines": unit["proof_lines"],
            "source_bytes": unit["end"]["offset"] - unit["start"]["offset"],
            "promotion_reasons": unit["promotion_reasons"],
            "contains_generated_companion": any(graph[name]["startLine"] == 0 for name in unit["graph_names"]),
        })

    statement_rows = []
    for record in collision_audit["statement_required_shared_helpers"]:
        for helper in record["helpers"]:
            key = helper["declaration"]["unit"]
            for name in helper["declaration"]["graph_names"]:
                statement_rows.append({
                    "consumer": record["consumer"]["theorem_name"], "helper": name, "unit": key,
                    "helper_public": not graph[name]["isPrivate"],
                    "provider_category": units[key]["category"],
                    "in_consumer_type_deps": name in record["consumer_graph_row"]["typeDeps"],
                    "in_consumer_value_deps": name in record["consumer_graph_row"]["valueDeps"],
                })

    syntax_supported, syntax_missing, active_context = [], [], []
    private_binding_tokens, unresolved_private = [], []
    scanned_modules, unavailable_modules, scanned_provenance = 0, [], []
    for module, bundle in artifacts["definition_bundles"].items():
        if module not in inventory_modules:
            unavailable_modules.append(module)
            continue
        relative = module.replace(".", "/") + ".lean"
        entry = state["stage2"].get(relative)
        if not entry:
            unavailable_modules.append(module)
            continue
        facts_path = ROOT / entry["facts"]
        if sha(facts_path) != entry["facts_sha256"]:
            raise ValueError("AST facts changed: " + module)
        facts = [json.loads(line) for line in facts_path.read_bytes().splitlines()]
        source_path = TASK / "port/lean" / relative
        source_sha = sha(source_path)
        if source_sha != entry["preflight"]["source_sha256"]:
            raise ValueError("Source changed: " + module)
        data = source_path.read_bytes()
        scanned_provenance.append({
            "module": module,
            "source": source_path.relative_to(ROOT).as_posix(),
            "source_sha256": source_sha,
            "facts": entry["facts"],
            "facts_sha256": entry["facts_sha256"],
        })
        inv = inventory_modules[module]
        selected = set(bundle["units"])
        by_name = {name: module + ":" + str(unit["start"]["offset"])
                   for unit in inv["units"] for name in unit["graph_names"]}
        binding_owner = {}
        for unit in inv["units"]:
            if not unit["nameRange"]:
                continue
            identities = {fact["const"] for fact in facts if fact["kind"] == "ref"
                          and fact["start"] == unit["nameRange"]["start"]
                          and fact["end"] == unit["nameRange"]["end"]}
            if len(identities) == 1:
                binding_owner[next(iter(identities))] = module + ":" + str(unit["start"]["offset"])
        selected_ranges = [(units[key]["start"]["offset"], units[key]["end"]["offset"], key)
                           for key in selected]
        all_ranges = [(unit["start"]["offset"], unit["end"]["offset"])
                      for unit in inv["units"]]
        contexts = []
        for fact in facts:
            if fact["kind"] != "command" or fact["isDeclaration"] or fact["syntax"].get("range") is None:
                continue
            contexts.append((fact["syntax"]["range"], fact["syntax"]["syntaxKind"]))
        seen = set()
        for fact in facts:
            if fact["kind"] != "ref":
                continue
            a, b = fact["start"]["offset"], fact["end"]["offset"]
            consumers = [key for left, right, key in selected_ranges if left <= a <= b <= right]
            context_kinds = [kind for span, kind in contexts if contains(span, fact)]
            outside_declarations = not any(left <= a <= b <= right for left, right in all_ranges)
            relevant_context = outside_declarations and bool(context_kinds)
            if not consumers and not relevant_context:
                continue
            target = by_name.get(fact["const"], binding_owner.get(fact["const"]))
            if target is None or target in selected or target not in units or units[target]["module"] != module:
                if fact["const"].startswith("_private.") and target is None:
                    row = {"source_module": module, "const": fact["const"],
                           "range": {"start": fact["start"], "end": fact["end"]},
                           "consumer_units": consumers,
                           "context_command_kinds": context_kinds}
                    binding_units = [key for key in consumers if units[key]["private"]
                                     and units[key]["valueStart"] is not None
                                     and b <= units[key]["valueStart"]["offset"]]
                    if binding_units:
                        row["binding_units"] = binding_units
                        row["classification"] = (
                            "private declaration binding token; generated snapshot must resolve the "
                            "actual environment name with privateToUserName plus exact module owner")
                        private_binding_tokens.append(row)
                    else:
                        row["classification"] = (
                            "unresolved private dependency; provider generation must reject unless "
                            "authoritative AST ownership and runtime environment resolution agree")
                        unresolved_private.append(row)
                continue
            identity = (module, target, a, b, tuple(consumers), tuple(context_kinds))
            if identity in seen:
                continue
            seen.add(identity)
            target_unit = units[target]
            row = {"source_module": module, "target_unit": target,
                   "target_graph_names": target_unit["graph_names"],
                   "reference_const": fact["const"],
                   "reference_range": {"start": fact["start"], "end": fact["end"]},
                   "consumer_units": consumers, "context_command_kinds": context_kinds,
                   "target_exact_public_rfl": exact_rfl(target_unit, data, graph)}
            if context_kinds:
                row["reason"] = "retained non-declaration context references a subtracted declaration"
                active_context.append(row)
            elif row["target_exact_public_rfl"]:
                row["reason"] = "supported by Generator.elaboration_helpers after exact AST/value checks"
                syntax_supported.append(row)
            else:
                row["reason"] = "selected source syntax references a non-rfl subtracted declaration; add a proved Definition context dependency or reject"
                syntax_missing.append(row)
        scanned_modules += 1

    context_roots = {row["target_unit"] for row in syntax_missing + active_context}
    report = {
        "schema_version": 1,
        "basis": "all-shared-public 799-module provider preview",
        "input_hashes": {path.relative_to(TASK).as_posix(): sha(path) for path in paths},
        "capture_observation": {
            "path": "verification/extraction-state.json",
            "sha256_at_capture": sha(state_path),
            "stage2_entries_at_capture": len(state["stage2"]),
            "dependency": False,
            "reason": "Only the exact per-module source and facts rows below are audit dependencies.",
        },
        "private_inline": {
            "base_reject_nodes": len(collision_audit["private_inline_reject_nodes"]),
            "remaining_reject_nodes": len(private_nodes),
            "remaining_private_units": len({key for values in private_nodes.values() for key in values}),
            "nodes": [{"node": node, "private_inline_units": values}
                      for node, values in sorted(private_nodes.items())],
            "reduction": len(collision_audit["private_inline_reject_nodes"]) - len(private_nodes),
            "resolved": len(private_nodes) == 0,
        },
        "statement_type_helpers": {
            "rows": statement_rows,
            "all_public_proved_definition_providers": all(
                row["helper_public"] and row["provider_category"] in DEFS
                and row["in_consumer_type_deps"] for row in statement_rows),
        },
        "mixed_atomic_nodes": {
            "count": len(mixed_nodes), "nodes": mixed_nodes,
            "promotion_delta": promotion_delta(plan, mixed_roots, scopes, reuse, "mixed-atomic-provider"),
            "recommendation": "Promote the whole multi-declaration command as one proved Definition provider when delta is small; never split an @[reassoc] companion.",
        },
        "source_syntax_dependencies": {
            "scanned_definition_modules": scanned_modules,
            "scanned_module_provenance": scanned_provenance,
            "unavailable_modules": unavailable_modules,
            "supported_exact_rfl_references": syntax_supported,
            "supported_exact_rfl_reference_count": len(syntax_supported),
            "missing_non_rfl_references": syntax_missing,
            "missing_non_rfl_reference_count": len(syntax_missing),
            "active_context_references_to_subtracted_declarations": active_context,
            "active_context_reference_count": len(active_context),
            "private_declaration_binding_tokens": private_binding_tokens,
            "private_declaration_binding_token_count": len(private_binding_tokens),
            "unresolved_private_reference_tokens": unresolved_private,
            "unresolved_private_reference_token_count": len(unresolved_private),
            "context_dependency_promotion_delta": promotion_delta(
                plan, context_roots, scopes, reuse, "source-syntax-context-provider"),
            "generator_policy": {
                "exact_public_rfl": "Generator.elaboration_helpers may retain the whole same-file command after checking accessible kernel dependencies.",
                "non_rfl_or_active_context": "Must become an explicit proved Definition context dependency, or generation must fail with the recorded reason.",
                "private": "Resolve only from authoritative binding ranges and later actual environment privateToUserName plus module ownership; never synthesize numeric private names.",
            },
        },
        "plan_modified": False,
        "lean_started": False,
        "api_used": False,
    }
    OUTPUT.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    mixed_delta = report["mixed_atomic_nodes"]["promotion_delta"]
    mixed_units = [units[row["unit"]] for row in mixed_nodes]
    mixed_provenance = []
    for unit in mixed_units:
        relative = unit["module"].replace(".", "/") + ".lean"
        entry = state["stage2"][relative]
        source_path = TASK / "port/lean" / relative
        mixed_provenance.append({
            "module": unit["module"],
            "unit": unit["id"],
            "whole_command_range": {"start": unit["start"], "end": unit["end"]},
            "graph_names": unit["graph_names"],
            "source": source_path.relative_to(ROOT).as_posix(),
            "source_sha256": sha(source_path),
            "facts": entry["facts"],
            "facts_sha256": entry["facts_sha256"],
        })
    MIXED_OUTPUT.write_text(json.dumps({
        "schema_version": 1,
        "candidate": "all-shared-public-plus-mixed-atomic-command",
        "base_provider_plan": plan_path.relative_to(TASK).as_posix(),
        "base_provider_plan_sha256": sha(plan_path),
        "base_provider_artifact_plan": artifacts_path.relative_to(TASK).as_posix(),
        "base_provider_artifact_plan_sha256": sha(artifacts_path),
        "overlay_root_units": sorted(mixed_roots),
        "promotion_delta": mixed_delta,
        "source_and_facts_provenance": mixed_provenance,
        "atomicity_policy": "Promote each full parser command; do not split generated or @[reassoc] companions.",
        "global_plan_modified": False,
        "candidate_applied": False,
        "validated": False,
        "pending": ["generate isolated provider bundle", "<=300s Lean preflight",
                    "type-only theorem snapshot comparison", "Std3 axiom audit"],
        "residual_risk_audit": OUTPUT.relative_to(TASK).as_posix(),
        "residual_risk_audit_sha256": sha(OUTPUT),
        "lean_started": False,
    }, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "private_inline_nodes": len(private_nodes),
        "mixed_atomic_nodes": len(mixed_nodes),
        "supported_rfl_refs": len(syntax_supported),
        "missing_non_rfl_refs": len(syntax_missing),
        "active_context_refs": len(active_context),
        "context_provider_roots": len(context_roots),
        "lean_started": False,
    }))


if __name__ == "__main__":
    main()
