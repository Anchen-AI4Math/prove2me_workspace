"""Plan proved Definitions providers without changing the platform plans.

This is a Python-only design audit.  It reconstructs either the archived
799-module preview or the current complete 875-module preview, proves that it
equals the checked-in base plans, and then writes two isolated variants:

* ``minimum`` promotes the three public helpers required by public statement
  types; and
* ``all-shared-public`` promotes every public inline helper identified by the
  collision audit.

Every promoted root is closed over the existing planner's whole-command direct
dependency graph.  In complete mode every declaration in the kernel graph must
have an AST command owner before any provider is selected.  Non-definition dependencies become ``definition_embedded``
and retain their source proof commands; no theorem placeholder is permitted in
a Definitions bundle.  The variants are deliberately provisional and are not
Lean validation or publication evidence.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import copy
import hashlib
import json
import math
from pathlib import Path
import sys

TASK = Path(__file__).resolve().parents[1]
DEST = TASK / "verification"
OUT = DEST / "provider-plans"
ROOT = TASK.parents[1]

sys.path.insert(0, str(Path(__file__).resolve().parent))
from plan_platform_artifacts import build_artifacts  # noqa: E402
from plan_platform_units import make_plan  # noqa: E402

DEFINITION_CATEGORIES = {"definition", "definition_embedded"}
EXPECTED_EXTRACTED_MODULES = 799
EXPECTED_UNITS = 5335
EXPECTED_NODES = 312
EXPECTED_SHARED_PUBLIC_NAMES = 326
EXPECTED_COLLISION_NODES = 84
EXPECTED_COMPLETE_MODULES = 875
EXPECTED_MINIMUM = {
    "OAI.PiExponent.FormalLogTruncation.logTail_constantCoeff":
        "OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation:12375",
    "OAI.PiExponent.GeneralCartierDegreeLength.finite_zeroIdeal_of_mono":
        "OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength:2792",
    "OAI.PiExponent.primeRectangular_maps_maximal":
        "OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent:419",
}


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bytes_sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def comparable(record):
    return {key: value for key, value in record.items()
            if key not in {"provisional", "ready_for_generation"}}


def percentile(values, fraction):
    if not values:
        return 0
    ordered = sorted(values)
    return ordered[max(0, math.ceil(len(ordered) * fraction) - 1)]


def bundle_module(source_module: str) -> str:
    if (not source_module.isascii()
            or any(not part.isidentifier() for part in source_module.split("."))):
        raise ValueError("Provider source module needs an ASCII identifier: " + source_module)
    return "Definitions.Def_" + source_module.replace(".", "_")


def graph_rows(path: Path):
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]


def transitive_units(roots, units):
    todo = list(roots)
    seen = set()
    while todo:
        key = todo.pop()
        if key in seen:
            continue
        if key not in units:
            raise ValueError("Provider closure references an unknown unit: " + key)
        seen.add(key)
        todo.extend(units[key]["direct_unit_dependencies"])
    return seen


def transitive_graph(roots, graph):
    todo = list(roots)
    seen = set()
    while todo:
        name = todo.pop()
        if name in seen or name not in graph:
            continue
        seen.add(name)
        row = graph[name]
        todo.extend(row["typeDeps"] + row["valueDeps"] + row["constructors"])
    return seen


def collision_nodes(artifacts, units, graph):
    """Find public inline names emitted by at least two imported node files."""
    results = {}
    nodes = artifacts["nodes"]
    for root in sorted(nodes):
        todo = [root]
        closure = set()
        while todo:
            node = todo.pop()
            if node in closure:
                continue
            closure.add(node)
            todo.extend(nodes[node]["node_dependencies"])
        providers = defaultdict(set)
        provider_units = defaultdict(set)
        for node in closure:
            for key in nodes[node]["inline_units"]:
                for graph_name in units[key]["graph_names"]:
                    row = graph[graph_name]
                    if not row["isPrivate"]:
                        providers[row["userName"]].add(node)
                        provider_units[row["userName"]].add(key)
        duplicates = {name: {"provider_nodes": sorted(nodeset),
                             "provider_units": sorted(provider_units[name])}
                      for name, nodeset in providers.items() if len(nodeset) > 1}
        if duplicates:
            results[root] = duplicates
    return results


def shared_public_declarations(collisions, units, graph):
    """Reconstruct provider roots from the current plan, without a stale audit."""
    consumers = defaultdict(set)
    provider_units = defaultdict(set)
    for consumer, duplicates in collisions.items():
        for name, detail in duplicates.items():
            consumers[name].add(consumer)
            provider_units[name].update(detail["provider_units"])
    result = {}
    for name in sorted(provider_units):
        candidates = sorted(provider_units[name])
        # A repeated inline declaration should still be one source command copied
        # into several node files.  Multiple source owners are an ambiguity, not a
        # reason to choose the first one.
        if len(candidates) != 1:
            raise ValueError("Public collision name has non-unique source unit: "
                             + name + " -> " + str(candidates))
        key = candidates[0]
        if key not in units or units[key]["category"] != "inline":
            raise ValueError("Shared public provider is not an inline unit: " + name)
        graph_names = [item for item in units[key]["graph_names"]
                       if item in graph and not graph[item]["isPrivate"]
                       and graph[item]["userName"] == name]
        if not graph_names:
            raise ValueError("Collision name does not belong to its source unit: " + name)
        result[name] = {
            "name": name,
            "declaration": {"unit": key, "graph_names": graph_names},
            "consumers": sorted(consumers[name]),
        }
    return result


def unresolved_graph_owners(unit_keys, units, graph, pending_names):
    """Return graph dependencies that have no AST command owner in the base plan."""
    pending = set(pending_names)
    found = defaultdict(set)
    for key in sorted(unit_keys):
        roots = units[key]["graph_names"]
        for name in transitive_graph(roots, graph) & pending:
            found[name].add(key)
    return [{"source_graph_name": name, "reachable_from_units": sorted(found[name])}
            for name in sorted(found)]


def variant_metrics(plan, artifacts, base_plan, base_artifacts, graph,
                    promoted_roots, closure_keys, original_shared_names):
    units = {unit["id"]: unit for unit in plan["units"]}
    base_units = {unit["id"]: unit for unit in base_plan["units"]}
    categories = Counter(unit["category"] for unit in units.values())
    base_categories = Counter(unit["category"] for unit in base_units.values())
    new_units = sorted(key for key in closure_keys
                       if base_units[key]["category"] not in DEFINITION_CATEGORIES)
    root_units = [units[key] for key in promoted_roots]
    embedded_theorems = [units[key] for key in new_units
                         if not units[key]["definition_command"]]
    private_new = [key for key in new_units if units[key]["private"]]
    absorbed_nodes = sorted(key for key in new_units
                            if base_units[key]["category"] == "node")

    def selected_bytes(current_units):
        grouped = defaultdict(int)
        for unit in current_units.values():
            if unit["category"] in DEFINITION_CATEGORIES:
                grouped[unit["module"]] += unit["end"]["offset"] - unit["start"]["offset"]
        return grouped

    current_bytes = selected_bytes(units)
    base_bytes = selected_bytes(base_units)
    byte_deltas = {module: current_bytes[module] - base_bytes.get(module, 0)
                   for module in current_bytes
                   if current_bytes[module] != base_bytes.get(module, 0)}
    max_module = max(current_bytes, key=current_bytes.get) if current_bytes else None
    max_delta_module = max(byte_deltas, key=byte_deltas.get) if byte_deltas else None

    source_components = [len(node["source_components"])
                         for node in artifacts["nodes"].values()]
    inline_units = [len(node["inline_units"])
                    for node in artifacts["nodes"].values()]
    base_source_components = [len(node["source_components"])
                              for node in base_artifacts["nodes"].values()]
    base_inline_units = [len(node["inline_units"])
                         for node in base_artifacts["nodes"].values()]

    collisions = collision_nodes(artifacts, units, graph)
    shared_units_by_name = {}
    for name in original_shared_names:
        matches = {key for key, unit in units.items()
                   if unit["category"] == "inline"
                   and any(graph[g]["userName"] == name and not graph[g]["isPrivate"]
                           for g in unit["graph_names"])}
        if matches:
            shared_units_by_name[name] = sorted(matches)

    cross_module_private_edges = []
    unresolved_cross_module_private_edges = []
    for key, unit in units.items():
        if unit["category"] not in DEFINITION_CATEGORIES:
            continue
        for dep in unit["direct_unit_dependencies"]:
            target = units[dep]
            if target["private"] and target["module"] != unit["module"]:
                edge = {"from": key, "to": dep, "target_deprivate": target["deprivate"]}
                cross_module_private_edges.append(edge)
                if not target["deprivate"]:
                    unresolved_cross_module_private_edges.append(edge)
    base_cross_module_private_edges = {
        (key, dep) for key, unit in base_units.items()
        if unit["category"] in DEFINITION_CATEGORIES
        for dep in unit["direct_unit_dependencies"]
        if base_units[dep]["private"] and base_units[dep]["module"] != unit["module"]
    }
    new_cross_module_private_edges = [edge for edge in cross_module_private_edges
                                      if (edge["from"], edge["to"]) not in base_cross_module_private_edges]

    proof_lines = [unit["proof_lines"] for unit in embedded_theorems
                   if unit["proof_lines"] is not None]
    return {
        "category_counts": dict(sorted(categories.items())),
        "category_delta": {key: categories[key] - base_categories[key]
                           for key in sorted(set(categories) | set(base_categories))},
        "provider_root_units": len(promoted_roots),
        "provider_root_names": sum(len([name for name in unit["graph_names"]
                                        if not graph[name]["isPrivate"]]) for unit in root_units),
        "provider_root_source_modules": len({unit["module"] for unit in root_units}),
        "provider_root_proof_lines": {
            "sum": sum(unit["proof_lines"] or 0 for unit in root_units),
            "max": max((unit["proof_lines"] or 0 for unit in root_units), default=0),
            "over_10": sum((unit["proof_lines"] or 0) > 10 for unit in root_units),
        },
        "complete_unit_closure": len(closure_keys),
        "complete_closure_source_modules": len({units[key]["module"] for key in closure_keys}),
        "newly_promoted_units": len(new_units),
        "newly_promoted_source_modules": len({units[key]["module"] for key in new_units}),
        "newly_promoted_definition_commands": sum(units[key]["definition_command"] for key in new_units),
        "newly_embedded_theorem_commands": len(embedded_theorems),
        "newly_promoted_private_commands": len(private_new),
        "newly_promoted_private_units": private_new,
        "absorbed_existing_nodes": len(absorbed_nodes),
        "absorbed_existing_node_units": absorbed_nodes,
        "nodes_remaining": len(artifacts["nodes"]),
        "node_delta": len(artifacts["nodes"]) - len(base_artifacts["nodes"]),
        "definition_bundles": len(artifacts["definition_bundles"]),
        "definition_bundle_delta": len(artifacts["definition_bundles"]) - len(base_artifacts["definition_bundles"]),
        "embedded_theorem_proof_lines": {
            "sum": sum(proof_lines),
            "max": max(proof_lines, default=0),
            "over_10": sum(value > 10 for value in proof_lines),
            "over_40": sum(value > 40 for value in proof_lines),
        },
        "definition_selected_source_bytes": {
            "total": sum(current_bytes.values()),
            "delta": sum(current_bytes.values()) - sum(base_bytes.values()),
            "max_bundle": {"source_module": max_module,
                           "bytes": current_bytes.get(max_module, 0)},
            "max_delta_bundle": {"source_module": max_delta_module,
                                 "bytes": byte_deltas.get(max_delta_module, 0)},
            "bundles_over_25000": sum(value > 25_000 for value in current_bytes.values()),
            "bundles_over_50000": sum(value > 50_000 for value in current_bytes.values()),
            "bundles_over_100000": sum(value > 100_000 for value in current_bytes.values()),
        },
        "node_source_components": {
            "max": max(source_components, default=0),
            "p95": percentile(source_components, .95),
            "base_max": max(base_source_components, default=0),
            "base_p95": percentile(base_source_components, .95),
        },
        "node_inline_units": {
            "max": max(inline_units, default=0),
            "p95": percentile(inline_units, .95),
            "base_max": max(base_inline_units, default=0),
            "base_p95": percentile(base_inline_units, .95),
        },
        "public_inline_collision_nodes": len(collisions),
        "public_inline_collision_node_ids": sorted(collisions),
        "original_shared_public_names_still_inline": len(shared_units_by_name),
        "original_shared_public_names_still_inline_detail": shared_units_by_name,
        "cross_module_private_definition_edges": cross_module_private_edges,
        "new_cross_module_private_definition_edges": new_cross_module_private_edges,
        "unresolved_cross_module_private_definition_edges": unresolved_cross_module_private_edges,
    }


def source_manifest(unit, graph, source_consumers, source_evidence):
    relative = Path(*unit["module"].split(".")).with_suffix(".lean")
    port_path = TASK / "port" / "lean" / relative
    original_path = TASK / "source" / "lean" / relative
    data = port_path.read_bytes()
    if sha256(port_path) != unit["source_sha256"]:
        raise ValueError("Port source hash differs from the AST inventory: " + unit["module"])
    start, end = unit["start"]["offset"], unit["end"]["offset"]
    command = data[start:end]
    names = []
    for name in unit["graph_names"]:
        row = graph[name]
        names.append({
            "name": name,
            "user_name": row["userName"],
            "kind": row["kind"],
            "is_private": row["isPrivate"],
            "is_instance": row["isInstance"],
            "type_deps": row["typeDeps"],
            "value_deps": row["valueDeps"],
            "constructors": row["constructors"],
        })
    result = {
        "unit": unit["id"],
        "source_module": unit["module"],
        "provider_module": bundle_module(unit["module"]),
        "source_paths": {
            "port": str(port_path.relative_to(ROOT)).replace("\\", "/"),
            "original": str(original_path.relative_to(ROOT)).replace("\\", "/"),
        },
        "source_hashes": {
            "port_sha256": sha256(port_path),
            "original_sha256": sha256(original_path) if original_path.exists() else None,
        },
        "command": {
            "range": {"start": unit["start"], "end": unit["end"]},
            "name_range": unit["nameRange"],
            "value_start": unit["valueStart"],
            "byte_length": len(command),
            "sha256": bytes_sha(command),
            "utf8": command.decode("utf-8"),
        },
        "interface": names,
        "consumers_in_collision_audit": sorted(source_consumers),
        "statement_type_evidence": source_evidence,
        "proof_policy": "retain the exact whole source command and its proof; theorem placeholders are forbidden",
        "lean_validated": False,
        "publish_ready": False,
    }
    return result


def promote(base_plan, root_keys, label):
    variant = copy.deepcopy(base_plan)
    units = {unit["id"]: unit for unit in variant["units"]}
    closure = transitive_units(root_keys, units)
    targets = {key for key, unit in units.items()
               if any(name in variant["source_targets"] for name in unit["graph_names"])}
    if targets & closure:
        raise ValueError(label + " provider closure absorbs a source target: " + str(sorted(targets & closure)))
    for key in sorted(closure):
        unit = units[key]
        if unit["category"] in DEFINITION_CATEGORIES:
            continue
        unit["category"] = "definition" if unit["definition_command"] else "definition_embedded"
        reason = "proved_provider_root:" + label if key in root_keys else "proved_provider_dependency:" + label
        unit["promotion_reasons"] = list(unit["promotion_reasons"]) + [reason]
    counts = Counter(unit["category"] for unit in units.values())
    variant["counts"] = dict(sorted(counts.items()))
    variant["provisional"] = True
    variant["ready_for_generation"] = False
    variant["provider_variant"] = {
        "label": label,
        "root_units": sorted(root_keys),
        "closure_units": sorted(closure),
        "proof_policy": "complete whole-command type/value/constructor closure retained in Definitions",
        "lean_validated": False,
        "accepted_plan_unchanged": True,
    }
    for key in closure:
        escaped = [dep for dep in units[key]["direct_unit_dependencies"]
                   if units[dep]["category"] not in DEFINITION_CATEGORIES]
        if escaped:
            raise ValueError(label + " Definitions dependency escapes: " + key + " -> " + str(escaped))
    return variant, closure


def write_json(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--frozen-preview", action="store_true",
                      help="reconstruct the archived 799-module preview (historical compatibility only)")
    mode.add_argument("--verified-complete", action="store_true",
                      help="require the complete 875-module AST inventories and zero unowned graph declarations")
    parser.add_argument("--variant", choices=("minimum", "all-shared-public", "both"), default="both")
    args = parser.parse_args()

    paths = {
        "unit_plan": DEST / "platform-unit-plan-preview.json",
        "artifact_plan": DEST / "platform-artifact-plan-preview.json",
        "unit_inventory": DEST / "ast-unit-inventory.json",
        "scope_inventory": DEST / "ast-scope-inventory.json",
        "graph": DEST / "decl_graph.jsonl",
        "collision_audit": DEST / "inline-provider-collision-audit.json",
        "reuse_candidates": TASK / "platform" / "definition-reuse-candidates.json",
        "source_integrity": DEST / "source-integrity.json",
        "validated_port_manifest": DEST / "validated-port-manifest.json",
    }
    input_hashes = {str(path.relative_to(TASK)).replace("\\", "/"): sha256(path)
                    for path in paths.values()}
    frozen_plan = read_json(paths["unit_plan"])
    frozen_artifacts = read_json(paths["artifact_plan"])
    inventory = read_json(paths["unit_inventory"])
    scopes = read_json(paths["scope_inventory"])
    rows = graph_rows(paths["graph"])
    graph = {row["name"]: row for row in rows}
    audit = read_json(paths["collision_audit"])
    reuse = read_json(paths["reuse_candidates"])["reuse_candidates"]
    source_commit = read_json(paths["source_integrity"])["commit"]
    if read_json(paths["validated_port_manifest"])["source_commit"] != source_commit:
        raise ValueError("Source integrity and validated port manifests disagree on the source commit")

    if args.frozen_preview:
        if (inventory["extracted_modules"] != EXPECTED_EXTRACTED_MODULES
                or len(frozen_plan["units"]) != EXPECTED_UNITS
                or len(frozen_artifacts["nodes"]) != EXPECTED_NODES
                or len(audit["shared_public_declarations"]) != EXPECTED_SHARED_PUBLIC_NAMES
                or len(audit["collision_nodes"]) != EXPECTED_COLLISION_NODES):
            raise ValueError("The input is not the fixed 799-module/5335-unit/312-node preview")
    else:
        complete_fields = {
            "unit_inventory": (inventory.get("complete_extraction"), inventory.get("extracted_modules")),
            "scope_inventory": (scopes.get("complete_extraction"), scopes.get("extracted_modules")),
            "unit_plan": (frozen_plan.get("complete_extraction"), None),
            "artifact_plan": (frozen_artifacts.get("complete_extraction"), None),
        }
        bad = {key: value for key, value in complete_fields.items()
               if value[0] is not True or (value[1] is not None and value[1] != EXPECTED_COMPLETE_MODULES)}
        if bad:
            raise ValueError("Complete provider planning requires the 875-module inventories: " + str(bad))
        if inventory.get("unmatched"):
            raise ValueError("Complete provider planning has unmatched AST declarations")
        pending = frozen_plan.get("source_declarations_pending_ast")
        if pending is None:
            raise ValueError("Complete base plan does not expose source_declarations_pending_ast")
        if pending:
            raise ValueError("Complete provider planning has unowned source graph declarations: "
                             + str(pending[:20]))
    reconstructed = make_plan(inventory, rows)
    if comparable(reconstructed) != comparable(frozen_plan):
        raise ValueError("Frozen unit plan does not equal a fresh reconstruction")
    reconstructed_artifacts = build_artifacts(frozen_plan, scopes, reuse)
    if comparable(reconstructed_artifacts) != comparable(frozen_artifacts):
        raise ValueError("Frozen artifact plan does not equal a fresh reconstruction")
    base_units = {unit["id"]: unit for unit in frozen_plan["units"]}
    base_collisions = collision_nodes(frozen_artifacts, base_units, graph)
    if args.frozen_preview:
        if set(base_collisions) != {item["consumer"]["node"] for item in audit["collision_nodes"]}:
            raise ValueError("Independent collision recomputation does not reproduce the 84-node audit")
        shared_by_name = {item["name"]: item for item in audit["shared_public_declarations"]}
    else:
        shared_by_name = shared_public_declarations(base_collisions, base_units, graph)
    all_roots = set()
    for name, item in shared_by_name.items():
        key = item["declaration"]["unit"]
        if key not in base_units or base_units[key]["category"] != "inline":
            raise ValueError("Shared public provider is not an inline unit: " + name)
        if not any(graph[g]["userName"] == name and not graph[g]["isPrivate"]
                   for g in base_units[key]["graph_names"]):
            raise ValueError("Shared public name does not belong to its audited unit: " + name)
        all_roots.add(key)

    statement_evidence = defaultdict(list)
    audited_minimum = {}
    for record in audit["statement_required_shared_helpers"]:
        consumer = record["consumer"]["node"]
        for helper in record["helpers"]:
            key = helper["declaration"]["unit"]
            names = [name for name in helper["declaration"]["graph_names"]
                     if name in EXPECTED_MINIMUM]
            if len(names) != 1:
                raise ValueError("Statement helper does not identify one expected public name")
            name = names[0]
            audited_minimum[name] = key
            statement_evidence[name].append({
                "consumer_unit": consumer,
                "consumer_theorem": record["consumer"]["theorem_name"],
                "consumer_type_deps_contains_helper": name in record["consumer_graph_row"]["typeDeps"],
                "consumer_value_deps_contains_helper": name in record["consumer_graph_row"]["valueDeps"],
                "facts": record["type_reference_evidence"]["facts"],
                "facts_sha256": record["type_reference_evidence"]["facts_sha256"],
                "reference_count": len(record["type_reference_evidence"]["refs"]),
            })
            facts_relative = record["type_reference_evidence"]["facts"]
            facts_path = ROOT / facts_relative
            facts_sha = record["type_reference_evidence"]["facts_sha256"]
            if sha256(facts_path) != facts_sha:
                raise ValueError("Statement type-reference facts changed: " + facts_relative)
            input_hashes[facts_relative] = facts_sha
    if audited_minimum != EXPECTED_MINIMUM:
        raise ValueError("The audited statement helper set differs from the expected three helpers")
    if any(not evidence["consumer_type_deps_contains_helper"]
           for records in statement_evidence.values() for evidence in records):
        raise ValueError("A required helper is absent from an audited consumer statement type")

    requested = []
    if args.variant in {"minimum", "both"}:
        requested.append(("minimum", set(EXPECTED_MINIMUM.values())))
    if args.variant in {"all-shared-public", "both"}:
        requested.append(("all-shared-public", all_roots))

    summaries = {}
    original_shared_names = set(shared_by_name)
    for label, roots in requested:
        variant, closure_keys = promote(frozen_plan, roots, label)
        owner_gaps = unresolved_graph_owners(
            closure_keys, {unit["id"]: unit for unit in variant["units"]}, graph,
            frozen_plan.get("source_declarations_pending_ast", []))
        if owner_gaps:
            raise ValueError(label + " provider closure reaches declarations without AST owners: "
                             + str(owner_gaps[:20]))
        artifacts = build_artifacts(variant, scopes, reuse)
        artifacts["provisional"] = True
        artifacts["ready_for_generation"] = False
        artifacts["provider_variant"] = variant["provider_variant"]
        units = {unit["id"]: unit for unit in variant["units"]}
        metrics = variant_metrics(variant, artifacts, frozen_plan, frozen_artifacts,
                                  graph, roots, closure_keys, original_shared_names)
        if metrics["unresolved_cross_module_private_definition_edges"]:
            raise ValueError(label + " creates an undeprivatized cross-module private Definitions dependency")
        variant_dir = OUT / label
        write_json(variant_dir / "platform-unit-plan-provider-variant.json", variant)
        write_json(variant_dir / "platform-artifact-plan-provider-variant.json", artifacts)

        root_rows = []
        for key in sorted(roots):
            unit = units[key]
            root_names = [name for name in unit["graph_names"]
                          if name in graph and not graph[name]["isPrivate"]]
            name = next((name for name in root_names if name in shared_by_name), root_names[0])
            declaration = shared_by_name[name]
            type_closure = transitive_graph(graph[name]["typeDeps"], graph)
            private_type_deps = sorted(dep for dep in type_closure if graph[dep]["isPrivate"])
            closure = transitive_units({key}, units)
            provider = source_manifest(unit, graph, declaration["consumers"],
                                       statement_evidence.get(name, []))
            provider.update({
                "provider_name": name,
                "provider_names": sorted(shared_name for shared_name in original_shared_names
                                         if shared_by_name[shared_name]["declaration"]["unit"] == key),
                "requested_alias": ("OAI.PiExponent.FormalLogJet.logTail_constantCoeff"
                                    if name == "OAI.PiExponent.FormalLogTruncation.logTail_constantCoeff"
                                    else None),
                "complete_unit_closure": sorted(closure),
                "complete_unit_closure_count": len(closure),
                "closure_source_modules": sorted({units[item]["module"] for item in closure}),
                "closure_selected_source_bytes": sum(units[item]["end"]["offset"]
                                                     - units[item]["start"]["offset"] for item in closure),
                "private_constants_in_transitive_statement_type": private_type_deps,
                "provider_bundle_imports": artifacts["definition_bundles"][unit["module"]]["imports"],
            })
            root_rows.append(provider)
        closure_index = []
        for key in sorted(closure_keys):
            unit = units[key]
            relative = Path(*unit["module"].split(".")).with_suffix(".lean")
            source_path = TASK / "port" / "lean" / relative
            data = source_path.read_bytes()
            if bytes_sha(data) != unit["source_sha256"]:
                raise ValueError("Closure source changed after AST inventory: " + unit["module"])
            command = data[unit["start"]["offset"]:unit["end"]["offset"]]
            closure_index.append({
                "unit": key,
                "source_module": unit["module"],
                "source_path": str(source_path.relative_to(ROOT)).replace("\\", "/"),
                "source_sha256": unit["source_sha256"],
                "command_range": {"start": unit["start"], "end": unit["end"]},
                "command_bytes": len(command),
                "command_sha256": bytes_sha(command),
                "graph_names": unit["graph_names"],
                "graph_kinds": unit["graph_kinds"],
                "category_before": base_units[key]["category"],
                "category_after": unit["category"],
                "private": unit["private"],
                "deprivate": unit["deprivate"],
                "direct_unit_dependencies": unit["direct_unit_dependencies"],
            })
        closure_index_path = variant_dir / "closure-command-index.jsonl"
        closure_index_path.write_text(
            "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in closure_index), encoding="utf-8")
        providers_path = variant_dir / "provider-roots.jsonl"
        providers_path.write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in root_rows),
                                  encoding="utf-8")
        if label == "minimum":
            for row in root_rows:
                safe = row["provider_name"].replace(".", "_")
                write_json(variant_dir / "providers" / (safe + ".json"), row)

        manifest = {
            "schema_version": 1,
            "variant": label,
            "basis": ("frozen 799-module historical preview only" if args.frozen_preview
                      else "verified complete 875-module preview"),
            "source_commit": source_commit,
            "input_hashes": input_hashes,
            "fixed_plan_checks": {
                "fresh_unit_plan_equals_frozen": True,
                "fresh_artifact_plan_equals_frozen": True,
                "independent_collision_recomputation_matches_base": True,
                "historical_84_node_audit_exact_match": bool(args.frozen_preview),
                "units": len(frozen_plan["units"]),
                "nodes": len(frozen_artifacts["nodes"]),
            },
            "invariants": {
                "whole_command_atomicity": True,
                "complete_direct_dependency_closure": True,
                "definitions_dependencies_closed": True,
                "definition_dag_acyclic": True,
                "node_dag_acyclic": True,
                "source_target_not_absorbed": True,
                "base_source_declarations_pending_ast": len(
                    frozen_plan.get("source_declarations_pending_ast", [])),
                "provider_closure_unowned_graph_dependencies": 0,
                "unresolved_cross_module_private_definition_edges": 0,
                "theorem_proofs_retained": True,
                "theorem_placeholders_in_definitions_allowed": False,
            },
            "metrics": metrics,
            "root_provider_rows": "provider-roots.jsonl",
            "closure_command_index": "closure-command-index.jsonl",
            "unit_plan": "platform-unit-plan-provider-variant.json",
            "artifact_plan": "platform-artifact-plan-provider-variant.json",
            "accepted_plan_unchanged": True,
            "preview_only": True,
            "lean_validated": False,
            "publish_ready": False,
            "final_plan_compatible": False,
            "limitations": [
                ("This historical variant uses the archived 799-module preview."
                 if args.frozen_preview else
                 "This variant uses all 875 extracted modules but remains a preview until Lean validation and final-plan review."),
                "Selected source bytes measure retained declaration commands, not Lean elaboration time.",
                "No generated bundle was compiled; the 300-second file budget remains unverified.",
                "Private proof dependencies remain source-module-local; final generated/source type mapping still requires Lean validation.",
            ],
            "pending_name_remaps": {
                "provider_root_names": [],
                "reason": "All provider roots retain their exact public source names; the two-name reassoc command is kept atomically.",
                "inherited_deprivate_units": sum(unit["deprivate"] for unit in units.values()),
                "new_cross_module_private_dependencies": len(metrics["new_cross_module_private_definition_edges"]),
            },
        }
        write_json(variant_dir / "provider-plan-manifest.json", manifest)
        summaries[label] = manifest

    comparison = {
        "schema_version": 1,
        "input_hashes": input_hashes,
        "base_preview": {
            "mode": "frozen-799" if args.frozen_preview else "verified-complete-875",
            "extracted_modules": inventory["extracted_modules"],
            "units": len(frozen_plan["units"]),
            "nodes": len(frozen_artifacts["nodes"]),
            "shared_public_names": len(shared_by_name),
            "collision_nodes": len(base_collisions),
        },
        "variants": {label: manifest["metrics"] for label, manifest in summaries.items()},
        "decision_rule": {
            "minimum": "Required correctness repair for the three helpers present in four public statement types.",
            "all-shared-public": "Use only if closure and bundle sizes are small enough for per-file Lean preflight; Python metrics cannot establish the 300-second budget.",
        },
        "accepted_plan_unchanged": True,
        "lean_run": False,
        "network_used": False,
    }
    write_json(OUT / "provider-promotion-comparison.json", comparison)
    print(json.dumps({
        "fixed_plan_reconstructed": True,
        "variants": {label: {
            "root_units": manifest["metrics"]["provider_root_units"],
            "root_names": manifest["metrics"]["provider_root_names"],
            "closure_units": manifest["metrics"]["complete_unit_closure"],
            "new_units": manifest["metrics"]["newly_promoted_units"],
            "absorbed_nodes": manifest["metrics"]["absorbed_existing_nodes"],
            "collision_nodes": manifest["metrics"]["public_inline_collision_nodes"],
            "selected_source_byte_delta": manifest["metrics"]["definition_selected_source_bytes"]["delta"],
        } for label, manifest in summaries.items()},
        "output": str(OUT),
        "lean_run": False,
    }, ensure_ascii=False))


if __name__ == "__main__":
    main()
