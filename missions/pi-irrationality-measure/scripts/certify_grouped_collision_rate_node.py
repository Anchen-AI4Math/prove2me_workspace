"""Pure strict replay of the grouped AP11 collision-rate proof evidence.

Requires four frozen primary preflights plus the additive source-helper CI
preflight. It never starts Lean, contacts a service, or reads credentials.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import hashlib
from itertools import permutations
import json
from pathlib import Path

import certify_full_row_minor_node as ap8c
import stage_collision_rate_source_helper_probe as supplement
import stage_grouped_collision_rate_node as stage
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone
from validate_formal_log_node import checked_expr

TASK, V, STAGE = stage.TASK, stage.V, stage.STAGE
SELF = Path(__file__).resolve()
CERT = STAGE / "node-validation.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def rel(path):
    return Path(path).resolve().relative_to(TASK.resolve()).as_posix()


def written_json(path, pf):
    data = pf["data"]
    finished = datetime.fromisoformat(data["at_utc"]).timestamp()
    need(path.is_file() and finished - data["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "Compiler JSON is outside its actual write window: " + rel(path))
    return read(path)


def level_mapping(row):
    params = row["levelParams"]
    need(isinstance(params, list) and all(isinstance(x, str) for x in params)
         and len(params) == len(set(params)), "Malformed actual CI universe parameters")
    return {name: str(i) for i, name in enumerate(params)}


def normalized_expr(row, key):
    mapping = level_mapping(row)

    def walk(x):
        if isinstance(x, list):
            if len(x) == 2 and x[0] == "param":
                need(x[1] in mapping, "Unbound CI universe parameter")
                return ["param", mapping[x[1]]]
            return [walk(item) for item in x]
        return x

    return len(mapping), walk(row[key])


def type_rows(path, pf, names, kinds):
    rows = written_json(path, pf)
    need(isinstance(rows, list) and len(rows) == len(names), "TypeOnly row count differs")
    seen = {}
    for row, name in zip(rows, names, strict=True):
        need(isinstance(row, dict) and set(row) ==
             {"name", "levelParams", "type", "value", "prettyType"}
             and row["name"] == name and isinstance(row["prettyType"], str)
             and bool(row["prettyType"]), "TypeOnly row schema/name differs: " + name)
        checked_expr(row["type"], set(row["levelParams"]))
        normalized_expr(row, "type")
        if kinds[name] == "theorem":
            need(row["value"] is None, "Theorem proof value was exported: " + name)
        else:
            need(kinds[name] == "def" and row["value"] is not None,
                 "Actual Def value missing: " + name)
            checked_expr(row["value"], set(row["levelParams"]))
            normalized_expr(row, "value")
        seen[name] = row
    return seen


def refs_doc(path, pf, side, name, module, main_module):
    doc = written_json(path, pf)
    need(isinstance(doc, dict) and set(doc) ==
         {"schemaVersion", "side", "probeMainModule", "importModule", "theorem"}
         and doc["schemaVersion"] == 1 and doc["side"] == side
         and doc["probeMainModule"] == main_module
         and doc["importModule"] == module,
         "Actual proof-reference envelope differs: " + name)
    return ap8c.evidence_row(doc["theorem"], name=name, module=module)


def insert_ci(table, row, *, module, helper=False):
    checked = ap8c.evidence_row(row, name=row["name"], module=module, helper=helper)
    name = checked["name"]
    if name in table:
        old = table[name]
        # A main row omits full type but includes its own auto-helper list.
        common = {k for k in checked if k in old and k not in {"automaticInlineHelpers", "type"}}
        need(all(checked[k] == old[k] for k in common),
             "Repeated actual CI row differs: " + name)
        if "type" in checked and "type" not in old:
            table[name] = checked
    else:
        table[name] = checked


def owner_module(name, plan):
    for row in plan["inline_exact_source_units"]:
        if row["name"] == name:
            return row["module"]
    if name == stage.TARGET:
        return stage.TARGET_MODULE
    raise ValueError("No exact source module owner for " + name)


def owned_inline_closure(rows, roots, provider_boundary):
    """Follow actual CI refs, stopping at certified imported provider names."""
    seen = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name in seen or name in provider_boundary or name not in rows:
            continue
        seen.add(name)
        pending.extend(rows[name]["allUsedConstants"])
    return seen


def private_pairing(source_private, generated_private, fixed_map):
    need(len(source_private) == len(generated_private),
         "Actual private helper CI counts differ")
    count = len(source_private)
    need(count <= 9, "More than nine actual private helpers require a bounded new pairing probe")
    source = [source_private[n] for n in sorted(source_private)]
    generated = [generated_private[n] for n in sorted(generated_private)]
    pairings = []
    for candidate in permutations(generated):
        mapping = dict(fixed_map)
        mapping.update({s["name"]: g["name"] for s, g in zip(source, candidate, strict=True)})
        if all(normalized_expr(s, "type")[0] == normalized_expr(g, "type")[0]
               and ap8c.rename_expr(normalized_expr(s, "type")[1], mapping) ==
                   normalized_expr(g, "type")[1]
               for s, g in zip(source, candidate, strict=True)):
            pairings.append([[s["name"], g["name"]]
                             for s, g in zip(source, candidate, strict=True)])
        need(len(pairings) <= 1, "Actual private CI types have non-unique source/generated pairing")
    need(len(pairings) == 1, "Actual private CI types have no source/generated pairing")
    return pairings[0]


def imported_dep(pf, module):
    return ap8c.imported_dep(pf, module)


def provider_certificates(solution_pf):
    """Bind AP9/AP10's certified Def bodies to their actual cached Oleans."""
    results = {}
    for family, producer, keys in [
        ("ap9", stage.ap9, stage.ap9.CONFIGS),
        ("ap10", stage.ap10, stage.ap10.CONFIGS),
    ]:
        for key in keys:
            c = producer.config(key)
            prepared = c["stage"] / "preparation.json"
            cert = c["stage"] / ("actual-provider-validation-helper-v2.json"
                                 if family == "ap10" and key == "determinant"
                                 else "actual-provider-validation.json")
            need(cert.is_file(), "Missing actual certified provider: " + rel(cert))
            row = read(cert)
            expected_kind = ("ap10-determinant-certified-proof-helper-provider-validation"
                             if family == "ap10" and key == "determinant"
                             else "ap10-core-data-actual-provider-validation"
                             if family == "ap10" else "ap9-foundational-actual-provider-validation")
            need(row["validated"] is True and row["artifact_kind"] == expected_kind
                 and row["source_commit"] == stage.COMMIT
                 and row["source_module"] == c["source_module"]
                 and row["platform_module"] == c["platform_module"]
                 and row["provided_names"] == c["names"]
                 and row["provider_source_sha256"] == sha(c["stage"] / c["provider_file"])
                 and row["preparation_sha256"] == sha(prepared)
                 and row["Std3_only"] is True and row["source_and_generated_types_equal"] is True,
                 "Actual AP9/AP10 certified provider binding differs: " + family + "/" + key)
            if family == "ap10" and key == "determinant":
                need(row["definition_values_equal_after_certified_proof_CI_substitution"] is True
                     and row["certified_actual_helper_pair"]["actual_closed_propositional_types_equal"] is True,
                     "AP10 determinant proof-helper exception is not actually certified")
            else:
                need(row["definition_values_equal_and_exported"] is True,
                     "AP9/AP10 provider full Def values are not certified")
            olean = TASK / row["provider_olean"]
            need(olean.is_file() and sha(olean) == row["provider_olean_sha256"],
                 "Certified provider OLean bytes changed: " + family + "/" + key)
            if family == "ap10" and key == "determinant":
                direct = imported_dep(solution_pf, c["platform_module"])
                need(Path(direct["path"]).resolve() == olean.resolve()
                     and direct["sha256_before"] == row["provider_olean_sha256"],
                     "AP11 solution did not import the actual certified AP10 determinant OLean")
            results[family + "/" + key] = {"certificate": rel(cert),
                                          "certificate_sha256": sha(cert),
                                          "provider_olean": rel(olean),
                                          "provider_olean_sha256": sha(olean)}
    return results


def preflight(filename, plan):
    path = STAGE / filename
    spec = plan["files"][filename]
    manifest = STAGE / spec["manifest"]
    module = ".".join(Path(filename).with_suffix("").parts)
    pf = context.record(path, manifest, spec["mode"], module, STAGE)
    m = read(manifest)
    need(pf["data"]["success"] is True and pf["data"]["exit_code"] == 0
         and pf["data"]["timed_out"] is False
         and 0 < pf["data"]["seconds"] <= 300
         and m["mode"] == spec["mode"] and m["emit_olean"] is spec["emit_olean"]
         and "emit_olean" not in pf["data"],
         "Bounded AP11 compiler mode/result differs: " + filename)
    return pf


def validate(*, write):
    stage.check_only()
    supplement.check_only()
    plan = read(STAGE / "preparation.json")
    need(plan["validated"] is False and plan["submission_ready"] is False
         and plan["proposal_status"] == "Draft" and len(plan["inline_exact_source_units"]) == 30,
         "Frozen AP11 preparation state differs")
    files = stage.FILES
    records = {filename: preflight(filename, plan) for filename in files}
    target_pf, solution_pf, source_pf, generated_pf = [records[x] for x in files]
    need(target_pf["data"]["output_olean"] is None
         and source_pf["data"]["output_olean"] is None
         and generated_pf["data"]["output_olean"] is None
         and solution_pf["data"]["output_olean"] is not None,
         "Comparator, solution, or snapshot OLean mode differs")
    solution_olean = V / "staged-build/lib/lean" / Path(*stage.SOLUTION_MODULE.split(".")).with_suffix(".olean")
    need(context.file(solution_pf["data"]["output_olean"]) == solution_olean.resolve()
         and sha(solution_olean) == solution_pf["data"]["output_olean_sha256"],
         "Global solution OLean differs from actual output")
    imported_dep(source_pf, stage.TARGET_MODULE)
    imported_solution = imported_dep(generated_pf, stage.SOLUTION_MODULE)
    need(Path(imported_solution["path"]).resolve() == solution_olean.resolve()
         and imported_solution["sha256_before"] == sha(solution_olean),
         "Generated snapshot did not import the exact solution OLean")
    certified_providers = provider_certificates(solution_pf)
    helper_stage = supplement.FOLDER
    helper_manifest = helper_stage / supplement.MANIFEST
    helper_file = helper_stage / supplement.PROBE_FILE
    helper_pf = context.record(helper_file, helper_manifest, "modecheck", "SourceHelperRefs", helper_stage)
    need(helper_pf["data"]["success"] is True and helper_pf["data"]["exit_code"] == 0
         and helper_pf["data"]["timed_out"] is False
         and 0 < helper_pf["data"]["seconds"] <= 300
         and helper_pf["data"]["output_olean"] is None
         and "emit_olean" not in helper_pf["data"],
         "Actual additive source-helper CI probe differs")
    imported_dep(helper_pf, stage.TARGET_MODULE)

    explicit = [x["name"] for x in plan["inline_exact_source_units"]]
    kinds = {x["name"]: x["kind"] for x in plan["inline_exact_source_units"]}
    kinds[stage.TARGET] = "theorem"
    source_types = type_rows(STAGE / stage.SOURCE_TYPE_JSON, source_pf,
                             explicit + [stage.TARGET], kinds)
    generated_kinds = {**kinds, "solution": "theorem"}
    generated_types = type_rows(STAGE / stage.GENERATED_TYPE_JSON, generated_pf,
                                explicit + ["solution"], generated_kinds)
    need(normalized_expr(source_types[stage.TARGET], "type") ==
         normalized_expr(generated_types["solution"], "type"),
         "Original theorem and global solution kernel types differ")
    for name in explicit:
        need(normalized_expr(source_types[name], "type") ==
             normalized_expr(generated_types[name], "type"),
             "Inline original/helper kernel types differ: " + name)
        if kinds[name] == "def":
            need(normalized_expr(source_types[name], "value") ==
                 normalized_expr(generated_types[name], "value"),
                 "Inline original/solution full Def values differ: " + name)

    source_main = refs_doc(STAGE / stage.SOURCE_REFS_JSON, source_pf,
                           "source", stage.TARGET, stage.TARGET_MODULE,
                           Path(stage.SOURCE_SNAPSHOT).stem)
    generated_main = refs_doc(STAGE / stage.GENERATED_REFS_JSON, generated_pf,
                              "generated", "solution", stage.SOLUTION_MODULE,
                              Path(stage.GENERATED_SNAPSHOT).stem)
    source_axioms = standalone.audit_axioms(context.file(source_pf["data"]["log"]), stage.TARGET)
    generated_axioms = standalone.audit_axioms(context.file(generated_pf["data"]["log"]), "solution")
    need(source_axioms == source_main["axioms"] == generated_axioms == generated_main["axioms"]
         and set(source_axioms) <= STD3,
         "Source/generated #print axioms logs or actual CI axiom sets differ")

    source_ci, generated_ci = {}, {}
    insert_ci(source_ci, source_main, module=stage.TARGET_MODULE)
    for row in source_main["automaticInlineHelpers"]:
        insert_ci(source_ci, row, module=stage.TARGET_MODULE, helper=True)
    insert_ci(generated_ci, generated_main, module=stage.SOLUTION_MODULE)
    for row in generated_main["automaticInlineHelpers"]:
        insert_ci(generated_ci, row, module=stage.SOLUTION_MODULE, helper=True)
    requests = read(helper_stage / supplement.PREPARATION)["actual_CI_requests"]
    need([x["name"] for x in requests] == explicit, "Supplemental actual CI request order differs")
    output_paths = [STAGE / stage.SOURCE_TYPE_JSON, STAGE / stage.GENERATED_TYPE_JSON,
                    STAGE / stage.SOURCE_REFS_JSON, STAGE / stage.GENERATED_REFS_JSON]
    for request in requests:
        name, module = request["name"], request["source_module"]
        need(module == owner_module(name, plan), "Source helper module authority differs")
        output = TASK / request["output"]
        row = refs_doc(output, helper_pf, "source-helper", name, module, "SourceHelperRefs")
        insert_ci(source_ci, row, module=module)
        for extra in row["automaticInlineHelpers"]:
            insert_ci(source_ci, extra, module=module, helper=True)
        output_paths.append(output)
    need(set(explicit) <= set(source_ci) and set(explicit) <= set(generated_ci),
         "A named helper has no actual source/generated proof CI evidence")
    need(stage.TARGET in source_ci and "solution" in generated_ci,
         "Missing original target/global solution proof CIs")
    for name, type_row in source_types.items():
        ci = source_ci[name]
        need(type_row["levelParams"] == ci["levelParams"]
             and ap8c.refs(type_row["type"]) == ci["typeRefs"],
             "Original TypeOnly/proof CI mismatch: " + name)
    for name, type_row in generated_types.items():
        ci = generated_ci[name]
        need(type_row["levelParams"] == ci["levelParams"]
             and ap8c.refs(type_row["type"]) == ci["typeRefs"],
             "Generated TypeOnly/proof CI mismatch: " + name)

    fixed_map = {stage.TARGET: "solution", **{name: name for name in explicit}}
    provider_boundary = set(plan["provider_subtracted_names"])
    need(len(provider_boundary) == 40 and not provider_boundary & set(fixed_map),
         "Exact 71-name closure provider boundary differs")
    source_inline = owned_inline_closure(source_ci, fixed_map, provider_boundary)
    generated_inline = owned_inline_closure(generated_ci,
                                            set(explicit) | {"solution"}, provider_boundary)
    need(set(fixed_map) <= source_inline and set(explicit) | {"solution"} <= generated_inline,
         "A named source/generated inline CI is outside the actual owned proof closure")
    source_private = {n: source_ci[n] for n in source_inline if n not in fixed_map}
    generated_private = {n: generated_ci[n] for n in generated_inline
                         if n not in set(explicit) | {"solution"}}
    paired = private_pairing(source_private, generated_private, fixed_map)
    mapping = {**fixed_map, **dict(paired)}
    graph_names = {json.loads(line)["name"] for line in stage.GRAPH.read_text(encoding="utf-8").splitlines()
                   if line.strip()}
    project_names = graph_names | set(source_ci) | set(generated_ci)
    source_project_refs = {x for n in source_inline for x in source_ci[n]["allUsedConstants"]
                           if x in project_names}
    generated_project_refs = {x for n in generated_inline for x in generated_ci[n]["allUsedConstants"]
                              if x in project_names}
    need(source_project_refs <= set(plan["graph_closure_names"]) | set(source_private)
         and generated_project_refs <=
             (set(plan["graph_closure_names"]) - {stage.TARGET}) |
             {"solution"} | set(generated_private),
         "Actual proof CI refers to a project declaration outside the certified closure")
    external_diffs = {}
    for source_name, generated_name in mapping.items():
        s, g = source_ci[source_name], generated_ci[generated_name]
        need(s["axioms"] == g["axioms"], "Source/generated CI axiom sets differ: " + source_name)
        if "type" in s and "type" in g:
            need(normalized_expr(s, "type")[0] == normalized_expr(g, "type")[0]
                 and ap8c.rename_expr(normalized_expr(s, "type")[1], mapping) ==
                     normalized_expr(g, "type")[1],
                 "Actual helper CI types differ: " + source_name)
        mapped = lambda values: {mapping.get(x, x) for x in values}
        need(mapped(s["typeRefs"]) == set(g["typeRefs"]),
             "Actual helper CI type references differ: " + source_name)
        left, right = mapped(s["valueRefs"]), set(g["valueRefs"])
        source_only, generated_only = sorted(left - right), sorted(right - left)
        need(len(source_only) <= 32 and len(generated_only) <= 32
             and not (set(source_only) | set(generated_only)) & project_names,
             "Actual proof reference difference includes project CI or is unbounded: " + source_name)
        if source_only or generated_only:
            external_diffs[source_name] = {"source_only_after_actual_mapping": source_only,
                                           "generated_only_after_actual_mapping": generated_only}

    original_command = (STAGE / "original-target-command.lean.txt").read_bytes()
    unit = plan["target_ast"]
    proof_start = unit["valueStart"]["offset"] - unit["start"]["offset"]
    ns = unit["nameRange"]["start"]["offset"] - unit["start"]["offset"]
    ne = unit["nameRange"]["end"]["offset"] - unit["start"]["offset"]
    expected_solution = (original_command[:ns] + b"solution" + original_command[ne:]).replace(b"\r\n", b"\n")
    solution_bytes = (STAGE / stage.SOLUTION_OUTPUT).read_bytes()
    original_source = stage.source_path(stage.TARGET_MODULE, "source").read_bytes().replace(b"\r\n", b"\n")
    need(original_source.count(original_command.replace(b"\r\n", b"\n")) == 1
         and hashlib.sha256(original_command).hexdigest() == plan["target_source_command_sha256"]
         and solution_bytes.endswith(expected_solution + b"\n")
         and expected_solution[expected_solution.find(b":= by"):] ==
             original_command[proof_start:].replace(b"\r\n", b"\n")
         and b"sorry" not in solution_bytes,
         "Global solution does not contain the exact original source proof after name replacement")
    before = solution_bytes[:-len(expected_solution) - 1]
    need(before.rstrip().endswith(b"open scoped Topology")
         and b"theorem solution" not in before,
         "Final theorem solution is not global top-level")
    need((STAGE / "wire-theorem-source.lean").read_bytes() ==
         (STAGE / stage.TARGET_OUTPUT).read_bytes(),
         "Exact comparator/wire theorem source differs")

    report = {
        "schema_version": 1,
        "artifact_kind": "ap11-grouped-collision-rate-strict-actual-node-validation",
        "validated": True, "source_name": stage.TARGET, "solution_name": "solution",
        "source_module": stage.TARGET_MODULE, "solution_module": stage.SOLUTION_MODULE,
        "source_commit": stage.COMMIT,
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "additive_probe_preparation_sha256": sha(helper_stage / supplement.PREPARATION),
        "source_ast_unit_sha256": sha(STAGE / "original-target-command.lean.txt"),
        "wire_theorem_sha256": sha(STAGE / "wire-theorem-source.lean"),
        "source_type_equals_global_solution_type": True,
        "source_helper_types_equal": True, "source_helper_full_def_values_equal": True,
        "source_original_proof_byte_exact_after_name_change": True,
        "global_top_level_theorem_solution": True,
        "type_only_theorem_values_null": True,
        "source_helper_count": len(explicit),
        "source_helper_actual_owners": {name: source_ci[name]["owner"] for name in explicit},
        "generated_helper_actual_owners": {name: generated_ci[name]["owner"] for name in explicit},
        "source_owner": source_main["owner"], "generated_owner": generated_main["owner"],
        "source_axioms": source_axioms, "generated_axioms": generated_axioms,
        "Std3_only": True, "actual_private_helper_pairs": paired,
        "external_elaboration_reference_differences": external_diffs,
        "actual_source_project_references": sorted(source_project_refs),
        "actual_generated_project_references": sorted(generated_project_refs),
        "solution_olean": rel(solution_olean), "solution_olean_sha256": sha(solution_olean),
        "certified_AP9_AP10_provider_bindings": certified_providers,
        "primary_preflights": records, "source_helper_preflight": helper_pf,
        "output_json_sha256": {rel(path): sha(path) for path in output_paths},
        "implementation_hashes": {rel(path): sha(path) for path in
                                  [SELF, Path(stage.__file__), Path(supplement.__file__),
                                   Path(context.__file__), Path(ap8c.__file__),
                                   TASK / "scripts/preflight_staged_module.py"]},
        "max_file_seconds": max(pf["data"]["seconds"] for pf in [*records.values(), helper_pf]),
        "submission_ready": False, "proposal_status": "Draft",
        "Lean_started_by_consumer": False, "API_used": False,
    }
    raw = (json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode()
    if write:
        if CERT.exists():
            need(CERT.read_bytes() == raw, "Existing AP11 certificate differs; refusing overwrite")
        else:
            CERT.write_bytes(raw)
    else:
        need(CERT.is_file() and CERT.read_bytes() == raw,
             "Saved AP11 certificate differs from exact read-only replay")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--certify-existing", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    report = validate(write=args.certify_existing)
    print(json.dumps({"validated": True, "certificate": rel(CERT),
                      "certificate_sha256": sha(CERT),
                      "max_file_seconds": report["max_file_seconds"],
                      "Lean_started": False, "API_used": False}, indent=2))
