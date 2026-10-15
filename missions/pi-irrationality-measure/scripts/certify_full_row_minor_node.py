"""Pure, strict replay of the four compiled full-row-minor node contexts.

This consumer reads saved files only. It never starts Lean or contacts Prove2Me.
"""
from __future__ import annotations

import argparse
from datetime import datetime
import hashlib
from itertools import permutations
import json
from pathlib import Path

import stage_full_row_minor_node as stage
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone
from validate_formal_log_node import checked_expr


TASK, V, STAGE = stage.TASK, stage.V, stage.STAGE
SELF = Path(__file__).resolve()
CERT = STAGE / "node-validation.json"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def need(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def rel(path: Path) -> str:
    return path.relative_to(TASK).as_posix()


def refs(expr):
    found = set()

    def visit(value):
        if not isinstance(value, list):
            return
        if len(value) >= 2 and value[0] in ("const", "projection") and isinstance(value[1], str):
            found.add(value[1])
        for child in value[1:]:
            visit(child)

    visit(expr)
    return sorted(found)


def normalized_type(row):
    params = row["levelParams"]
    need(isinstance(params, list) and all(isinstance(x, str) for x in params)
         and len(params) == len(set(params)), "Malformed universe parameter list")
    mapping = {name: str(i) for i, name in enumerate(params)}

    def walk(value):
        if isinstance(value, list):
            if len(value) == 2 and value[0] == "param":
                need(value[1] in mapping, "Unbound universe parameter")
                return ["param", mapping[value[1]]]
            return [walk(item) for item in value]
        return value

    return len(params), walk(row["type"])


def rename_expr(expr, mapping):
    if isinstance(expr, list):
        if len(expr) >= 2 and expr[0] in ("const", "projection") and isinstance(expr[1], str):
            expr = list(expr)
            expr[1] = mapping.get(expr[1], expr[1])
        return [rename_expr(item, mapping) for item in expr]
    return expr


def imported_owner(row, module):
    owner = row["owner"]
    need(isinstance(owner, dict) and set(owner) == {"kind", "module", "moduleIndex"}
         and owner["kind"] == "ImportedModule" and owner["module"] == module
         and type(owner["moduleIndex"]) is int and owner["moduleIndex"] >= 0,
         "Proof CI is not imported from the asserted compiled module")
    return owner


def evidence_row(row, *, name, module, helper=False):
    required = {"name", "levelParams", "closedType", "closedValue", "typeRefs",
                "valueRefs", "allUsedConstants", "axioms", "owner"}
    if helper:
        required.add("type")
    else:
        required.add("automaticInlineHelpers")
    need(isinstance(row, dict) and set(row) == required and row["name"] == name
         and row["closedType"] is True and row["closedValue"] is True,
         "Proof CI schema/identity/closedness differs: " + name)
    levels = row["levelParams"]
    need(isinstance(levels, list) and all(isinstance(x, str) for x in levels)
         and len(levels) == len(set(levels)), "Invalid proof CI universe binders: " + name)
    for key in ("typeRefs", "valueRefs", "allUsedConstants", "axioms"):
        values = row[key]
        need(isinstance(values, list) and all(isinstance(x, str) for x in values)
             and values == sorted(set(values)), "Malformed actual proof CI " + key + ": " + name)
    need(row["allUsedConstants"] == sorted(set(row["typeRefs"] + row["valueRefs"])),
         "Actual proof CI used constants differ from type/value references: " + name)
    need(set(row["axioms"]) <= STD3, "Proof exceeds Std3: " + name)
    imported_owner(row, module)
    if helper:
        checked_expr(row["type"], set(levels))
        need(refs(row["type"]) == row["typeRefs"], "Helper complete type refs differ")
    return row


def written_json(path, pf):
    data = pf["data"]
    finished = datetime.fromisoformat(data["at_utc"]).timestamp()
    need(path.is_file() and finished - data["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "Output JSON was not written during its exact compiler invocation: " + rel(path))
    return read(path)


def snapshot(path, pf, name):
    rows = written_json(path, pf)
    need(isinstance(rows, list) and len(rows) == 1 and isinstance(rows[0], dict)
         and set(rows[0]) == {"name", "levelParams", "type", "value", "prettyType"},
         "Type-only snapshot schema differs: " + rel(path))
    row = rows[0]
    need(row["name"] == name and row["value"] is None
         and isinstance(row["prettyType"], str) and bool(row["prettyType"]),
         "Theorem snapshot name or null proof value differs: " + name)
    checked_expr(row["type"], set(row["levelParams"]))
    normalized_type(row)
    return row


def refs_document(path, pf, side, main_module, name, imported_module):
    doc = written_json(path, pf)
    need(isinstance(doc, dict) and set(doc) == {"schemaVersion", "side", "probeMainModule", "importModule", "theorem"}
         and doc["schemaVersion"] == 1 and doc["side"] == side
         and doc["probeMainModule"] == main_module and doc["importModule"] == imported_module,
         "Proof-reference document envelope differs: " + side)
    return evidence_row(doc["theorem"], name=name, module=imported_module)


def imported_dep(pf, module):
    matches = [x for x in pf["data"]["dependency_oleans"] if x["module"] == module]
    need(len(matches) == 1, "Missing/ambiguous imported proof module: " + module)
    entry = matches[0]
    path = Path(entry["path"])
    need(path.is_file() and sha(path) == entry["sha256_before"] == entry["sha256_after"]
         and entry["stable_during_compile"] is True,
         "Imported proof OLean differs from actual first-search compiler input: " + module)
    return entry


def validate(*, write):
    stage.check_only()
    plan = read(STAGE / "preparation.json")
    need(plan["validated"] is False and plan["submission_ready"] is False
         and plan["proposal_status"] == "Draft", "Prepared node state differs")
    files = [stage.SOURCE_OUTPUT, stage.SOLUTION_OUTPUT,
             stage.SOURCE_SNAPSHOT, stage.GENERATED_SNAPSHOT]
    records = {}
    for filename in files:
        path = STAGE / filename
        spec = plan["files"][filename]
        manifest = STAGE / spec["manifest"]
        mode = spec["mode"]
        module = ".".join(Path(filename).with_suffix("").parts)
        pf = context.record(path, manifest, mode, module, STAGE)
        need(pf["data"]["success"] is True and pf["data"]["exit_code"] == 0
             and pf["data"]["timed_out"] is False
             and 0 < pf["data"]["seconds"] <= 300
             and read(manifest)["mode"] == mode
             and read(manifest)["emit_olean"] is spec["emit_olean"]
             and "emit_olean" not in pf["data"],
             "Actual bounded preflight/manifest mode differs: " + filename)
        records[filename] = pf
    target_pf, solution_pf, source_pf, generated_pf = [records[x] for x in files]
    need(target_pf["data"]["output_olean"] is None
         and source_pf["data"]["output_olean"] is None
         and generated_pf["data"]["output_olean"] is None
         and solution_pf["data"]["output_olean"] is not None,
         "Comparator/probe OLean emission mode differs")
    solution_module = ".".join(Path(stage.SOLUTION_OUTPUT).with_suffix("").parts)
    solution_olean = V / "staged-build/lib/lean" / Path(*solution_module.split(".")).with_suffix(".olean")
    need(context.file(solution_pf["data"]["output_olean"]) == solution_olean.resolve()
         and sha(solution_olean) == solution_pf["data"]["output_olean_sha256"],
         "Emitted solution OLean differs from exact compiler output")
    imported_dep(source_pf, stage.MODULE)
    imported_solution = imported_dep(generated_pf, solution_module)
    need(Path(imported_solution["path"]).resolve() == solution_olean.resolve()
         and imported_solution["sha256_before"] == sha(solution_olean),
         "Generated probe did not import the just-compiled solution OLean")

    src_type = snapshot(STAGE / stage.SOURCE_TYPE_JSON, source_pf, stage.NAME)
    gen_type = snapshot(STAGE / stage.GENERATED_TYPE_JSON, generated_pf, "solution")
    need(normalized_type(src_type) == normalized_type(gen_type),
         "Source and top-level solution kernel types differ")
    source_main = refs_document(STAGE / stage.SOURCE_REFS_JSON, source_pf,
                                "source", Path(stage.SOURCE_SNAPSHOT).stem,
                                stage.NAME, stage.MODULE)
    generated_main = refs_document(STAGE / stage.GENERATED_REFS_JSON, generated_pf,
                                   "generated", Path(stage.GENERATED_SNAPSHOT).stem,
                                   "solution", solution_module)
    need(src_type["levelParams"] == source_main["levelParams"]
         and gen_type["levelParams"] == generated_main["levelParams"]
         and refs(src_type["type"]) == source_main["typeRefs"]
         and refs(gen_type["type"]) == generated_main["typeRefs"],
         "Proof-reference theorem identity/type differs from type-only snapshot")
    source_axioms = standalone.audit_axioms(context.file(source_pf["data"]["log"]), stage.NAME)
    generated_axioms = standalone.audit_axioms(context.file(generated_pf["data"]["log"]), "solution")
    need(source_axioms == source_main["axioms"] == generated_axioms == generated_main["axioms"],
         "Actual #print axioms logs differ from imported theorem CI")

    src_helpers = source_main["automaticInlineHelpers"]
    gen_helpers = generated_main["automaticInlineHelpers"]
    need(isinstance(src_helpers, list) and isinstance(gen_helpers, list)
         and len(src_helpers) == len(gen_helpers) <= 8,
         "Actual automatic helper domain differs or exceeds bounded node")
    src_names = [h["name"] for h in src_helpers]
    gen_names = [h["name"] for h in gen_helpers]
    need(src_names == sorted(set(src_names)) and gen_names == sorted(set(gen_names))
         and set(src_names) & set(gen_names) == set(),
         "Actual helper rows are repeated or not deterministic")
    for s in src_helpers:
        evidence_row(s, name=s["name"], module=stage.MODULE, helper=True)
    for g in gen_helpers:
        evidence_row(g, name=g["name"], module=solution_module, helper=True)
    matchings = []
    for candidate in permutations(gen_helpers):
        mapping = {stage.NAME: "solution"}
        mapping.update({s["name"]: g["name"] for s, g in zip(src_helpers, candidate, strict=True)})
        mapped = lambda values: sorted(mapping.get(value, value) for value in values)
        if mapped(source_main["typeRefs"]) != generated_main["typeRefs"]:
            continue
        if all(normalized_type(s)[0] == normalized_type(g)[0]
               and rename_expr(normalized_type(s)[1], mapping) == normalized_type(g)[1]
               and mapped(s["typeRefs"]) == g["typeRefs"]
               and mapped(s["valueRefs"]) == g["valueRefs"]
               and mapped(s["allUsedConstants"]) == g["allUsedConstants"]
               and s["axioms"] == g["axioms"]
               for s, g in zip(src_helpers, candidate, strict=True)):
            matchings.append([[s["name"], g["name"]]
                              for s, g in zip(src_helpers, candidate, strict=True)])
    need(len(matchings) == 1, "Actual helper type/reference graph has no unique source/solution pairing")
    paired = matchings[0]
    helper_map = {stage.NAME: "solution", **{source: generated for source, generated in paired}}
    mapped_source_values = {helper_map.get(r, r) for r in source_main["valueRefs"]}
    generated_values = set(generated_main["valueRefs"])
    source_only_refs = sorted(mapped_source_values - generated_values)
    generated_only_refs = sorted(generated_values - mapped_source_values)
    # The literal source proof is elaborated under two real import contexts.
    # Local helper CIs match exactly; any remaining difference must be a finite,
    # explicitly recorded external instance choice, never an OAI dependency.
    need(len(source_only_refs) <= 16 and len(generated_only_refs) <= 16,
         "Source/solution external elaboration reference difference is unbounded")
    graph_names = {json.loads(line)["name"] for line in stage.GRAPH.read_text(encoding="utf-8").splitlines()
                   if line.strip()}
    project_names = graph_names | set(src_names) | set(gen_names)
    project_name = lambda name: name in project_names
    need(not any(project_name(r) for r in source_only_refs + generated_only_refs),
         "Source/solution proof reference difference contains an OAI constant")
    actual_project_refs = {r for ci in [source_main, *src_helpers] for r in ci["allUsedConstants"]
                           if project_name(r)}
    generated_project_refs = {r for ci in [generated_main, *gen_helpers] for r in ci["allUsedConstants"]
                              if project_name(r)}
    need(actual_project_refs <= set(src_names)
         and generated_project_refs <= set(gen_names),
         "This generic source proof has an uncertified project constant dependency")

    source_command = stage.source_unit()
    exact_solution_command = source_command.replace(
        b"theorem exists_full_row_minor_of_surjective",
        b"theorem solution", 1)
    solution_bytes = (STAGE / stage.SOLUTION_OUTPUT).read_bytes()
    need(exact_solution_command != source_command
         and solution_bytes.endswith(exact_solution_command)
         and b"namespace " not in solution_bytes[: -len(exact_solution_command)]
         and b"sorry" not in solution_bytes,
         "Compiled global solution is not exact renamed source AST proof")
    expected_target = (plan["preamble"] + plan["formal_statement"]).encode("utf-8")
    need((STAGE / stage.SOURCE_OUTPUT).read_bytes() == expected_target
         and (STAGE / "wire-theorem-source.lean").read_bytes() == expected_target,
         "Compiled comparator differs from exact platform preamble + statement")
    outputs = [STAGE / x for x in (stage.SOURCE_TYPE_JSON, stage.GENERATED_TYPE_JSON,
                                   stage.SOURCE_REFS_JSON, stage.GENERATED_REFS_JSON)]
    report = {
        "schema_version": 1,
        "artifact_kind": "ap8-full-row-minor-strict-actual-node-validation",
        "validated": True,
        "source_name": stage.NAME,
        "solution_name": "solution",
        "source_module": stage.MODULE,
        "solution_module": solution_module,
        "source_commit": stage.SOURCE_COMMIT,
        "source_url": stage.SOURCE_URL,
        "source_sha256": sha(stage.SOURCE),
        "original_source_sha256": sha(stage.ORIGINAL),
        "source_ast_unit_sha256": hashlib.sha256(source_command).hexdigest(),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "wire_theorem_sha256": sha(STAGE / "wire-theorem-source.lean"),
        "source_type_equals_solution_type": True,
        "source_proof_byte_exact_after_name_change": True,
        "top_level_global_theorem_solution": True,
        "type_only_theorem_values_null": True,
        "source_owner": source_main["owner"],
        "generated_owner": generated_main["owner"],
        "source_axioms": source_axioms,
        "generated_axioms": generated_axioms,
        "Std3_only": True,
        "automatic_inline_helper_pairs": paired,
        "external_elaboration_reference_difference": {
            "source_only_after_actual_helper_mapping": source_only_refs,
            "solution_only_after_actual_helper_mapping": generated_only_refs},
        "actual_source_project_references": sorted(actual_project_refs),
        "actual_generated_project_references": sorted(generated_project_refs),
        "solution_olean": rel(solution_olean),
        "solution_olean_sha256": sha(solution_olean),
        "preflights": records,
        "output_json_sha256": {rel(path): sha(path) for path in outputs},
        "implementation_hashes": {rel(path): sha(path) for path in (
            SELF, Path(stage.__file__), Path(context.__file__), Path(standalone.__file__),
            TASK / "scripts/preflight_staged_module.py",
            TASK / "scripts/validate_shared_source_snapshot.py",
            TASK / "scripts/validate_formal_log_node.py")},
        "max_file_seconds": max(pf["data"]["seconds"] for pf in records.values()),
        "submission_ready": False,
        "proposal_status": "Draft",
        "Lean_started_by_consumer": False,
        "API_used": False,
    }
    raw = (json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    if write:
        if CERT.exists():
            need(CERT.read_bytes() == raw, "Existing certificate differs; refusing overwrite")
        else:
            CERT.write_bytes(raw)
    else:
        need(CERT.is_file() and CERT.read_bytes() == raw,
             "Saved certificate differs from exact read-only evidence replay")
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
