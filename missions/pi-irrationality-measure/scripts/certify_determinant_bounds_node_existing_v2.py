"""Pure strict consumer for the four compiled determinant-bounds artifacts."""
from __future__ import annotations

from datetime import datetime
from itertools import permutations
import hashlib
import json
from pathlib import Path

import prepare_determinant_bounds_global_node as stage
import prepare_determinant_bounds_node as old_stage
import preflight_staged_module as runner
import validate_formal_log_node as kernel
import validate_namespace_context_providers as context
import validate_standalone_platform_node as standalone

TASK, V, STAGE = stage.TASK, stage.V, stage.STAGE
SELF = Path(__file__).resolve()
OLD_CONSUMER = TASK / "scripts/certify_determinant_bounds_node_existing.py"
CERT = STAGE / "node-validation-v2.json"
SOLUTION_MODULE = "Solutions.Sol_OAI_PiExponent_determinant_bounds_inconsistent_global"
STD3 = {"propext", "Classical.choice", "Quot.sound"}


def need(ok, why):
    if not ok:
        raise ValueError(why)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def rel(path):
    return path.relative_to(TASK).as_posix()


def refs(expr):
    found = set()
    def visit(node):
        if not isinstance(node, list):
            return
        if len(node) == 3 and node[0] == "const" and isinstance(node[1], str):
            found.add(node[1])
        elif len(node) >= 3 and node[0] == "projection" and isinstance(node[1], str):
            found.add(node[1])
        for item in node[1:]:
            visit(item)
    visit(expr)
    return sorted(found)


def rename_expr(expr, mapping):
    if isinstance(expr, list):
        if len(expr) >= 2 and expr[0] in ("const", "projection") and isinstance(expr[1], str):
            expr = list(expr)
            expr[1] = mapping.get(expr[1], expr[1])
        return [rename_expr(item, mapping) for item in expr]
    return expr


def normalized_type(ci):
    params = {name: "u" + str(index) for index, name in enumerate(ci["levelParams"])}
    def walk(node):
        if isinstance(node, list):
            if len(node) == 2 and node[0] == "param" and node[1] in params:
                return ["param", params[node[1]]]
            return [walk(item) for item in node]
        return node
    return len(params), walk(ci["type"])


def owner(ci, module):
    row = ci["owner"]
    need(isinstance(row, dict) and set(row) == {"kind", "module", "moduleIndex"}
         and row["kind"] == "ImportedModule" and row["module"] == module
         and type(row["moduleIndex"]) is int and row["moduleIndex"] >= 0,
         "Actual imported CI owner differs: " + ci["name"])


def full_ci(ci, *, name, module, helper):
    keys = {"name", "levelParams", "closedType", "closedValue", "type", "value",
            "typeRefs", "valueRefs", "axioms", "owner"}
    if not helper:
        keys.add("automaticInlineHelpers")
    need(isinstance(ci, dict) and set(ci) == keys and ci["name"] == name
         and ci["closedType"] is True and ci["closedValue"] is True,
         "Actual full theorem CI schema/name/closedness differs: " + name)
    params = ci["levelParams"]
    need(isinstance(params, list) and all(isinstance(x, str) for x in params)
         and len(params) == len(set(params)), "Malformed CI universe parameters: " + name)
    kernel.checked_expr(ci["type"], set(params))
    kernel.checked_expr(ci["value"], set(params))
    need(ci["typeRefs"] == refs(ci["type"]) and ci["valueRefs"] == refs(ci["value"]),
         "Actual CI references differ from complete kernel expressions: " + name)
    axioms = ci["axioms"]
    need(isinstance(axioms, list) and axioms == sorted(set(axioms))
         and set(axioms) <= STD3, "Theorem CI axioms exceed Std3: " + name)
    owner(ci, module)
    return ci


def written_json(path, pf):
    finished = datetime.fromisoformat(pf["data"]["at_utc"]).timestamp()
    need(finished - pf["data"]["seconds"] - 2 <= path.stat().st_mtime <= finished + 2,
         "Exported JSON was not written during exact preflight: " + rel(path))
    return read(path)


def type_snapshot(path, pf, name, ci):
    rows = written_json(path, pf)
    need(isinstance(rows, list) and len(rows) == 1 and isinstance(rows[0], dict)
         and set(rows[0]) == {"name", "levelParams", "type", "value", "prettyType"},
         "Typed snapshot schema differs: " + rel(path))
    row = rows[0]
    need(row["name"] == name and row["levelParams"] == ci["levelParams"]
         and row["type"] == ci["type"] and row["value"] == ci["value"]
         and row["value"] is not None and isinstance(row["prettyType"], str)
         and row["prettyType"],
         "Typed theorem proof value/type differ from actual full-CI probe: " + name)
    return row


def unique_helper_pairing(source_main, generated_main, source_helpers, generated_helpers):
    need(len(source_helpers) == len(generated_helpers) <= 8,
         "Actual source/generated auto-helper domains differ or are unbounded")
    source_names = [h["name"] for h in source_helpers]
    generated_names = [h["name"] for h in generated_helpers]
    need(len(set(source_names)) == len(source_names)
         and len(set(generated_names)) == len(generated_names)
         and source_names == [r for r in source_main["valueRefs"]
                              if r.startswith(source_main["name"] + "._proof_")]
         and generated_names == [r for r in generated_main["valueRefs"]
                                 if r.startswith(generated_main["name"] + "._proof_")],
         "Auto-helper names differ from actual immediate theorem proof references")
    matches = []
    for candidate in permutations(generated_helpers):
        mapping = {source_main["name"]: generated_main["name"]}
        mapping.update({src["name"]: gen["name"]
                        for src, gen in zip(source_helpers, candidate, strict=True)})
        if rename_expr(source_main["value"], mapping) != generated_main["value"]:
            continue
        if all(normalized_type(src) == normalized_type(gen)
               and rename_expr(src["value"], mapping) == gen["value"]
               for src, gen in zip(source_helpers, candidate, strict=True)):
            matches.append((mapping, candidate))
            if len(matches) > 1:
                break
    need(len(matches) == 1,
         "Actual auto-proof CIs lack a unique source/generated type-and-value pairing")
    mapping, candidate = matches[0]
    return mapping, [{"source_name": src["name"], "generated_name": gen["name"],
                      "source_owner": src["owner"], "generated_owner": gen["owner"],
                      "source_axioms": src["axioms"], "generated_axioms": gen["axioms"]}
                     for src, gen in zip(source_helpers, candidate, strict=True)]


def validate(*, write):
    stage.check_only()
    plan = read(STAGE / "preparation.json")
    need(plan["status"] == "prepared-uncompiled" and plan["validated"] is False
         and plan["proposal_status"] == "Draft" and plan["submission_ready"] is False,
         "Prepared determinant node state changed")
    files = [stage.SOURCE_OUTPUT, stage.SOLUTION_OUTPUT,
             stage.SOURCE_SNAPSHOT, stage.GENERATED_SNAPSHOT]
    records = {}
    for filename in files:
        path = STAGE / filename
        manifest = STAGE / (Path(filename).name + ".json")
        spec = plan["files"][filename]
        mode = spec["mode"]
        module = ".".join(Path(filename).with_suffix("").parts)
        pf = context.record(path, manifest, mode, module, STAGE)
        need(pf["data"]["success"] is True and pf["data"]["exit_code"] == 0
             and pf["data"]["timed_out"] is False
             and 0 < pf["data"]["seconds"] <= 300
             and read(manifest)["mode"] == mode
             and read(manifest)["emit_olean"] is spec["emit_olean"],
             "Actual bounded preflight/manifest mode differs: " + filename)
        records[filename] = pf
    target_pf = records[stage.SOURCE_OUTPUT]
    solution_pf = records[stage.SOLUTION_OUTPUT]
    source_pf = records[stage.SOURCE_SNAPSHOT]
    generated_pf = records[stage.GENERATED_SNAPSHOT]
    need(target_pf["data"]["output_olean"] is None
         and source_pf["data"]["output_olean"] is None
         and generated_pf["data"]["output_olean"] is None
         and solution_pf["data"]["output_olean"] is not None,
         "Comparator/snapshot emitted OLean or solution failed to emit OLean")
    expected_olean = V / "staged-build/lib/lean/Solutions/Sol_OAI_PiExponent_determinant_bounds_inconsistent_global.olean"
    need(context.file(solution_pf["data"]["output_olean"]) == expected_olean.resolve()
         and sha(expected_olean) == solution_pf["data"]["output_olean_sha256"],
         "Emitted solution OLean differs from actual preflight")
    imports = [row for row in generated_pf["data"]["dependency_oleans"]
               if row["module"] == SOLUTION_MODULE]
    need(len(imports) == 1 and Path(imports[0]["path"]).resolve() == expected_olean.resolve()
         and imports[0]["sha256_before"] == imports[0]["sha256_after"] == sha(expected_olean)
         and imports[0]["stable_during_compile"] is True,
         "Generated proof snapshot did not import exact emitted solution OLean")
    src_doc = written_json(STAGE / "source-proof-references.json", source_pf)
    gen_doc = written_json(STAGE / "generated-proof-references.json", generated_pf)
    for doc, side, module in ((src_doc, "source", "SourceSnapshot"),
                              (gen_doc, "generated", "GeneratedSnapshotWithRefs")):
        need(isinstance(doc, dict) and set(doc) == {
            "schemaVersion", "side", "probeMainModule", "theorem"}
            and doc["schemaVersion"] == 1 and doc["side"] == side
            and doc["probeMainModule"] == module,
            "Actual complete proof-reference probe envelope differs: " + side)
    src = full_ci(src_doc["theorem"], name=stage.NAME, module=stage.MODULE, helper=False)
    gen = full_ci(gen_doc["theorem"], name="solution", module=SOLUTION_MODULE, helper=False)
    src_type = type_snapshot(STAGE / "source-type.json", source_pf, stage.NAME, src)
    gen_type = type_snapshot(STAGE / "generated-type.json", generated_pf, "solution", gen)
    need(normalized_type(src) == normalized_type(gen),
         "Source/solution theorem kernel types differ")
    source_axioms = set(standalone.audit_axioms(context.file(source_pf["data"]["log"]), stage.NAME))
    solution_axioms = set(standalone.audit_axioms(context.file(generated_pf["data"]["log"]), "solution"))
    need(source_axioms == set(src["axioms"]) and solution_axioms == set(gen["axioms"])
         and source_axioms == solution_axioms,
         "Exact source/generated theorem axiom logs differ from full CI")
    source_helpers = src["automaticInlineHelpers"]
    generated_helpers = gen["automaticInlineHelpers"]
    need(isinstance(source_helpers, list) and isinstance(generated_helpers, list),
         "Actual inline helper arrays missing")
    for ci in source_helpers:
        full_ci(ci, name=ci["name"], module=stage.MODULE, helper=True)
    for ci in generated_helpers:
        full_ci(ci, name=ci["name"], module=SOLUTION_MODULE, helper=True)
    mapping, paired_helpers = unique_helper_pairing(src, gen, source_helpers, generated_helpers)
    need(src["levelParams"] == gen["levelParams"]
         and rename_expr(src["type"], mapping) == gen["type"]
         and rename_expr(src["value"], mapping) == gen["value"],
         "Full source proof value differs from exact renamed solution")
    need(sorted(mapping.get(ref, ref) for ref in src["valueRefs"]) == gen["valueRefs"],
         "Source/generated proof value references differ after unique actual pairing")
    source_project_refs = {r for ci in [src, *source_helpers] for key in ("typeRefs", "valueRefs")
                           for r in ci[key] if r.startswith("OAI.")}
    generated_project_refs = {r for ci in [gen, *generated_helpers] for key in ("typeRefs", "valueRefs")
                              for r in ci[key] if r.startswith("OAI.")}
    need(source_project_refs <= {ci["name"] for ci in source_helpers}
         and not generated_project_refs,
         "Self-contained determinant proof gained an uncertified project dependency")
    target_bytes = (plan["preamble"] + plan["formal_statement"]).encode("utf-8")
    original = stage.source_unit()
    expected_solution = original.replace(b"theorem determinant_bounds_inconsistent", b"theorem solution", 1)
    solution_bytes = (STAGE / stage.SOLUTION_OUTPUT).read_bytes()
    need((STAGE / stage.SOURCE_OUTPUT).read_bytes() == target_bytes
         and (STAGE / "wire-theorem-source.lean").read_bytes() == target_bytes
         and expected_solution in solution_bytes
         and b"namespace OAI" not in solution_bytes
         and b"namespace PiExponent" not in solution_bytes
         and b"sorry" not in solution_bytes,
         "Compiled target/wire or top-level exact source proof body differs")
    output_paths = [STAGE / x for x in ("source-type.json", "generated-type.json",
                                      "source-proof-references.json", "generated-proof-references.json")]
    report = {"schema_version": 1,
        "artifact_kind": "ap7-determinant-bounds-strict-actual-node-v2-validation",
        "validated": True, "source_name": stage.NAME, "solution_name": "solution",
        "source_module": stage.MODULE, "solution_module": SOLUTION_MODULE,
        "source_commit": stage.SOURCE_COMMIT,
        "source_sha256": stage.sha(stage.SOURCE),
        "source_ast_unit_sha256": stage.sha_bytes(original),
        "stage_manifest_sha256": sha(STAGE / "manifest.json"),
        "stage_preparation_sha256": sha(STAGE / "preparation.json"),
        "wire_theorem_sha256": sha(STAGE / "wire-theorem-source.lean"),
        "source_type_equals_solution_type": True,
        "source_proof_value_equals_renamed_solution": True,
        "top_level_global_theorem_solution": True,
        "typed_snapshots_include_actual_proof_values": True,
        "source_owner": src["owner"], "generated_owner": gen["owner"],
        "source_axioms": sorted(source_axioms), "generated_axioms": sorted(solution_axioms),
        "Std3_only": True, "automatic_inline_helper_pairs": paired_helpers,
        "project_reference_closure": "only uniquely paired actual inline helper CIs",
        "solution_olean": rel(expected_olean), "solution_olean_sha256": sha(expected_olean),
        "preserved_namespaced_stage": plan["preserved_namespaced_stage"],
        "preflights": records,
        "output_json_sha256": {rel(p): sha(p) for p in output_paths},
        "implementation_hashes": {rel(p): sha(p) for p in (
            SELF, OLD_CONSUMER, Path(old_stage.__file__), Path(stage.__file__), Path(context.__file__),
            Path(kernel.__file__), Path(standalone.__file__), Path(runner.__file__))},
        "consumer_provenance": {"active_consumer": rel(SELF),
            "active_consumer_sha256": sha(SELF),
            "original_consumer": rel(OLD_CONSUMER),
            "original_consumer_sha256": sha(OLD_CONSUMER)},
        "max_file_seconds": max(pf["data"]["seconds"] for pf in records.values()),
        "submission_ready": False, "proposal_status": "Draft",
        "Lean_started_by_consumer": False, "API_used": False}
    raw = (json.dumps(report, ensure_ascii=False, indent=2) + "\n").encode("utf-8")
    if write:
        if CERT.exists():
            need(CERT.read_bytes() == raw, "Existing strict node certificate differs; refusing overwrite")
        else:
            CERT.write_bytes(raw)
    else:
        need(CERT.is_file() and CERT.read_bytes() == raw,
             "Strict node certificate differs from exact evidence replay")
    return report


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--certify-existing", action="store_true")
    modes.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    report = validate(write=args.certify_existing)
    print(json.dumps({"validated": True, "certificate": rel(CERT),
                      "certificate_sha256": sha(CERT),
                      "helper_count": len(report["automatic_inline_helper_pairs"]),
                      "max_file_seconds": report["max_file_seconds"],
                      "Lean_started": False, "API_used": False}, indent=2))
