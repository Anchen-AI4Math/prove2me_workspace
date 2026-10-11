"""Freeze actual author evidence only after all complete SOURCE and controls passed.

This script runs no Lean and makes no independent-review or platform claim.
It retains all historical failures and verifies every recorded byte binding.
"""
from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
OUT = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"
PROJECT = OUT / ".rt/afb1"
EXPORT = OUT / "native-author-export"
STD3 = {"propext", "Classical.choice", "Quot.sound"}
PLAN_SHA = "f2b45465770375bf49131450fa3d72b3d9646fd4f940bf17199bbc42ee317a94"
CONTROLS_SHA = "f916fd9c1e7bdfa4258d008823aea1ae34a07a470a544f966a53d3e0e6daef19"
CONTROL_MODULES = ("AFTypes", "AFKernel", "AFBoundary", "AFResolver")
DAG_MODULES = ("AFExprDag", "AFExprDagValidation")


def load(path: Path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def binding(path: Path):
    data = path.read_bytes()
    base = TASK if path.is_relative_to(TASK) else WORKSPACE
    return {"task_relative" if base == TASK else "root_relative": path.relative_to(base).as_posix(),
            "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def path_of(row):
    return (TASK if "task_relative" in row else WORKSPACE) / row.get("task_relative", row.get("root_relative"))


def verify(row):
    actual = binding(path_of(row))
    assert actual == row, (row, actual)


def dump_new(path: Path, value):
    assert not path.exists(), "Frozen evidence must never be overwritten: " + str(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def prefixes(text):
    return {m.group(1): text[m.start():text.index(":=", m.end()) + 2]
            for m in re.finditer(r"(?m)^theorem (\w+)", text)}


def definitions(text):
    return {m.group(1): m.group(0).strip() for m in re.finditer(r"(?ms)^def (\w+)\b.*?(?=\n\n)", text)}


def copy_exact(source: Path, target: Path):
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        assert target.read_bytes() == source.read_bytes(), target
    else:
        target.write_bytes(source.read_bytes())


def af_records(row):
    data = path_of(row["stdout"]).read_text(encoding="utf-8")
    return [json.loads(line[len("AF_RECORD|"):]) for line in data.splitlines()
            if line.startswith("AF_RECORD|")]


def record_values(records):
    for record in records:
        for key in ("axioms", "actual_axioms", "expected_axioms"):
            if key in record:
                assert set(record[key]) <= STD3, record
        if "value_type_isDefEq" in record:
            assert record["value_type_isDefEq"] is True and record["value_raw"] is not None, record
        for key in ("type_isDefEq", "actual_value_typed", "expected_value_typed"):
            if key in record:
                assert record[key] is True, record
        if "value_raw_format" in record:
            assert record["value_raw_format"] == "lossless lean-expr-dag-v1; full type_root and value_root"
            payload = json.loads(record["value_raw"])
            assert payload["format"] == "lean-expr-dag-v1"
            assert payload["nodes"] and 0 <= payload["type_root"] < len(payload["nodes"])
            assert 0 <= payload["value_root"] < len(payload["nodes"])
            for key in ("all_fields_type_Expr_equal", "all_fields_value_Expr_equal", "full_type_kernel_equal", "full_value_kernel_equal"):
                assert record[key] is True, record


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    assert binding(OUT / "native-inputs-layout-v2-audit.json")["sha256"] == PLAN_SHA
    assert binding(OUT / "controls-preparation-v1.json")["sha256"] == CONTROLS_SHA
    plan = load(OUT / "native-inputs-layout-v2-audit.json")
    control_plan = load(OUT / "controls-preparation-v1.json")
    grant = load(OUT / "Root-author-lane1-grant.json")
    assert grant["Root_explicit_grant"] and grant["lane"] == 1
    assert grant["owner"] == "factorial_bound_author_1007"
    assert grant["private_project"] == PROJECT.relative_to(TASK).as_posix()
    receipt_path = OUT / "author-compile-receipt.json"
    receipt = load(receipt_path)
    calls = receipt["rows"]
    assert [r["index"] for r in calls] == list(range(1, len(calls) + 1))
    assert all(isinstance(r["exit_code"], int) for r in calls)
    binding_count = 0
    for row in calls:
        for key in ("stdout", "stderr", "log", "exit_file", "selected_paths"):
            verify(row[key]); binding_count += 1
        assert int(path_of(row["exit_file"]).read_text()) == row["exit_code"]
        assert row["cwd"] == str(PROJECT)
        assert row["actual_environment"] == {"LEAN_NUM_THREADS": "1", "LAKE_JOBS": "1"}
        assert "-j1" in row["command"] and str(PROJECT / "leaf.py") in row["command"]
        for key in ("input_bindings", "output_bindings"):
            for item in row[key]:
                verify(item); binding_count += 1
        for key in ("retained_inputs", "retained_outputs"):
            for item in row[key]:
                verify(item["original_binding"]); verify(item["snapshot_binding"]); binding_count += 2
                assert item["original_binding"]["bytes"] == item["snapshot_binding"]["bytes"]
                assert item["original_binding"]["sha256"] == item["snapshot_binding"]["sha256"]
        selected = load(path_of(row["selected_paths"]))
        for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
            for raw in selected[key]["filtered"]:
                p = Path(raw).resolve()
                assert p.is_relative_to(PROJECT.resolve()) or p.is_relative_to((WORKSPACE / ".lake/packages").resolve())
        assert row["failed_attempt_retained"] == (row["exit_code"] != 0)
    last = {}
    for row in calls:
        if row["exit_code"] == 0 and row["module"]:
            last[row["module"]] = row
    modules = [r["module_name"] for r in plan["actual_source_copy_order"]]
    assert len(modules) == len(set(modules)) == 11
    assert set(modules) | set(CONTROL_MODULES) | set(DAG_MODULES) <= set(last)
    fixture_data = path_of(last["AFExprDagValidation"]["stdout"]).read_text(encoding="utf-8")
    fixture_records = [json.loads(line) for line in fixture_data.splitlines() if line.startswith('{')]
    fixtures = [r for r in fixture_records if r["kind"] == "expr_dag_validation"]
    small = [r for r in fixture_records if r["kind"] == "expr_dag_small_source_validation"]
    assert len(fixtures) == 20 and {r["fixture_index"] for r in fixtures} == set(range(20))
    assert len(small) == 3
    assert all(r["all_fields_roundtrip"] and r["raw_repr_reconstruction_equal"] for r in fixture_records)
    exports = []
    source_gates = []
    theorem_count = definition_count = 0
    for original in plan["actual_source_copy_order"]:
        module = original["module_name"]
        row = last[module]
        source_arg = Path(row["command"][-1])
        matching = [b for b in row["input_bindings"] if path_of(b) == source_arg]
        assert len(matching) == 1
        verify(matching[0])
        source = source_arg.read_text(encoding="utf-8")
        verify(original["source"])
        original_source = path_of(original["source"]).read_text(encoding="utf-8")
        assert prefixes(original_source) == prefixes(source), module
        assert definitions(original_source) == definitions(source), module
        if module.startswith("Analytic") and module not in ("AnalyticPhaseUpperBound",):
            theorem_count += len(prefixes(source))
            definition_count += len(definitions(source))
        code = re.sub(r"/-.*?-/", "", source, flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|partial)\b", code), module
        export = EXPORT / "src" / (module.replace(".", "/") + ".lean")
        copy_exact(source_arg, export)
        exports.append({"module": module, "actual_success_call": row["index"],
                        "source": matching[0], "complete_source_export": binding(export)})
        source_gates.append({"module": module, "actual_call": row["index"],
                             "all_original_complete_theorem_prefixes_exact": True,
                             "all_original_whole_definitions_exact": True,
                             "original_theorems": len(prefixes(original_source)),
                             "original_definitions": len(definitions(original_source))})
    assert theorem_count == 70 and definition_count == 13, (theorem_count, definition_count)
    all_records = {}
    for module in CONTROL_MODULES:
        row = last[module]
        records = af_records(row)
        assert records, module
        record_values(records)
        all_records[module] = records
        source = Path(row["command"][-1])
        export = EXPORT / "controls" / (module + ".lean")
        copy_exact(source, export)
        exports.append({"module": module, "actual_success_call": row["index"],
                        "source": binding(source), "complete_source_export": binding(export)})
    for module in DAG_MODULES:
        row = last[module]
        source = Path(row["command"][-1])
        export = EXPORT / "controls" / (module + ".lean")
        copy_exact(source, export)
        exports.append({"module": module, "actual_success_call": row["index"],
                        "source": binding(source), "complete_source_export": binding(export)})
    types = all_records["AFTypes"]
    kernels = all_records["AFKernel"]
    boundaries = all_records["AFBoundary"]
    resolvers = all_records["AFResolver"]
    theorems = [r for r in types if r["kind"] == "theorem"]
    defs = [r for r in types if r["kind"] == "definition"]
    assert len(theorems) == 70 and {r["name"] for r in theorems} == set(control_plan["complete_theorem_names"])
    assert len(defs) == 29 and {r["name"] for r in defs} == set(control_plan["whole_definition_names"])
    tc = [r for r in kernels if r["kind"] == "theorem_compare"]
    dc = [r for r in kernels if r["kind"] == "definition_compare"]
    rfls = [r for r in kernels if r["kind"] == "definition_rfl"]
    expected_values = [r for r in kernels if r["kind"] == "expected_theorem_value"]
    helpers = [r for r in kernels if r["kind"] == "definition_helper_compare"]
    assert len(tc) == len(expected_values) == 70 and len(dc) == len(rfls) == 29
    assert {r["actual"] for r in tc} == set(control_plan["complete_theorem_names"])
    assert {r["actual"] for r in dc} == set(control_plan["whole_definition_names"])
    for row in dc:
        assert row["value_isDefEq"] and row["normalized_value_isDefEq"]
    for row in helpers:
        assert row["type_exprEqual"] and row["value_exprEqual"] and row["value_isDefEq"]
    inventories = [r for r in types if r["kind"] == "module_inventory"]
    assert len(inventories) == 11 and {r["module"] for r in inventories} == set(modules)
    declarations = [r for r in types if r["kind"] == "module_declaration"]
    extras = [r for r in types if r["kind"] == "module_extra"]
    declared_names = [n for r in inventories for n in r["constant_names"]]
    assert Counter(r["name"] for r in declarations) == Counter(declared_names)
    extra_names = set(n for r in inventories for n in r["extra_names"])
    visible_extras = {r["name"] for r in extras}
    assert visible_extras <= extra_names
    assert len(boundaries) == 15 and all(r["kind"] == "typed_boundary" for r in boundaries)
    assert {r["name"] for r in boundaries} == {"AFBoundary." + n for n in control_plan["typed_boundary_names"]}
    assert all(r["kind"] == "actual_module_resolver" for r in resolvers)
    assert len({r["module"] for r in resolvers}) == len(resolvers)
    resolver_by_module = {r["module"]: r for r in resolvers}
    own_resolvers = []
    resolver_classifications = Counter()
    for row in resolvers:
        canonical = Path(row["canonical_olean"]).resolve()
        assert canonical.exists()
        if canonical.is_relative_to(PROJECT.resolve()):
            classification = "own_fresh_SOURCE_objects"
        elif canonical.is_relative_to((WORKSPACE / ".lake/packages").resolve()):
            classification = "pinned_packages"
        else:
            assert ".elan/toolchains/leanprover--lean4---v4.33.1/lib/lean/" in canonical.as_posix(), row
            classification = "intrinsic_Lean_4.33.1"
        resolver_classifications[classification] += 1
        if row["module"] in modules:
            expected = (PROJECT / "b/lib/lean" / (row["module"].replace(".", "/") + ".olean")).resolve()
            assert canonical == expected and classification == "own_fresh_SOURCE_objects", row
            own_resolvers.append(row)
    assert len(own_resolvers) == 11
    command = "$project = '" + str(PROJECT).replace("'", "''") + "'; @(Get-CimInstance Win32_Process | Where-Object { $_.Name -in @('lean.exe','lake.exe','python.exe') -and $_.CommandLine -and $_.CommandLine.Contains($project) } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
    result = subprocess.run(["powershell", "-NoProfile", "-Command", command], capture_output=True)
    assert result.returncode == 0, result.stderr
    live = json.loads(result.stdout.decode("utf-8-sig") or "[]")
    assert not live, live
    evidence = {"status": "AUTHOR_FULL_SOURCE_AND_CONTROLS_PASS_INDEPENDENT_REVIEW_PENDING",
                "scope": "Actual weighted uniform analytic upper bound only; integer preimage/height, J, exact f-star limit, and irrationality remain open",
                "role": "author", "lane": 1, "private_project": PROJECT.relative_to(TASK).as_posix(),
                "independent_review_pass": False, "platform_uploaded": False,
                "author_calls": len(calls), "author_success_calls": sum(r["exit_code"] == 0 for r in calls),
                "historical_failure_calls_preserved": [r["index"] for r in calls if r["exit_code"] != 0],
                "all_actual_handles_terminal": True, "actual_own_WMI_live_processes": live,
                "own_WMI_command": command, "full_recorded_binding_rehash_count": binding_count,
                "new_complete_theorems": 70, "new_complete_definitions": 13,
                "expected_complete_types": len(tc), "whole_definition_type_value_controls": len(dc),
                "lossless_DAG_constructor_and_payload_fixtures": len(fixtures),
                "lossless_DAG_small_source_raw_tree_reconstruction_controls": len(small),
                "lossless_DAG_core_and_validation_actual_calls": {m: last[m]["index"] for m in DAG_MODULES},
                "whole_function_rfl_controls": len(rfls), "typed_boundary_controls": len(boundaries),
                "paired_proposition_compiler_helpers": len(helpers), "all_actual_generated_and_extra_inventory": inventories,
                "all_module_declaration_records": len(declarations), "all_module_visible_extra_records": len(extras),
                "inventoried_extras_without_environment_declarations": sorted(extra_names - visible_extras),
                "raw_Expr_equal_false_types_retained": [r["actual"] for r in tc + dc if not r["type_exprEqual"]],
                "raw_Expr_equal_false_definition_values_retained": [r["actual"] for r in dc if not r["value_exprEqual"]],
                "normalized_Expr_equal_false_definition_values_retained": [r["actual"] for r in dc if not r["normalized_value_exprEqual"]],
                "all_isDefEq_and_actual_inferType_controls_pass": True, "all_axioms_within_Std3": True,
                "normalization_policy": "Only full-expression-paired proposition-valued own compiler helpers expanded; raw values retained; no binder or metadata erasure",
                "actual_resolver_records": len(resolvers), "actual_resolver_classifications": dict(resolver_classifications),
                "all_11_own_actual_resolvers": own_resolvers, "foreign_math_objects_borrowed": False,
                "root_proof_object_fallback": False, "source_statement_definition_gates": source_gates,
                "all_complete_exports": exports, "actual_calls_receipt": binding(receipt_path),
                "frozen_original_layout": binding(OUT / "native-inputs-layout-v2-audit.json"),
                "frozen_original_controls": binding(OUT / "controls-preparation-v1.json"),
                "actual_pass_control_calls": {m: last[m]["index"] for m in CONTROL_MODULES},
                "freeze_script": binding(Path(__file__))}
    for module, records in all_records.items():
        target = OUT / "author-full-records" / (module + ".jsonl")
        assert not target.exists()
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in records), encoding="utf-8")
        evidence.setdefault("full_control_record_files", []).append(binding(target))
    fixture_target = OUT / "author-full-records/AFExprDagValidation.json"
    dump_new(fixture_target, fixture_records)
    evidence["full_lossless_DAG_validation_records"] = binding(fixture_target)
    frozen_calls = OUT / "author-complete-calls-frozen.json"
    dump_new(frozen_calls, receipt)
    evidence["all_actual_calls_frozen"] = binding(frozen_calls)
    dump_new(OUT / "author-complete-audit.json", evidence)
    print(json.dumps({"audit": binding(OUT / "author-complete-audit.json"),
                      "status": evidence["status"], "calls": len(calls), "bindings": binding_count,
                      "complete_theorems": 70, "complete_definitions": 13,
                      "records": {m: len(rs) for m, rs in all_records.items()}}, ensure_ascii=False))


if __name__ == "__main__":
    main()
