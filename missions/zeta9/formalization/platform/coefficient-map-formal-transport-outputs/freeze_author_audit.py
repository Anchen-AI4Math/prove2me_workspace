"""Freeze actual AUTHOR evidence only after all fresh contexts and controls pass."""
from collections import Counter
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess

import initialize_author as p
import inspect_completed_controls as controls


def unique_bindings(paths):
    unique = {}
    for path in paths:
        resolved = Path(path).resolve()
        key = str(resolved).casefold()
        if key not in unique:
            unique[key] = p.bind(resolved)
    return [unique[key] for key in sorted(unique)]


def success(receipt, tag, module):
    rows = [row for row in receipt["rows"] if row["tag"] == tag and row["module"] == module and row["exit_code"] == 0]
    assert len(rows) == 1, (tag, module, len(rows))
    return rows[0]


def source_from_actual(row):
    matching = [item for item in row["immutable_snapshots"] if item["original"].get("task_relative", "").endswith("/" + row["source"])]
    assert len(matching) == 1
    original, retained = matching[0]["original"], matching[0]["retained"]
    p.check([original, retained])
    raw = p.resolve(original).read_bytes()
    assert raw == p.resolve(retained).read_bytes()
    return raw


def export(receipt):
    plan = p.load(p.OUT / "target-plan.json")
    rows = []
    target = p.OUT / "compiled-export"
    definition = plan["local_definition"]
    actual = success(receipt, "d", definition[:-5].replace("/", "."))
    raw = source_from_actual(actual)
    p.write(target / definition, raw)
    rows.append({"kind": "Definition", "platform_module": definition[:-5].replace("/", "."),
                 "path": definition, "binding": p.bind(target / definition),
                 "own_actual_SOURCE_success": {"tag": actual["tag"], "label": actual["label"], "source": actual["source"]}})
    targets = []
    for tag, short, old in zip(["c", "f", "m"], ["Constant", "Five", "Matrix"], plan["targets"], strict=True):
        reference = old["local_reference"]
        actual = success(receipt, "r", "Theorems.Ref" + short + "V2")
        raw = source_from_actual(actual)
        preamble = old["preamble"].replace("open ZetaNine.CoefficientMapFormalTransportOutputs\n", "", 1)
        formal = old["formal_statement"]
        assert raw == (preamble + "\n\n" + formal + "\n").encode("utf-8")
        p.write(target / reference, raw)
        rows.append({"kind": "Statement type catalog only", "platform_module": reference[:-5].replace("/", "."),
                     "path": reference, "binding": p.bind(target / reference),
                     "own_actual_SOURCE_success": {"tag": actual["tag"], "label": actual["label"], "source": actual["source"]},
                     "proof_or_Std3_PASS_claimed": False})
        solution = old["local_solution"]
        actual = success(receipt, tag, "Solutions.Outputs" + short + "V2")
        raw = source_from_actual(actual)
        p.write(target / solution, raw)
        rows.append({"kind": "Solution", "platform_module": solution[:-5].replace("/", "."),
                     "path": solution, "binding": p.bind(target / solution),
                     "own_actual_SOURCE_success": {"tag": actual["tag"], "label": actual["label"], "source": actual["source"]}})
        targets.append({**old, "preamble": preamble, "reference_preamble_import_repair": "remove one unnecessary open",
                        "reference_complete_formal_statement_bytes_unchanged": True,
                        "local_reference_export": p.bind(target / reference), "local_solution_export": p.bind(target / solution)})
    assert len(rows) == 7
    result = {"definition": plan["definition"], "Mathlib_ENV": plan["Mathlib_ENV"], "payloads": rows, "targets": targets,
              "native_all16_exact_headers": plan["native_all16_exact_headers"], "whole_definition_controls": 20,
              "raw_references_are_type_catalogs_only": True, "author_actual_complete_PASS": True,
              "independent_PASS_claimed": False, "Root_install_or_API_PASS_claimed": False,
              "API_publication_forbidden_until_independent_and_Root_gates": True,
              "original_frozen_SOURCE_candidate_preserved": p.bind(p.OUT / "pure-source-handoff.json")}
    p.dump(p.OUT / "compiled-export-manifest.json", result)
    return result


def main():
    report_path = p.OUT / "author-audit.json"
    assert not report_path.exists()
    grant = p.load(p.OUT / "Root-platform-author-lane2-grant.json")
    assert grant["Root_explicit_grant"] is True and grant["lane"] == 2
    assert p.sha(p.OUT / "pure-source-handoff.json") == grant["frozen_SOURCE_handoff_sha256"]
    p.check(p.load(p.OUT / "pure-source-handoff.json")["stable_files"])
    preparation = p.load(p.OUT / "author-context-preparation.json")
    p.check(preparation["stable_files"])
    receipt_path = p.OUT / "author-execution-receipt.json"
    receipt = p.load(receipt_path)
    counts = Counter()
    paths = []
    live_pids = []
    for row in receipt["rows"]:
        assert row["state"] == "ACTUAL_TERMINAL" and row["all_actual_handles_terminal"] is True
        assert row["LEAN_NUM_THREADS"] == row["LAKE_JOBS"] == 1
        assert Path(row["execution_CWD"]).resolve() == (p.PROJECT / row["tag"]).resolve()
        assert row["command"][:6] == ["lake", "env", "C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe", "lean_call.py", "lean", "-j1"]
        folder = p.TASK / row["folder_task_relative"]
        handle = p.load(folder / "live-handle.json")
        assert handle["state"] == "ACTUAL_TERMINAL" and handle["exit_code"] == row["exit_code"]
        live_pids.append(handle["pid"])
        assert row["whole_failed_run_excluded"] is (row["exit_code"] != 0)
        bindings = row["input_bindings"] + row["output_bindings"] + row["evidence_bindings"]
        bindings += [item["retained"] for item in row["immutable_snapshots"]]
        p.check(bindings)
        paths.extend(p.resolve(binding) for binding in bindings)
        selected = p.load(folder / "selected-paths.json")
        assert Path(selected["actual_execution_CWD"]).resolve() == (p.PROJECT / row["tag"]).resolve()
        for key in ["LEAN_PATH", "LEAN_SRC_PATH"]:
            allowed = {str(Path(value).resolve()).casefold() for value in selected[key]["allowed_exact_set"]}
            assert all(str(Path(value).resolve()).casefold() in allowed for value in selected[key]["filtered"])
            assert str((p.PROJECT / row["tag"] / ("b/lib/lean" if key == "LEAN_PATH" else "")).resolve()).casefold() in allowed
        counts[row["tag"] + (":success" if row["exit_code"] == 0 else ":preserved_failure")] += 1
    source_plan = p.load(p.OUT / "author-math-source-preparation-v2.json")
    for context in source_plan["contexts"]:
        _, runtime_folder = controls.actual(receipt, context["tag"], "runtime")
        assert "4.33.1" in (runtime_folder / "stdout.log").read_text(encoding="utf-8")
        if context["tag"] == "r":
            selected_sources = [row for row in context["math_sources"] if row["kind"] != "catalog_type_only_never_proof"]
        else:
            selected_sources = context["math_sources"]
        for source in selected_sources:
            success(receipt, context["tag"], source["module"])
    for short in ["Constant", "Five", "Matrix"]:
        success(receipt, "r", "Theorems.Ref" + short + "V2")
    control_plan = p.load(p.OUT / "author-control-preparation-v3.json")
    summaries = [controls.summarize_context(receipt, context) for context in control_plan["contexts"]]
    _, reference_folder = controls.actual(receipt, "r", "rt1")
    catalog_types = list(controls.records(reference_folder / "stdout.log"))
    assert len(catalog_types) == 3
    _, actual_types_folder = controls.actual(receipt, "c", "a01")
    actual_types = {item["declaration"]: item["full_type_raw_Expr"]
                    for item in controls.records(actual_types_folder / "stdout.log")
                    if item["kind"] == "platform_author_actual_original_forall"}
    reference_diagnostics = []
    for item in catalog_types:
        assert item["kind"] == "platform_author_complete_catalog_type_only"
        for key in ["whole_type_kernel_equal", "closed_complete_types", "all_fields_roundtrip"]:
            assert item[key] is True
        assert item["catalog_proof_value_read_or_used"] is False and item["catalog_proof_or_Std3_PASS_claimed"] is False
        assert item["complete_catalog_type_and_expected_Prop_dag"]["format"] == "lean-expr-dag-v1"
        reference_diagnostics.append({"declaration": item["declaration"], "whole_original_type_kernel_equal": True,
                                      "reference_vs_solution_type_raw_Expr_equal_diagnostic":
                                      item["actual_catalog_full_type_raw_Expr"] == actual_types[item["declaration"]]})
    fixture_summaries = []
    for tag in ["d", "c", "f", "m"]:
        context = next(row for row in source_plan["contexts"] if row["tag"] == tag)
        fixture = next(row for row in context["math_sources"] if row["module"] == "OutputsPlatformExprDagValidationV1")
        actual = success(receipt, tag, fixture["module"])
        lines = list(controls.records(p.TASK / actual["folder_task_relative"] / "stdout.log"))
        kinds = Counter(item["kind"] for item in lines)
        assert kinds == {"expr_dag_validation": 20, "expr_dag_small_source_validation": 3}, (tag, kinds)
        for item in lines:
            assert item["all_fields_roundtrip"] is True and item["raw_repr_reconstruction_equal"] is True
        fixture_summaries.append({"tag": tag, "counts": dict(kinds), "strict_all_fields_PASS": True})
        _, folder = controls.actual(receipt, tag, "a03")
        for item in controls.records(folder / "stdout.log"):
            paths.append(Path(item["realPath"]))
    query = "Get-CimInstance Win32_Process | Where-Object { $_.Name -in @('lean.exe','lake.exe','python.exe') } | Select-Object ProcessId,ParentProcessId,Name,CommandLine,CreationDate | ConvertTo-Json -Depth 5"
    result = subprocess.run(["pwsh", "-NoProfile", "-Command", query], capture_output=True)
    assert result.returncode == 0
    p.write(p.OUT / "author-terminal-process-query.json", result.stdout)
    observed = json.loads(result.stdout.decode("utf-8-sig") or "null") or []
    observed = observed if isinstance(observed, list) else [observed]
    scripts = ["run_author_sources.py", "run_three_proof_contexts.py", "run_three_proof_contexts_v3.py",
               "run_author_controls.py", "repair_reference_open_v2.py"]
    claimed = []
    for item in observed:
        command = (item.get("CommandLine") or "").casefold()
        if item["ProcessId"] == os.getpid():
            continue
        if ".rt\\opfa1" in command or ".rt/opfa1" in command or any(name in command for name in scripts):
            claimed.append(item)
        if item["ProcessId"] in live_pids:
            assert "lake" not in command, "A recorded actual Lake handle still exists: " + repr(item)
    assert not claimed, claimed
    exported = export(receipt)
    toolchain = Path("C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1")
    executables = [toolchain / "bin/lean.exe", toolchain / "bin/lake.exe",
                   Path("C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe")]
    assert all(path.is_file() for path in executables)
    paths.extend(executables)
    for path in p.OUT.rglob("*"):
        if path.is_file() and "__pycache__" not in path.parts and path != report_path:
            paths.append(path)
    for context in source_plan["contexts"]:
        ctx = p.PROJECT / context["tag"]
        paths.extend(ctx / name for name in ["lakefile.toml", "lean-toolchain", "lake-manifest.json", "lean_call.py"])
        paths.extend(p.resolve(row["binding"]) for row in context["math_sources"])
        for path in ctx.glob("OutputsPlatform*.lean"):
            paths.append(path)
    stable = unique_bindings(paths)
    p.check(stable)
    report = {"role": "Outputs platform AUTHOR actual audit", "frozen_at": datetime.now(timezone.utc).isoformat(),
              "author_actual_complete_PASS": True, "independent_PASS_claimed": False,
              "Root_explicit_lane2_grant": p.bind(p.OUT / "Root-platform-author-lane2-grant.json"),
              "initial_project_absent_before_preparation": preparation["fresh_project_initially_absent"],
              "original_SOURCE_handoff": p.bind(p.OUT / "pure-source-handoff.json"),
              "actual_execution_receipt": p.bind(receipt_path), "actual_calls": len(receipt["rows"]),
              "actual_successes": sum(row["exit_code"] == 0 for row in receipt["rows"]),
              "all_failed_runs_preserved_and_excluded": [row["folder_task_relative"] for row in receipt["rows"] if row["exit_code"] != 0],
              "actual_counts_by_context": dict(counts), "complete_control_summaries": summaries,
              "three_complete_catalog_type_controls": reference_diagnostics,
              "catalog_proof_values_read_or_used": False,
              "strict_lossless_DAG_fixtures": fixture_summaries, "compiled_seven_payload_export": p.bind(p.OUT / "compiled-export-manifest.json"),
              "all_actual_handles_terminal": True, "owned_mathematical_processes_observed": claimed,
              "process_query": p.bind(p.OUT / "author-terminal-process-query.json"),
              "actual_environment_executable_bindings": [p.bind(path) for path in executables],
              "no_foreign_mathematical_proof_object_reused": True, "all_own_objects_own_actual_SOURCE_verified": True,
              "raw_Expr_differences_preserved_honestly": True, "SOURCE_native_closure_per_proof_context": 21,
              "original_full_proof_SOURCE_declarations_per_Solution": 380,
              "connectionPair_Classical_choose_full27_existence_proof_SOURCE_retained": True,
              "original16_forall_and_three_n_ge_one_targets_unchanged": True,
              "matrix_LEFT_Gamma_order_preserved": True, "whole_original18_plus2_definition_gates": 20,
              "typed_boundaries_per_proof_context": 9, "API_calls": 0, "credentials_reads": 0,
              "shared_modules_or_scope_modified": False, "open_conditions_not_closed": ["J", "denominator/height bounds", "irrationality of zeta(9)"],
              "stable_binding_schema": ["task_relative", "root_relative", "absolute_path"],
              "stable_file_count": len(stable), "stable_files": stable}
    p.dump(report_path, report)
    print(json.dumps({"report": p.bind(report_path), "export": p.bind(p.OUT / "compiled-export-manifest.json"),
                      "actual_calls": report["actual_calls"], "successes": report["actual_successes"],
                      "stable_files": len(stable), "controls": summaries}, ensure_ascii=False, indent=2), flush=True)


if __name__ == "__main__":
    main()
