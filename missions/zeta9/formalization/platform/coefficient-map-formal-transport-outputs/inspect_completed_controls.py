"""Offline checks of actual control records; never invokes Lean or an API."""
from collections import Counter
import json
from pathlib import Path
import sys

import initialize_author as p

STD3 = {"propext", "Classical.choice", "Quot.sound"}
FULL_GATES = ["closed_complete_type_and_value", "actual_value_inferType_kernel_equal",
              "all_fields_Expr_equal_roundtrip", "type_roundtrip_kernel_equal", "value_roundtrip_kernel_equal"]


def records(path):
    with path.open(encoding="utf-8-sig") as handle:
        for number, line in enumerate(handle, 1):
            if not line.lstrip().startswith("{"):
                continue
            item = json.loads(line)
            assert isinstance(item, dict) and isinstance(item.get("kind"), str), (path, number)
            yield item


def actual(receipt, tag, label):
    matching = [row for row in receipt["rows"] if row["tag"] == tag and row["label"] == label and row["exit_code"] == 0]
    assert len(matching) == 1, (tag, label, len(matching))
    row = matching[0]
    assert row["state"] == "ACTUAL_TERMINAL" and row["all_actual_handles_terminal"] is True
    return row, p.TASK / row["folder_task_relative"]


def full_record(item):
    for key in FULL_GATES:
        assert item.get(key) is True, (item.get("declaration"), key)
    assert set(item["axioms"]) <= STD3
    dag = item["complete_type_and_value_expression_dag"]
    assert dag["format"] == "lean-expr-dag-v1" and dag["nodes"]
    assert 0 <= dag["type_root"] < len(dag["nodes"]) and 0 <= dag["value_root"] < len(dag["nodes"])
    assert item["full_type_raw_Expr"] and item["actual_inferred_type_raw_Expr"]


def summarize_context(receipt, context):
    tag = context["tag"]
    _, folder = actual(receipt, tag, "a01")
    semantic = list(records(folder / "stdout.log"))
    kinds = Counter(item["kind"] for item in semantic)
    expected = {"platform_author_actual_whole_definition": 20, "platform_author_fresh_native_whole_definition": 20,
                "platform_author_full_definition_kernel_comparison": 20, "platform_author_whole_function_rfl": 20}
    if context["proof_context"]:
        expected.update({"platform_author_actual_original_forall": 16, "platform_author_fresh_native_original_forall": 16,
                         "platform_author_complete_forall_kernel_comparison": 17,
                         "platform_author_actual_complete_solution": 1, "platform_author_actual_typed_boundary": 9})
    assert dict(kinds) == expected, (tag, kinds, expected)
    diagnostics = Counter()
    for item in semantic:
        if item["kind"] == "platform_author_full_definition_kernel_comparison":
            assert item["type_kernel_equal"] is True and item["value_kernel_equal"] is True
            for key in ["type_Expr_equal_diagnostic", "value_Expr_equal_diagnostic"]:
                assert isinstance(item[key], bool)
                diagnostics[key + ":" + str(item[key])] += 1
            for key in ["full_actual_type_and_value_dag", "full_expected_type_and_value_dag"]:
                assert item[key]["format"] == "lean-expr-dag-v1"
        elif item["kind"] == "platform_author_complete_forall_kernel_comparison":
            assert item["whole_type_kernel_equal"] is True
            assert item["full_actual_type_raw_Expr"] and item["full_expected_type_raw_Expr"]
            assert isinstance(item["type_Expr_equal_diagnostic"], bool)
            diagnostics["forall_type_Expr_equal_diagnostic:" + str(item["type_Expr_equal_diagnostic"])] += 1
        else:
            full_record(item)
    _, folder = actual(receipt, tag, "a02")
    std_names, value_names, inventory = set(), set(), None
    for item in records(folder / "stdout.log"):
        if item["kind"] == "platform_author_all_actual_declaration_Std3":
            assert item["closed_complete_type"] is True and set(item["axioms"]) <= STD3
            assert item["declaration"] not in std_names
            std_names.add(item["declaration"])
        elif item["kind"] == "platform_author_all_actual_complete_type_and_value":
            full_record(item)
            assert item["declaration"] not in value_names
            value_names.add(item["declaration"])
        else:
            assert item["kind"] == "platform_author_complete_generated_closure_inventory" and inventory is None
            inventory = item
    assert inventory is not None
    assert std_names == value_names == set(inventory["all_declarations"])
    assert len(inventory["all_declarations"]) == len(std_names)
    assert set(inventory["all_generated_helpers"]) <= std_names
    assert len(set(inventory["all_generated_helpers"])) == len(inventory["all_generated_helpers"])
    assert set(inventory["modules"]) == set(context["all_actual_math_modules"])
    _, folder = actual(receipt, tag, "a03")
    imports, own = [], []
    for item in records(folder / "stdout.log"):
        if item["kind"] == "actual_import_origin":
            assert Path(item["chosen"]).resolve() == Path(item["realPath"]).resolve()
            imports.append(item)
        else:
            assert item["kind"] == "actual_own_object_resolution" and item["own_exact"] is True
            assert Path(item["expected"]).resolve() == Path(item["realPath"]).resolve()
            own.append(item)
    assert {item["module"] for item in own} == set(context["actual_own_modules"])
    manifest = p.load(p.PROJECT / tag / "lake-manifest.json")
    stock = [(p.ROOT / ".lake/packages" / item["name"] / ".lake/build/lib/lean").resolve()
             for item in manifest["packages"]]
    intrinsic = Path("C:/Users/anche/.elan/toolchains/leanprover--lean4---v4.33.1/lib/lean").resolve()
    current = (p.PROJECT / tag / "b/lib/lean").resolve()
    source_by_object = {p.resolve(binding).resolve(): row for row in receipt["rows"]
                        if row["tag"] == tag and row["exit_code"] == 0
                        for binding in row["output_bindings"]}
    for item in imports:
        path = Path(item["realPath"]).resolve()
        assert path.is_relative_to(current) or path.is_relative_to(intrinsic) or any(path.is_relative_to(root) for root in stock), path
        if path.is_relative_to(current):
            assert path in source_by_object, "Own object lacks own actual SOURCE success: " + str(path)
    return {"tag": tag, "semantic_counts": dict(kinds), "honest_raw_Expr_diagnostics": dict(diagnostics),
            "full_all_declarations": len(value_names), "full_actual_generated_helpers": len(inventory["all_generated_helpers"]),
            "Std3_all_declarations": len(std_names), "math_modules": len(inventory["modules"]),
            "actual_import_origins": len(imports), "actual_own_object_resolutions": len(own),
            "source_and_value_gates_PASS": True, "own_actual_SOURCE_object_origins_PASS": True}


def main():
    receipt = p.load(p.OUT / "author-execution-receipt.json")
    plan = p.load(p.OUT / "author-control-preparation-v3.json")
    selected = set(sys.argv[1:] or ["d", "c", "f", "m"])
    summaries = [summarize_context(receipt, row) for row in plan["contexts"] if row["tag"] in selected]
    print(json.dumps(summaries, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
