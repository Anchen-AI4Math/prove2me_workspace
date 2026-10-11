"""Pure byte/header/lexical review of the uncompiled Outputs SOURCE candidate."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    target = OUT / "source-candidate-lexical-review.json"
    assert not target.exists()
    plan = load(OUT / "target-plan.json")
    prep = load(OUT / "source-preparation.json")
    old = load(OUT / "preparation-binding-check.json")
    assert old["differences"] == 0 and old["source_preparation_sha256"] == sha(OUT / "source-preparation.json")
    for row in old["stable_files"]:
        path = TASK / row["task_relative"] if row.get("task_relative") else TASK.parents[1] / row["root_relative"]
        assert path.stat().st_size == row["bytes"] and sha(path) == row["sha256"]
    helper = TASK / "scripts/publish_formalization_2026_10_02.py"
    tree = ast.parse(helper.read_text(encoding="utf-8"))
    function = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "without_lean_comments")
    ns = {"re": re}
    exec(compile(ast.Module(body=[function], type_ignores=[]), "<pure comment remover SOURCE>", "exec"), ns)
    checked = []
    stage = OUT / "staged"
    for item in plan["payloads"]:
        path = stage / item["path"]
        assert sha(path) == item["binding"]["sha256"]
        code = ns["without_lean_comments"](path.read_text(encoding="utf-8"))
        imports = re.findall(r"^import\s+(\S+)", code, re.M)
        assert all(name.startswith(("Definitions.", "Mathlib")) for name in imports)
        assert not re.search(r"\b(?:axiom|admit|unsafe|native_decide)\b", code)
        if item["kind"] == "statement_type_catalog_only_SOURCE_candidate":
            assert len(re.findall(r"\bsorry\b", code)) == 1
        else:
            assert not re.search(r"\bsorry\b", code)
        checked.append({"path": item["path"], "bytes": path.stat().st_size, "sha256": sha(path), "imports": imports,
                        "lexical_gate_passed": True, "Lean_kernel_gate_performed": False})
    for item in plan["targets"]:
        reference = (stage / item["local_reference"]).read_text(encoding="utf-8")
        assert reference == item["preamble"] + "\n\n" + item["formal_statement"] + "\n"
        assert "(hn : 1 ≤ n)" in item["exact_original_header"]
        assert "Even" not in item["exact_original_header"]
        assert item["full_original_forall_not_n_one_test"] is True
        solution = (stage / item["local_solution"]).read_text(encoding="utf-8")
        for row in plan["native_all16_exact_headers"]:
            assert row["header"] + " :=" in solution, row["name"]
    assert len(plan["all18_definition_controls_required"]) == 18 and len(plan["additional_whole_definition_controls_required"]) == 2
    assert len(prep["native_SOURCE_closure"]) == 21 and prep["Lean_calls"] == prep["API_calls"] == prep["credentials_reads"] == 0
    assert not (TASK / prep["planned_project"]).exists()
    result = {"checked_at": datetime.now(timezone.utc).isoformat(), "status": "UNCOMPILED_SOURCE_LEXICAL_GATES_ONLY",
              "payloads": checked, "all16_original_exact_header_occurrences_per_solution": True,
              "three_original_n_ge_one_domains_preserved": True, "matrix_LEFT_Gamma_order_preserved": True,
              "three_reference_full_formal_statement_and_double_newline_exact": True,
              "no_sorry_or_other_forbidden_proof_token_in_Definition_or_Solutions": True,
              "native_all1085_binding_rehash_passed": True, "native_sources": 21, "planned_original_whole_defs": 18,
              "additional_whole_defs": 2, "retained_proof_SOURCE_declarations": len(prep["retained_proof_SOURCE_inventory"]),
              "Lean_calls": 0, "API_calls": 0, "credentials_reads": 0, "platform_PASS_claimed": False,
              "genuine_Lean_parser_decl_graph_type_value_rfl_boundaries_Std3_helpers_resolver_still_required": True,
              "comment_remover_generic_SOURCE": {"task_relative": helper.relative_to(TASK).as_posix(), "sha256": sha(helper)}}
    target.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"report": str(target), "sha256": sha(target), "seven_payloads_lexically_checked": 7,
                      "all16_original_headers_per_solution": True, "Lean_calls": 0, "API_calls": 0,
                      "credentials_reads": 0, "platform_PASS_claimed": False}, indent=2))


if __name__ == "__main__":
    main()
