"""Append immutable SOURCE layout/moment inputs; preserve all previous audit bytes."""
from __future__ import annotations

import hashlib
import json
import re
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
OUT = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"
PROJECT = OUT / ".rt/afb1"
PREVIOUS_SHA = "11a993ceb2e4cf626b268c24f2e145678130c3a5f32e41558e70b2684fe9f82a"


def binding(path: Path) -> dict:
    data = path.read_bytes()
    base = TASK if path.is_relative_to(TASK) else WORKSPACE
    return {"task_relative" if base == TASK else "root_relative": path.relative_to(base).as_posix(),
            "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def assert_binding(row: dict) -> None:
    path = (TASK if "task_relative" in row else WORKSPACE) / row.get("task_relative", row.get("root_relative"))
    actual = binding(path)
    assert row["bytes"] == actual["bytes"] and row["sha256"] == actual["sha256"]


def main() -> None:
    previous_path = OUT / "native-inputs-preparation-audit.json"
    assert binding(previous_path)["sha256"] == PREVIOUS_SHA
    previous = json.loads(previous_path.read_text(encoding="utf-8"))
    for row in previous["new_sources"]:
        assert_binding(row)
    for row in previous["source_copies"]:
        assert_binding(row["source"])
        assert_binding(row["private_source_copy"])
    assert_binding(previous["own_object_policy"])
    assert not list(PROJECT.rglob("*.olean")), "No compiler lane has been granted for these inputs."

    native_phase = TASK / "verification/formalization-analytic-phase-upper-bound-2026-10-07/native-export/AnalyticPhase.lean"
    phase_layout_target = PROJECT / "src/missions/zeta9/formalization/AnalyticPhase.lean"
    assert not phase_layout_target.exists()
    phase_layout_target.parent.mkdir(parents=True)
    phase_layout_target.write_bytes(native_phase.read_bytes())
    assert binding(phase_layout_target)["sha256"] == "2b53b56f103bc69322c35d18e120c248cc34402fe831b7be86651f584d3bf4bd"

    additions = []
    new_source_bindings = list(previous["new_sources"])
    for name in ("AnalyticMomentBounds.lean", "AnalyticUniformMomentBound.lean", "AnalyticWeightedBound.lean"):
        source = TASK / "formalization" / name
        text = source.read_text(encoding="utf-8")
        assert not re.search(r"\b(?:sorry|admit|native_decide)\b", text)
        assert not re.search(r"(?m)^\s*axiom\b", text)
        names = re.findall(r"(?m)^theorem\s+(\w+)", text)
        definitions = re.findall(r"(?m)^def\s+(\w+)", text)
        target = PROJECT / "src" / name
        assert not target.exists()
        target.write_bytes(source.read_bytes())
        source_row = {**binding(source), "complete_theorem_bodies": names,
                      "actual_definitions": definitions}
        assert binding(target)["sha256"] == source_row["sha256"]
        new_source_bindings.append(source_row)
        additions.append({"source": binding(source), "private_source_copy": binding(target),
                          "module_name": source.stem, "copied_objects": 0})
    assert sum(len(row["complete_theorem_bodies"]) for row in new_source_bindings) == 70
    assert sum(len(row.get("actual_definitions", [])) for row in new_source_bindings) == 13

    source_rows = []
    for row in previous["source_copies"]:
        if row["module_name"] != "AnalyticPhase":
            source_rows.append(row)
    source_rows.insert(3, {"source": binding(native_phase), "private_source_copy": binding(phase_layout_target),
                           "module_name": "missions.zeta9.formalization.AnalyticPhase", "copied_objects": 0})
    source_rows.extend(additions)
    assert len(source_rows) == 11
    closure_checks = []
    for row in source_rows:
        path = TASK / row["private_source_copy"]["task_relative"]
        imports = re.findall(r"(?m)^import\s+([^\s]+)", path.read_text(encoding="utf-8"))
        for module in imports:
            if module.startswith("Mathlib."):
                closure_checks.append({"module": row["module_name"], "import": module,
                                       "resolver": "pinned Mathlib package runtime only"})
            else:
                source = PROJECT / "src" / (module.replace(".", "/") + ".lean")
                assert source.is_file(), (row["module_name"], module, source)
                closure_checks.append({"module": row["module_name"], "import": module,
                                       "resolver": binding(source)})

    policy_path = PROJECT / "own-object-policy-layout-v2.json"
    policy = {"status": "SOURCE_ONLY_NO_COMPILER_LANE",
              "supersedes_execution_mapping_only": previous["own_object_policy"],
              "old_short_phase_copy_is_inert_frozen_history": True,
              "topological_own_modules": [row["module_name"] for row in source_rows],
              "own_object_directory": (PROJECT / "b/lib/lean").relative_to(TASK).as_posix(),
              "actual_lean_calls": 0, "copied_olean_files": 0,
              "permitted_external_objects": "Pinned Mathlib packages only; no Root or other proof objects.",
              "mandatory_author_checks": ["All 70 complete expected forall types and actual kernel expressions.",
                                          "All reached complete definition types and values, including 13 actual new definitions.",
                                          "Every actual own-module resolver path under afb1 b/lib/lean.",
                                          "Standard three axioms only; preserve all actual failed compiler attempts.",
                                          "Separate fresh independent native SOURCE compilation after author PASS."],
              "lane_gate": "No actual Lean/lake/runtime invocation until explicit Root grant."}
    assert not policy_path.exists()
    policy_path.write_text(json.dumps(policy, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    coefficient_checks = []
    for n in range(1, 11):
        for r in range(5):
            s = 7 * n + 9 - 2 * r
            upper_coeff = {"log_n": 7 * (n + 1) - s - 2 * r,
                           "log_2": n - s, "log_3_over_2": r,
                           "log_9_over_7": 1, "constant": -7 * n + 7}
            certified_coeff = {"log_n": -2, "log_2": -(9 - 2 * r) - 6 * n,
                               "log_3_over_2": r, "log_9_over_7": 1, "constant": 7 - 7 * n}
            assert upper_coeff == certified_coeff
            constant = Fraction(9, 7) * Fraction(3, 2) ** r / Fraction(2) ** (9 - 2 * r)
            assert 0 < constant <= Fraction(729, 224)
            coefficient_checks.append({"n": n, "r": r, "tail_power": s,
                                       "exact_tail_constant": str(constant), "symbolic_log_coefficients": upper_coeff})

    mathlib = WORKSPACE / ".lake/packages/mathlib/Mathlib"
    signatures = []
    for rel, names in (
        ("Algebra/Polynomial/Eval/Degree.lean", ("theorem eval_eq_sum_range'",)),
        ("Topology/Algebra/InfiniteSum/Basic.lean", ("theorem hasProd_prod", "theorem multipliable_prod")),
        ("Topology/Algebra/InfiniteSum/Ring.lean", ("theorem HasSum.mul_left", "theorem tsum_mul_left")),
        ("Topology/Algebra/InfiniteSum/ENNReal.lean", ("theorem Summable.of_nonneg_of_le",)),
        ("Algebra/Order/BigOperators/Group/Finset.lean", ("theorem abs_sum_le_sum_abs",)),
        ("Analysis/SpecialFunctions/Log/Basic.lean", ("theorem tendsto_pow_log_div_mul_add_atTop",)),
    ):
        path = mathlib / rel
        text = path.read_text(encoding="utf-8")
        assert all(name in text for name in names)
        signatures.append({**binding(path), "actual_signature_sources": list(names)})

    report = {"schema_version": 1, "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
              "status": "UNCOMPILED_FULL_ACTUAL_WEIGHTED_A_SOURCE_CHAIN",
              "actual_lean_calls": 0, "actual_kernel_checks": 0, "actual_api_calls": 0, "credential_reads": 0,
              "new_complete_theorem_bodies": 70, "new_actual_definitions": 13,
              "previous_frozen_audit": binding(previous_path), "new_sources": new_source_bindings,
              "actual_source_copy_order": source_rows, "append_only_added_source_copies": additions,
              "phase_fullpath_layout_copy": binding(phase_layout_target),
              "inert_preserved_short_phase_copy": binding(PROJECT / "src/AnalyticPhase.lean"),
              "own_object_policy_layout_v2": binding(policy_path), "pure_local_import_closure": closure_checks,
              "copied_olean_files": 0, "source_layout_checks_are_not_runtime_resolver_checks": True,
              "exact_symbolic_log_boundary_checks": coefficient_checks,
              "finite_checks_are_not_universal_kernel_proofs": True,
              "mathlib_signature_bindings": signatures,
              "mathematical_handoff_delta": binding(TASK / "research/analytic-weighted-uniform-source-delta-2026-10-07.md"),
              "source_final_endpoint": "ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one",
              "final_endpoint_inputs": ["n >= 1", "W : rational polynomial, natDegree <= 4"],
              "final_endpoint_no_assumed_bounds": True,
              "not_yet_verified_or_published": True}
    report_path = OUT / "native-inputs-layout-v2-audit.json"
    assert not report_path.exists()
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "theorems": 70, "definitions": 13,
                      "compile_own_modules": len(source_rows), "copied_olean_files": 0,
                      "audit": binding(report_path)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
