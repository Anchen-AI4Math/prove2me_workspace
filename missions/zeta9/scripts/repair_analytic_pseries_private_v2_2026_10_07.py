"""Private-only repairs for actual p-series elaboration errors, unchanged full types."""
import hashlib
import json
import re
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
OUT = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"
PROJECT = OUT / ".rt/afb1"


def binding(path):
    data = path.read_bytes()
    return {"task_relative": path.relative_to(TASK).as_posix(), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def prefixes(text):
    return {m.group(1): text[m.start():text.index(":=", m.end()) + 2]
            for m in re.finditer(r"(?m)^theorem (\w+)", text)}


def main():
    source = TASK / "formalization/AnalyticPSeriesTail.lean"
    original = source.read_text(encoding="utf-8")
    replacements = {
        "(by positivity : -(s : ℝ) ≤ 0)": "(by have h : (0 : ℝ) ≤ s := Nat.cast_nonneg s; linarith)",
        "[sum_range_one, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm,":
            "[sum_range_one, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_left_comm,",
        "  exact add_le_add_left htail _": "  exact add_le_add le_rfl htail",
        "    field_simp [hM0.ne', hs0.ne']\n    ring": "    field_simp [hM0.ne', hs0.ne']",
    }
    fixed = original
    for old, new in replacements.items():
        assert fixed.count(old) == 1, old
        fixed = fixed.replace(old, new)
    assert prefixes(fixed) == prefixes(original) and len(prefixes(fixed)) == 4
    target = PROJECT / "private-repairs/v2/src/AnalyticPSeriesTail.lean"
    assert not target.exists()
    target.write_text(fixed, encoding="utf-8")
    report = {"status": "private_source_only_not_compiled", "original_candidate": binding(source),
              "private_corrected_source": binding(target), "all_4_original_full_statement_prefixes_exact": True,
              "reason": "Actual nonpositive exponent needs linarith; ordered simp needs Nat.add_zero; the sum inequality uses componentwise add_le_add; field_simp already closes final factorization.",
              "changed_proof_bodies": ["reciprocal_power_tail_bound", "reciprocal_power_tail_bound_factored"],
              "actual_failure_call_index": 13, "original_candidates_and_frozen_copies_unchanged": True,
              "actual_lean_calls": 0}
    report_path = OUT / "private-pseries-repair-v2.json"
    assert not report_path.exists()
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "source": binding(target), "report": binding(report_path)}))


if __name__ == "__main__":
    main()
