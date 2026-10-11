"""Private actual moment proof repairs; preserve every type and whole definition."""
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


def definitions(text):
    return {m.group(1): m.group(0) for m in re.finditer(r"(?ms)^def (\w+)\b.*?(?=\n\n)", text)}


def main():
    source = TASK / "formalization/AnalyticMomentBounds.lean"
    original = source.read_text(encoding="utf-8")
    replacements = {
        "    field_simp [hk0.ne']\n    ring": "    field_simp [hk0.ne']",
        "actualMomentSequence n r (m + n)": "actualMomentSequence n r (n + m)",
        "actual_compact_momentTerm_bound n r (m + n + 1)":
            "actual_compact_momentTerm_bound n r (n + m + 1)",
        "    _ = _ := by dsimp [B]; ring": """    _ = 5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := by dsimp [B]; ring""",
        """      rw [tsum_mul_left]
      congr 1
      funext m
      rw [mul_one_div]""": """      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      rw [mul_one_div]""",
    }
    fixed = original
    for old, new in replacements.items():
        assert fixed.count(old) == 1, old
        fixed = fixed.replace(old, new)
    assert prefixes(fixed) == prefixes(original) and len(prefixes(fixed)) == 15
    assert definitions(fixed) == definitions(original) and len(definitions(fixed)) == 5
    target = PROJECT / "private-repairs/v2/src/AnalyticMomentBounds.lean"
    assert not target.exists()
    target.write_text(fixed, encoding="utf-8")
    report = {"status": "private_source_only_not_compiled", "original_candidate": binding(source),
              "private_corrected_source": binding(target), "all_15_original_full_statement_prefixes_exact": True,
              "all_5_complete_definition_types_and_values_source_exact": True,
              "reason": "Actual field_simp closes tail factorization; sum_range_add uses n+m; the final calc target needs its explicit exponent-10 expression; tsum_mul_left must be reversed.",
              "changed_proof_bodies": ["actual_tail_momentTerm_bound", "actual_compact_moment_sum_bound",
                                       "actual_tail_moment_sum_factorial_bound"],
              "actual_failure_call_index": 15, "original_candidates_and_frozen_copies_unchanged": True,
              "actual_lean_calls": 0}
    report_path = OUT / "private-moment-repair-v2.json"
    assert not report_path.exists()
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "source": binding(target), "report": binding(report_path)}))


if __name__ == "__main__":
    main()
