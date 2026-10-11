"""Private-only tail proof compatibility repair; preserve all six forall headers."""
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
    source = TASK / "formalization/AnalyticRationalTail.lean"
    original = source.read_text(encoding="utf-8")
    old = "      field_simp [hk0.ne']\n      ring"
    assert original.count(old) == 1
    fixed = original.replace(old, "      field_simp [hk0.ne']")
    old_cast = "  exact_mod_cast actualR_tail_bound_rational n k hn hk"
    assert fixed.count(old_cast) == 1
    fixed = fixed.replace(old_cast, """  have h := actualR_tail_bound_rational n k hn hk
  have hc : (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (( (n.factorial : ℚ) ^ 7 * (2 : ℚ) ^ n / (k : ℚ) ^ (7 * n + 9) : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at hc
  exact hc""")
    assert prefixes(fixed) == prefixes(original) and len(prefixes(fixed)) == 6
    target = PROJECT / "private-repairs/v2/src/AnalyticRationalTail.lean"
    assert not target.exists()
    target.write_text(fixed, encoding="utf-8")
    report = {"status": "private_source_only_not_compiled", "original_candidate": binding(source),
              "private_corrected_source": binding(target), "all_6_original_full_statement_prefixes_exact": True,
              "reason": "Actual field_simp already closes the cleared division identity; cast inequality must first retain the entire rational right side then push_cast.",
              "changed_proof_bodies": ["actualR_tail_bound_rational", "actualR_tail_bound"],
              "actual_failure_call_index": 11, "original_candidates_and_frozen_copies_unchanged": True,
              "actual_lean_calls": 0}
    report_path = OUT / "private-tail-repair-v2.json"
    assert not report_path.exists()
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "source": binding(target), "report": binding(report_path)}))


if __name__ == "__main__":
    main()
