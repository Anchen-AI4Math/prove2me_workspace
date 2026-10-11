"""Private proof-only repair for the two observed successor-rewrite errors."""
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
    source = TASK / "formalization/AnalyticFactorialBounds.lean"
    original = source.read_text(encoding="utf-8")
    old = "rw [Nat.succ_eq_add_one, log_factorial_succ, Nat.cast_add, Nat.cast_one]"
    new = "rw [log_factorial_succ, Nat.cast_add, Nat.cast_one]"
    assert original.count(old) == 2
    fixed = original.replace(old, new)
    assert prefixes(fixed) == prefixes(original) and len(prefixes(fixed)) == 7
    target = PROJECT / "private-repairs/v2/src/AnalyticFactorialBounds.lean"
    assert not target.exists()
    target.parent.mkdir(parents=True)
    target.write_text(fixed, encoding="utf-8")
    report = {"status": "private_source_only_not_compiled", "actual_failure_receipt":
              "actual-author-runs/003-native-AnalyticFactorialBounds", "original_candidate": binding(source),
              "private_corrected_source": binding(target), "all_7_original_full_statement_prefixes_exact": True,
              "changed_proof_bodies": ["log_factorial_lower", "log_factorial_upper"],
              "reason": "Actual target already elaborated successor as n+1; the redundant rw Nat.succ_eq_add_one fails.",
              "original_candidate_and_frozen_source_copies_unchanged": True,
              "no_definition_value_changes": True, "actual_lean_calls": 0}
    report_path = OUT / "private-factorial-repair-v2.json"
    assert not report_path.exists()
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "private_source": binding(target), "report": binding(report_path)}))


if __name__ == "__main__":
    main()
