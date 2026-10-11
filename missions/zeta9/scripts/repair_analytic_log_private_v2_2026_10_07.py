"""Private proof-only repair for the retained log bound cast rewrite failure."""
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
    source = TASK / "formalization/AnalyticRationalLogBound.lean"
    original = source.read_text(encoding="utf-8")
    old = """  rw [AnalyticRationalFactorial.actualR_log_factorial n k hk,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (Nat.le_of_lt hk)]"""
    new = """  rw [AnalyticRationalFactorial.actualR_log_factorial n k hk]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_sub (Nat.le_of_lt hk)]"""
    assert original.count(old) == 1
    fixed = original.replace(old, new)
    assert prefixes(fixed) == prefixes(original) and len(prefixes(fixed)) == 5
    target = PROJECT / "private-repairs/v2/src/AnalyticRationalLogBound.lean"
    assert not target.exists()
    target.write_text(fixed, encoding="utf-8")
    report = {"status": "private_source_only_not_compiled", "original_candidate": binding(source),
              "private_corrected_source": binding(target), "all_5_original_full_statement_prefixes_exact": True,
              "reason": "After exact shifted log identity, no Nat cast of an addition occurs in the target; simp handles the existing cast subtraction without a missing-pattern failure.",
              "changed_proof_bodies": ["actualR_log_le_phase"], "actual_failure_call_index": 9,
              "original_candidates_and_frozen_copies_unchanged": True, "actual_lean_calls": 0}
    report_path = OUT / "private-log-repair-v2.json"
    assert not report_path.exists()
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "source": binding(target), "report": binding(report_path)}))


if __name__ == "__main__":
    main()
