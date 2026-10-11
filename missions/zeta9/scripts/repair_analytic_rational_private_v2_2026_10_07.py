"""Private-only repairs for retained rational-factorial compiler errors."""
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
    source = TASK / "formalization/AnalyticRationalFactorial.lean"
    original = source.read_text(encoding="utf-8")
    old = "  field_simp [rational_factorial_ne_zero]\n  ring"
    assert original.count(old) == 1
    fixed = original.replace(old, "  field_simp [rational_factorial_ne_zero]")
    old_cast = "  exact_mod_cast actualR_factorial n k hk"
    assert fixed.count(old_cast) == 1
    fixed = fixed.replace(old_cast, "  have h := congrArg (fun q : ℚ => (q : ℝ)) (actualR_factorial n k hk)\n  push_cast at h\n  exact h")
    assert prefixes(fixed) == prefixes(original) and len(prefixes(fixed)) == 10
    target = PROJECT / "private-repairs/v2/src/AnalyticRationalFactorial.lean"
    assert not target.exists()
    target.write_text(fixed, encoding="utf-8")
    report = {"status": "private_source_only_not_compiled", "original_candidate": binding(source),
              "private_corrected_source": binding(target), "all_10_original_full_statement_prefixes_exact": True,
              "reason": "Actual field_simp already closes the rational identity; actual ℚ→ℝ bridge needs congrArg cast then push_cast.",
              "changed_proof_bodies": ["actualR_factorial", "actualR_factorial_real"],
              "original_candidates_and_frozen_copies_unchanged": True,
              "actual_failure_call_index": 5, "actual_lean_calls": 0}
    report_path = OUT / "private-rational-repair-v2.json"
    assert not report_path.exists()
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "source": binding(target), "report": binding(report_path)}))


if __name__ == "__main__":
    main()
