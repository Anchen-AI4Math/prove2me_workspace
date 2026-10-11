"""Private-only exponent-normalization and convert repairs; all 11 headers/4 defs fixed."""
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
    source = TASK / "formalization/AnalyticUniformMomentBound.lean"
    original = source.read_text(encoding="utf-8")
    replacements = {
        "      Real.exp_log (by norm_num : (0 : ℝ) < 729 / 224)]":
            "      Real.exp_log (by norm_num : (0 : ℝ) < 729 / 224)]\n    rw [neg_mul]",
        "    convert h using 1 <;> ring": "    convert h using 1 <;> first | rfl | ring",
    }
    fixed = original
    for old, new in replacements.items():
        assert fixed.count(old) == 1, old
        fixed = fixed.replace(old, new)
    assert prefixes(fixed) == prefixes(original) and len(prefixes(fixed)) == 11
    assert definitions(fixed) == definitions(original) and len(definitions(fixed)) == 4
    target = PROJECT / "private-repairs/v2/src/AnalyticUniformMomentBound.lean"
    assert not target.exists()
    target.write_text(fixed, encoding="utf-8")
    report = {"status": "private_source_only_not_compiled", "original_candidate": binding(source),
              "private_corrected_source": binding(target), "all_11_original_full_statement_prefixes_exact": True,
              "all_4_complete_definition_types_and_values_source_exact": True,
              "reason": "Actual exp arguments require neg_mul normalization; convert emits a reflexive sum equality that should use rfl before ring.",
              "changed_proof_bodies": ["tailMajorant_certified_bound", "actualMoment_uniform_bound"],
              "actual_failure_call_index": 17, "original_candidates_and_frozen_copies_unchanged": True,
              "actual_lean_calls": 0}
    report_path = OUT / "private-uniform-repair-v2.json"
    assert not report_path.exists()
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "source": binding(target), "report": binding(report_path)}))


if __name__ == "__main__":
    main()
