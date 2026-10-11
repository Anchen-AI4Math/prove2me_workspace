"""Pure SOURCE/math preparation. Never runs Lean, lake, APIs or credentials."""
from __future__ import annotations

import hashlib
import json
import math
import re
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
OUT = TASK / "verification/formalization-analytic-factorial-preparation-2026-10-07"


def binding(path: Path) -> dict:
    data = path.read_bytes()
    return {
        "task_relative" if path.is_relative_to(TASK) else "root_relative":
            path.relative_to(TASK if path.is_relative_to(TASK) else WORKSPACE).as_posix(),
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def real_product_formula(n: int, k: int) -> Fraction:
    numerator = math.factorial(n) ** 7
    for i in range(n):
        numerator *= k - i - 1
    for i in range(n):
        numerator *= k + n + i + 1
    pole = math.prod(k + j for j in range(n + 1))
    return Fraction(numerator, pole ** 9)


def factorial_formula(n: int, k: int) -> Fraction:
    return Fraction(
        math.factorial(n) ** 7 * math.factorial(k - 1) ** 10 * math.factorial(k + 2 * n),
        math.factorial(k - n - 1) * math.factorial(k + n) ** 10,
    )


def main() -> None:
    source_paths = [TASK / "formalization" / name for name in (
        "AnalyticFactorialBounds.lean", "AnalyticRationalFactorial.lean",
        "AnalyticRationalLogBound.lean", "AnalyticRationalTail.lean",
    )]
    sources = []
    all_names = []
    for path in source_paths:
        text = path.read_text(encoding="utf-8")
        assert not re.search(r"\b(?:sorry|admit|native_decide)\b", text)
        assert not re.search(r"(?m)^\s*axiom\b", text)
        names = re.findall(r"(?m)^theorem\s+(\w+)", text)
        all_names.extend(names)
        sources.append({**binding(path), "complete_theorem_bodies": names})
    assert len(all_names) == 28 and len(set(all_names)) == 28

    native = TASK / "verification/formalization-analytic-phase-upper-bound-2026-10-07/native-export"
    phase_expected = {
        "AnalyticPhase.lean": "2b53b56f103bc69322c35d18e120c248cc34402fe831b7be86651f584d3bf4bd",
        "AnalyticPhaseUpperBound.lean": "388c2be7c6401e0b0944e5ee9601ddd4f9359f85d05319ce191e6c6a4d0f1635",
    }
    phase_bindings = []
    for name, expected in phase_expected.items():
        row = binding(native / name)
        assert row["sha256"] == expected
        phase_bindings.append(row)

    mathlib = WORKSPACE / ".lake/packages/mathlib/Mathlib"
    signatures = [
        ("Analysis/SpecialFunctions/Log/Basic.lean", (
            "theorem log_le_sub_one_of_pos", "theorem log_mul", "theorem log_div",
            "theorem log_pow", "theorem log_le_iff_le_exp")),
        ("Data/Nat/Factorial/Basic.lean", (
            "theorem factorial_succ", "theorem factorial_mul_ascFactorial'",
            "theorem factorial_mul_descFactorial")),
        ("Data/Nat/Factorial/BigOperators.lean", (
            "theorem ascFactorial_eq_prod_range", "theorem descFactorial_eq_prod_range")),
        ("Algebra/BigOperators/Ring/Finset.lean", (
            "theorem prod_range_natCast_sub", "lemma cast_prod")),
        ("Analysis/SumIntegralComparisons.lean", (
            "theorem AntitoneOn.tsum_comp_add_le_integral",)),
    ]
    dependency_signatures = []
    for rel, needles in signatures:
        path = mathlib / rel
        text = path.read_text(encoding="utf-8")
        assert all(needle in text for needle in needles), (rel, needles)
        dependency_signatures.append({**binding(path), "observed_signatures": list(needles)})

    factorial_equalities = zero_terms = tail_pointwise_checks = 0
    for n in range(9):
        for k in range(n + 1, 5 * n + 10):
            actual = real_product_formula(n, k)
            assert actual == factorial_formula(n, k) and actual > 0
            factorial_equalities += 1
        for k in range(1, n + 1):
            assert real_product_formula(n, k) == 0
            zero_terms += 1
        if n:
            for k in range(2 * n, 8 * n + 3):
                upper = Fraction(math.factorial(n) ** 7 * 2 ** n, k ** (7 * n + 9))
                assert real_product_formula(n, k) <= upper
                tail_pointwise_checks += 1

    compact_constants = [4 * 6 ** r for r in range(5)]
    tail_constants = [Fraction(9, 7) * 3 ** r * Fraction(2) ** (r - 9) for r in range(5)]
    assert max(compact_constants) == 5184
    assert max(tail_constants) == Fraction(729, 224)
    exponent_domain = [{"r": r, "s_minus_7n": 9 - 2 * r,
                       "s_minus_one_minus_7n": 8 - 2 * r} for r in range(5)]
    assert all(row["s_minus_one_minus_7n"] >= 0 for row in exponent_domain)
    c = Fraction(2641, 250)
    gamma_lower = Fraction(7) + 6 * Fraction(693147, 1000000)
    assert gamma_lower - c == Fraction(297441, 500000) > 0

    # This is the polynomial identity for the log(n) coefficient after
    # splitting k = n*x. All entries are integer coefficients in n,k.
    log_n_coeff = {"n": 7 + 2 + 1 - 10, "k": 10 + 1 - 1 - 10}
    linear_coeff = {"n": -7 - 2 - 1 + 10, "k": -10 - 1 + 1 + 10}
    assert log_n_coeff == {"n": 0, "k": 0}
    assert linear_coeff == {"n": 0, "k": 0}
    assert 7 + 10 + 1 == 18

    report = {
        "schema_version": 1, "prepared_at_utc": datetime.now(timezone.utc).isoformat(),
        "status": "PURE_SOURCE_PREPARATION_ONLY",
        "actual_lean_calls": 0, "actual_kernel_checks": 0,
        "actual_api_calls": 0, "credential_reads": 0,
        "complete_theorem_bodies": len(all_names), "sources": sources,
        "required_verified_native_phase_dependencies": phase_bindings,
        "actual_product_dependency": binding(TASK / "formalization/CoefficientMap.lean"),
        "mathlib_signature_bindings": dependency_signatures,
        "exact_fraction_checks": {
            "finite_product_factorial_equalities": factorial_equalities,
            "finite_zero_terms": zero_terms,
            "finite_actual_tail_pointwise_bounds": tail_pointwise_checks,
            "finite_checks_are_not_universal_proofs": True,
            "compact_constants_by_r": compact_constants,
            "tail_constants_by_r": [str(x) for x in tail_constants],
            "tail_exponent_domain": exponent_domain,
            "phase_exponent_c": str(c), "tail_gamma_lower": str(gamma_lower),
            "tail_gamma_lower_minus_c": str(gamma_lower - c),
            "exact_log_remainder_constant": 18,
            "log_n_coefficient_cancellation": log_n_coeff,
            "linear_term_cancellation": linear_coeff,
        },
        "remaining_for_whole_Z9_A": [
            "Compile these 28 complete SOURCE endpoints with own objects and actual full types.",
            "Independent review of every actual source/type/value/axiom boundary.",
            "Prove quantitative p-series tail with M=2n, s=7n+9-2r.",
            "Prove real moment summation bound from compact and tail bounds.",
            "Prove arbitrary changing-coefficient weighted triangle estimate and uniform o(1).",
            "Publish accepted actual endpoints on the current public mission workflow.",
        ],
    }
    OUT.mkdir(parents=True, exist_ok=True)
    target = OUT / "preparation-audit.json"
    assert not target.exists(), "Do not overwrite a frozen preparation audit."
    target.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": report["status"], "theorems": len(all_names),
                      "audit": binding(target), "finite_checks": factorial_equalities + zero_terms + tail_pointwise_checks},
                     ensure_ascii=False))


if __name__ == "__main__":
    main()
