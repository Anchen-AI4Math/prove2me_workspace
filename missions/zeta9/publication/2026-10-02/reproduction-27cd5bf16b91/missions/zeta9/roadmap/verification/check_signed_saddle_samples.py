"""Exact finite sign certificates for two frozen full-lattice first rows.

The uniform saddle-window lemma is proved in the research note; this script
only replays the two finite integer inequalities used there.
"""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2] / "round7/verification/modulus-scan.json"
sys.set_int_max_str_digits(0)


def polynomial(coeff, u):
    value = 0
    for a in reversed(coeff):
        value = value * u + a
    return value


def check(case, stop, left, right):
    n = int(case["n"])
    mode = next(item for item in case["modes"] if item["mode"] == "n2r")
    tier = next(item for item in mode["tiers"] if "full_N" in item["labels"])
    coeff = [int(a) for a in tier["gauss_reduced_rows"][0]]
    u0 = (n + 1) * (2*n + 1)
    first = polynomial(coeff, u0)
    norm1 = sum(abs(a) * n ** (2*r) for r, a in enumerate(coeff))
    assert first < 0 and norm1 < -first
    assert all(polynomial(coeff, k*(k+n)) < 0 for k in range(n+1, stop))

    def scaled(x):
        return n*n*x*(x+1)

    assert polynomial(coeff, scaled(left)) * polynomial(coeff, scaled(right)) < 0
    ratio = Fraction(1)
    for k in range(n+1, stop):
        ratio *= Fraction(k**10 * (k+2*n+1), (k-n)*(k+n+1)**10)
    assert 10**30 * ratio < 1
    tail_constant = n * (10*110**4 + 3*144**4)
    assert tail_constant * norm1 * ratio < -first
    return {"n": n, "first_term_sign": "negative", "sampled_initial_signs": stop-n-1,
            "tail_ratio_less_than_1e-30": True, "absolute_tail_below_first_term": True}


def main():
    with ROOT.open(encoding="utf-8") as stream:
        data = json.load(stream)
    cases = {int(case["n"]): case for case in data["cases"]}
    result = [check(cases[24], 49, Fraction(2), Fraction(21, 10)),
              check(cases[192], 226, Fraction(117, 100), Fraction(59, 50))]
    print(json.dumps(result, ensure_ascii=True))


if __name__ == "__main__":
    main()
