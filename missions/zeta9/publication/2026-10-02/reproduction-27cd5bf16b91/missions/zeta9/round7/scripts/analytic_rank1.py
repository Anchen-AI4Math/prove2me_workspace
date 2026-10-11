"""Exact rational audit of the finite inverse-map rank-one diagnostics.

The rational slope uses only truncated positive moments; no zeta values are
loaded.  The approximation inequality follows from Cauchy--Schwarz and the
rigorous moment tails in round 6.
"""

from fractions import Fraction as Q
import gzip
import json
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[4]
VERIFY = ROOT / "missions/zeta9/round6/verification"
OUT = ROOT / "missions/zeta9/round7/verification/analytic-rank1.json"


def f(pair: list[str]) -> Q:
    return Q(int(pair[0]), int(pair[1]))


def main() -> None:
    rows = []
    for n, digits in ((12, 50), (24, 100), (48, 200), (96, 400)):
        with gzip.open(VERIFY / f"analytic-triangle-exact-n{n}.json.gz",
                       "rt", encoding="utf-8") as handle:
            data = json.load(handle)
        T = [[f(entry) for entry in row]
             for row in data["inverse_output_T_rows"]]
        c = [f(row["lower"]) for row in data["moments"]]
        tau = [f(row["tail"]) for row in data["moments"]]
        qbb = sum((c[i]**2 * T[i][0]**2 for i in range(5)), Q())
        qba = sum((c[i]**2 * T[i][0] * T[i][1]
                   for i in range(5)), Q())
        qaa = sum((c[i]**2 * T[i][1]**2 for i in range(5)), Q())
        det = qbb*qaa-qba*qba
        assert qbb > 0 and det > 0
        r = qba/qbb
        error_b = sum((tau[i]*abs(T[i][0]) for i in range(5)), Q())
        error_a = sum((tau[i]*abs(T[i][1]) for i in range(5)), Q())
        target = Q(1, 10**digits)
        assert 20*det/qbb < target*target
        assert error_a+abs(r)*error_b < target/2
        deficit = det/(qbb*qaa)
        exponent = {12:105, 24:210, 48:421, 96:842}[n]
        assert Q(1,10**exponent) < deficit < Q(1,10**(exponent-1))
        rows.append({
            "n": n,
            "rational_slope_definition": "Q_BA/Q_BB from lower rational moments",
            "rational_slope_denominator_decimal_digits": len(str(r.denominator)),
            "certified_absolute_zeta9_error_lt": f"1e-{digits}",
            "deficit_between": [f"1e-{exponent}",
                                f"1e-{exponent-1}"],
            "proof": "sqrt(5 det/Q_BB) < half target; moment truncation error_a+abs(r)*error_b < half target",
        })
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(rows, indent=2), encoding="utf-8")
    print(json.dumps(rows, indent=2))


if __name__ == "__main__":
    main()
