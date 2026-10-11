"""Rational interval certificate for the p=9,m=n real phase exponent."""

from fractions import Fraction as Q
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
OUT = ROOT / "missions/zeta9/round7/verification/analytic-exponent.json"


def raw_log_interval(x: Q, terms: int = 18) -> tuple[Q, Q]:
    assert Q(1) <= x <= Q(2)
    y = (x - 1) / (x + 1)
    partial = 2 * sum((y ** (2 * k + 1) / (2 * k + 1)
                       for k in range(terms)), Q(0))
    tail = 2 * y ** (2 * terms + 1) / (
        (2 * terms + 1) * (1 - y * y))
    return partial, partial + tail


def log_interval(x: Q) -> tuple[Q, Q]:
    assert x > 0
    k = 0
    while x < 1:
        x *= 2
        k -= 1
    while x > 2:
        x /= 2
        k += 1
    lo, hi = raw_log_interval(x)
    l2, h2 = raw_log_interval(Q(2))
    if k >= 0:
        return lo + k * l2, hi + k * h2
    return lo + k * h2, hi + k * l2


def linear_log_interval(pairs: list[tuple[Q, Q]]) -> tuple[Q, Q]:
    low = high = Q(0)
    for coefficient, argument in pairs:
        lo, hi = log_interval(argument)
        if coefficient >= 0:
            low += coefficient * lo
            high += coefficient * hi
        else:
            low += coefficient * hi
            high += coefficient * lo
    return low, high


def decimal_out(x: Q, digits: int = 14) -> str:
    scale = 10 ** digits
    floor = x.numerator * scale // x.denominator
    sign = "-" if floor < 0 else ""
    return f"{sign}{abs(floor)//scale}.{abs(floor)%scale:0{digits}d}"


def main() -> None:
    x = Q(1003, 1000)
    f_lo, f_hi = linear_log_interval([
        (10*x, x), (x+2, x+2), (-(x-1), x-1), (-10*(x+1), x+1)
    ])
    f1_lo, f1_hi = linear_log_interval([
        (Q(3), Q(3)), (Q(-20), Q(2))
    ])
    A = Q(301,100) * (Q(101,201) ** 10)
    assert f_lo > Q(-10564155, 1000000)
    assert f1_hi + A < Q(-10564, 1000)
    assert A < Q(309, 100000)
    assert log_interval(Q(2))[0] > Q(693147, 1000000)
    assert log_interval(Q(3))[1] < Q(1098613, 1000000)
    result = {
        "method": "atanh rational series with geometric tail; all assertions exact",
        "x": "1003/1000",
        "f_x_lower_gt": "-10.564155",
        "f_1_plus_A_upper_lt": "-10.564",
        "A_rational": [str(A.numerator), str(A.denominator)],
        "f_x_interval_decimal_noncertifying": [
            decimal_out(f_lo), decimal_out(f_hi)
        ],
        "f_1_interval_decimal_noncertifying": [
            decimal_out(f1_lo), decimal_out(f1_hi)
        ],
        "log_2_lower_gt": "0.693147",
        "log_3_upper_lt": "1.098613",
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
