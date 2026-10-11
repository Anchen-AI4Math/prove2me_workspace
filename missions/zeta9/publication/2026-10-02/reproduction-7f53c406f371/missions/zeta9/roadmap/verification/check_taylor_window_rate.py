"""Exact rational check of the displayed -10.1109 Taylor-window rate."""
from __future__ import annotations

from fractions import Fraction


def main():
    # 2*10.1109 = 20.2218.  The positive exponential tail after k=100
    # is bounded geometrically by the first omitted term and ratio x/102.
    x = Fraction(101109, 5000)
    term = Fraction(1)
    partial = term
    for k in range(1, 101):
        term *= x / k
        partial += term
    first_omitted = term * x / 101
    upper = partial + first_omitted / (1 - x / 102)
    assert upper < 605650000
    assert Fraction(605650000) < Fraction(1499000000 * 40, 99)
    print("passed: exp(20.2218) < 1499000000/(99/40) by exact rational Taylor bound")


if __name__ == "__main__":
    main()
