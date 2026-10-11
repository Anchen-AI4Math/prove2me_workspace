"""Exact rational audit of the limiting Taylor transfer certificate.

The mathematical conclusion for the varying connection uses the already
proved round-7 limit.  This script checks the new finite matrix identities.
"""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import math
import re


NOTE = Path(__file__).resolve().parents[1] / "research/taylor-connection-next.md"


def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def inverse(a):
    size = len(a)
    aug = [[Fraction(a[i][j]) for j in range(size)] +
           [Fraction(i == j) for j in range(size)] for i in range(size)]
    for j in range(size):
        pivot = next(i for i in range(j, size) if aug[i][j])
        aug[j], aug[pivot] = aug[pivot], aug[j]
        value = aug[j][j]
        aug[j] = [x / value for x in aug[j]]
        for i in range(size):
            if i != j:
                value = aug[i][j]
                aug[i] = [x - value * y for x, y in zip(aug[i], aug[j])]
    return [row[size:] for row in aug]


def matrix_from_note(label):
    source = NOTE.read_text(encoding="utf-8")
    match = re.search(r"^" + re.escape(label) + r"\s*=\s*\n([\s\S]+?)\n```", source, re.M)
    assert match, label
    rows = []
    for line in match.group(1).splitlines():
        line = line.strip()
        if line.startswith("["):
            rows.append([int(x.strip()) for x in line.strip("[]").split(",")])
    assert len(rows) == 5 and all(len(row) == 5 for row in rows), label
    return rows


def main():
    a = matrix_from_note("A")
    a2 = matrix_from_note("A²")
    assert matmul(a, a) == a2
    assert all(value > 0 for row in a2 for value in row)
    assert [x > 0 for x in a[4]] == [True, False, False, False, False]

    # Y is multiplication by y in Q[y]/(h), h=7y^5+5y^4-23y^3-26y^2-9y-1.
    y = [[Fraction(int(j == i + 1)) for j in range(5)] for i in range(4)]
    y.append([Fraction(x, 7) for x in (1, 9, 26, 23, -5)])
    eye = [[Fraction(int(i == j)) for j in range(5)] for i in range(5)]
    y_minus_two = [[y[i][j] - 2 * eye[i][j] for j in range(5)] for i in range(5)]
    power = eye
    for _ in range(10):
        power = matmul(power, y)
    inverse_cubed = eye
    inv = inverse(y_minus_two)
    for _ in range(3):
        inverse_cubed = matmul(inverse_cubed, inv)
    g = matmul(power, inverse_cubed)
    b = [[Fraction(math.comb(i, j) * 2 ** (i - j)) if j <= i else Fraction(0)
          for j in range(5)] for i in range(5)]
    d = 22235661
    left = matmul(b, a)
    right = matmul(g, b)
    assert all(left[i][j] == d * right[i][j] for i in range(5) for j in range(5))
    print("passed: Taylor limit conjugacy, last-row sign, and all 25 entries of A^2 positive")


if __name__ == "__main__":
    main()
