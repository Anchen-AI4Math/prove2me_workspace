"""Exact rational checks for the saddle threshold and limiting cubatures.

The analytic Gaussian moment limit and eventual positivity are proved in the
research note, not by this finite algebraic checker.
"""

from fractions import Fraction as Q


def main() -> None:
    left = Q(10029764657548, 10**13)
    right = Q(10029764657550, 10**13)
    phi = lambda x: (x + 2) * x**10 - (x - 1) * (x + 1) ** 10
    amin = 1 / (right - 1) - 10 / (left * (left + 1)) - 1 / (left + 2)
    amax = 1 / (left - 1) - 10 / (right * (right + 1)) - 1 / (right + 2)
    assert phi(left) > 0 > phi(right)
    assert Q(330658, 1000) < amin < amax < Q(330659, 1000)
    assert Q(95251, 10**6) ** 2 * amax < 3
    assert 3 < Q(95252, 10**6) ** 2 * amin

    gaussian_moments = (1, 0, 1, 0, 3)
    nodes = (-2, -1, 0, 1, 2)
    weights = (Q(1, 12), Q(1, 6), Q(1, 2), Q(1, 6), Q(1, 12))
    assert all(sum(w * x**r for w, x in zip(weights, nodes)) == moment
               for r, moment in enumerate(gaussian_moments))
    assert all(w > 0 for w in weights)
    print("passed: exact saddle interval and five-point Gaussian moments")


if __name__ == "__main__":
    main()
