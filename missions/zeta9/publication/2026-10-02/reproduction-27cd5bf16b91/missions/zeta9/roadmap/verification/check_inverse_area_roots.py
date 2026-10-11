"""Exact rational sign certificate for the five roots used in the area rate."""

from fractions import Fraction as F
import json
from pathlib import Path


COEFFS = (-1, -10336452, -10120051241400, -82488337575256095,
          -33339376907507494, 22235661)
INTERVALS = (
    (F(-99, 40), F(-12, 5), -1, 1),
    (F(-1, 8000), F(-1, 9000), 1, -1),
    (F(-1, 1000000), F(-1, 1200000), -1, 1),
    (F(-1, 9000000), F(-1, 10000000), 1, -1),
    (F(1499000000), F(1499400000), -1, 1),
)


def q(x: F) -> F:
    result = F(0)
    for coeff in reversed(COEFFS):
        result = result * x + coeff
    return result


def sign(x: F) -> int:
    return (x > 0) - (x < 0)


def main() -> None:
    frozen = (Path(__file__).resolve().parents[2] / "round8/verification/limit-obstruction.json")
    certificate = json.loads(frozen.read_text(encoding="utf-8"))
    assert certificate["status"] == "passed"
    assert tuple(certificate["inverse_primitive_charpoly"]) == COEFFS
    assert len(COEFFS) == len(INTERVALS) + 1
    for i, (left, right, sign_left, sign_right) in enumerate(INTERVALS):
        assert left < right
        if i:
            assert INTERVALS[i-1][1] < left
        assert sign(q(left)) == sign_left
        assert sign(q(right)) == sign_right
        assert sign_left == -sign_right
    assert abs(INTERVALS[0][0]) == F(99, 40)
    assert INTERVALS[-1][1] == 1499400000
    assert abs(INTERVALS[0][0]) * INTERVALS[-1][1] == 3711015000
    print("passed: five disjoint rational sign-changing root intervals; exterior-square radius < 3711015000")


if __name__ == "__main__":
    main()
