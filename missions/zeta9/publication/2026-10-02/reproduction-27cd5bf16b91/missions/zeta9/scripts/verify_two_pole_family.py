"""Exact checks for the all-pairs, two-square-pole h=2 arithmetic barrier.

This proves the finite identities and p-adic checks stated in the note.
The all-parameter conclusion is a written proof, not a finite extrapolation.
"""
from __future__ import annotations

import hashlib
import json
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "scripts"))
import verify_local_connection  # noqa: F401: established local flint path
from flint import arb, ctx, fmpq as Q, fmpq_poly as Poly
import sympy as sp

sys.set_int_max_str_digits(0)
X = Poly([0, 1])
MU_ZERO = Q(3, 4)
W_LOWER = Q(1, 20643840)
DELTA_LOWER_CONSTANT = Q(25, 4096) * W_LOWER**2


def vp_int(value, prime):
    value = abs(int(value))
    if not value:
        return math.inf
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def vp(value, prime):
    value = Q(value)
    return vp_int(value.numer(), prime) - vp_int(value.denom(), prime)


def primitives(delta):
    denominator = math.lcm(*(int(c.denom()) for c in delta))
    integers = [int((denominator * c).numer()) for c in delta]
    content = math.gcd(*integers)
    coefficients = [c // content for c in integers]
    scalar = Q(denominator, content)
    assert Poly(coefficients) == scalar * delta
    assert math.gcd(*coefficients) == 1
    return scalar, coefficients


def evaluate(coefficients):
    precision = max(512, max(abs(c).bit_length() for c in coefficients) + 256)
    for _ in range(7):
        ctx.prec = precision
        zeta = arb(9).zeta()
        value = arb(0)
        for coefficient in reversed(coefficients):
            value = value * zeta + coefficient
        if value > 0 and value.rel_accuracy_bits() >= 80:
            return value, precision
        precision *= 2
    raise AssertionError("positive Arb ball not certified")


def construct(a, b):
    assert 1 <= a < b
    harmonic_a = sum((Q(1, j**9) for j in range(1, a + 1)), Q(0))
    harmonic_b = sum((Q(1, j**9) for j in range(1, b + 1)), Q(0))
    beta_a = -a**8 * harmonic_a - Q(1, 8) + Q(1, 2 * a)
    beta_b = -b**8 * harmonic_b - Q(1, 8) + Q(1, 2 * b)
    f_a = a**8 * X + beta_a
    f_b = b**8 * X + beta_b
    difference = b * b - a * a
    m0 = (f_a - f_b) / difference
    m1 = (-a * a * f_a + b * b * f_b) / difference
    m2 = MU_ZERO + (a**4 * f_a - b**4 * f_b) / difference
    delta_matrix = m0 * m2 - m1 * m1
    delta_formula = MU_ZERO * (f_a - f_b) / difference - f_a * f_b
    assert delta_matrix == delta_formula
    assert delta_formula.degree() == 2
    assert delta_formula[2] == -a**8 * b**8
    integer_quotient = -(a**6 + a**4 * b**2 + a**2 * b**4 + b**6)
    assert Q(a**8 - b**8, difference) == integer_quotient
    assert delta_formula[1] == (
        -a**8 * beta_b - b**8 * beta_a + MU_ZERO * integer_quotient
    )
    scalar, coefficients = primitives(delta_formula)
    # The reduced scalar denominator divides the integral leading coefficient.
    assert (a**8 * b**8) % int(scalar.denom()) == 0
    prime_records = []
    weighted_product = 1
    eligible_product = 1
    for prime in sp.primerange(5, b + 1):
        prime = int(prime)
        if 2 * prime <= b or (a * b) % prime == 0:
            continue
        valuations = [vp(coefficient, prime) for coefficient in delta_formula]
        scalar_valuation = vp(scalar, prime)
        assert scalar_valuation == -min(valuations)
        eligible_product *= prime
        if prime <= a:
            assert vp(harmonic_a, prime) == vp(harmonic_b, prime) == -9
            assert vp(beta_a, prime) == vp(beta_b, prime) == -9
            assert vp_int(difference, prime) <= 1
            assert valuations[0] == -18
            assert scalar_valuation == 18
            required = 18
            branch = "common-harmonic-prime"
        else:
            assert vp(harmonic_b, prime) == -9
            assert vp(beta_a, prime) >= 0 and vp(beta_b, prime) == -9
            assert valuations[1] == -9
            assert scalar_valuation >= 9
            required = 9
            branch = "new-harmonic-prime"
        weighted_product *= prime**required
        prime_records.append({
            "prime": prime,
            "branch": branch,
            "vp_difference": vp_int(difference, prime),
            "delta_coefficient_valuations": valuations,
            "vp_primitive_multiplier": scalar_valuation,
            "required_multiplier_valuation": required,
        })
    # A rational scalar can have negative valuations only at primes dividing ab.
    assert scalar >= Q(weighted_product, a**8 * b**8)
    assert scalar >= Q(eligible_product**9, a**8 * b**8)
    lower_bound = DELTA_LOWER_CONSTANT * Q(
        weighted_product, a**8 * b**8 * (b * b + 1)**4
    )
    value, precision = evaluate(coefficients)
    assert value >= arb(lower_bound)
    return {
        "a": a, "b": b, "h": 2, "numerator": "1",
        "rational_determinant_coefficients": [str(c) for c in delta_formula],
        "primitive_integer_coefficients": [str(c) for c in coefficients],
        "minimal_positive_rational_multiplier": str(scalar),
        "reduced_multiplier_denominator_divides": str(a**8 * b**8),
        "eligible_prime_product": str(eligible_product),
        "weighted_required_prime_product": str(weighted_product),
        "prime_checks": prime_records,
        "rigorous_uniform_lower_bound": str(lower_bound),
        "positive_value_ball": value.str(40),
        "log_positive_value_ball": value.log().str(30),
        "log_positive_value_mid": float(value.log().mid()),
        "strictly_below_one": bool(value < 1),
        "strictly_above_one": bool(value > 1),
        "precision_bits": precision,
    }


def symbolic_checks():
    u, v, fa, fb, mu = sp.symbols("u v fa fb mu")
    d = v - u
    m0 = (fa - fb) / d
    m1 = (-u * fa + v * fb) / d
    m2 = mu + (u * u * fa - v * v * fb) / d
    assert sp.cancel(m0 * m2 - m1**2 - (mu * (fa - fb) / d - fa * fb)) == 0
    a, b = sp.symbols("a b")
    assert sp.expand((b * b - a * a) * (
        -(a**6 + a**4 * b**2 + a**2 * b**4 + b**6)
    ) - (a**8 - b**8)) == 0
    assert Q.bernoulli(2) * Q(math.factorial(9), math.factorial(8) * 2) == MU_ZERO
    # w9(y) >= 2*6^8/(8!*4^9*3^8) on 1/4 <= y <= 1.
    assert Q(2 * 6**8, math.factorial(8) * 4**9 * 3**8) == W_LOWER
    return {
        "abstract_two_by_two_determinant_identity": "passed",
        "difference_of_eighth_powers_integer_quotient": "passed",
        "mu9_of_one": str(MU_ZERO),
        "uniform_weight_lower_bound_on_one_quarter_to_one": str(W_LOWER),
        "uniform_delta_lower_bound_constant": str(DELTA_LOWER_CONSTANT),
    }


def main():
    symbolic = symbolic_checks()
    pairs = [(a, b) for b in range(2, 25) for a in range(1, b)]
    pairs += [(25, 26), (31, 32), (63, 64), (127, 128)]
    records = [construct(a, b) for a, b in pairs]
    small = [record for record in records if record["strictly_below_one"]]
    assert len(records) == 280
    assert len(small) == 1 and (small[0]["a"], small[0]["b"]) == (1, 2)
    assert small[0]["primitive_integer_coefficients"] == ["-6163", "22568", "-16384"]
    assert all(record["strictly_below_one"] or record["strictly_above_one"] for record in records)
    prime_checks = [check for record in records for check in record["prime_checks"]]
    summary = {
        "status": "passed",
        "case_count": len(records),
        "pair_boundary": "All 1 <= a < b <= 24; extra adjacent pairs (25,26),(31,32),(63,64),(127,128).",
        "prime_check_count": len(prime_checks),
        "common_branch_count": sum(check["branch"] == "common-harmonic-prime" for check in prime_checks),
        "new_branch_count": sum(check["branch"] == "new-harmonic-prime" for check in prime_checks),
        "prime_divides_difference_count": sum(check["vp_difference"] > 0 for check in prime_checks),
        "below_one_pairs": [[record["a"], record["b"]] for record in small],
        "symbolic_checks": symbolic,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "boundary": "All-pairs divergence is established by the written proof; finite exact checks certify identities and arithmetic implementation, not irrationality.",
    }
    output = HERE / "verification" / "two-pole-family-2026-10-01"
    output.mkdir(parents=True, exist_ok=True)
    (output / "certificate.json").write_text(json.dumps({**summary, "cases": records}, indent=2) + "\n", encoding="utf-8")
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
