"""Exact fixed-dimension Lagrange-basis barrier and its h < m boundary.

The written all-parameter proof is in pole-dimension-frontier-2026-10-01.md.
This script checks a predetermined finite set, including four-way square
collisions modulo a top-half prime and fixed numerator cancellation.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "scripts"))
import verify_local_connection  # noqa: F401: established local flint path
from flint import arb, ctx, fmpq as Q, fmpq_mat as Mat, fmpq_poly as Poly
import sympy as sp

sys.set_int_max_str_digits(0)
T = Poly([0, 1])


def moment(e):
    return (-1)**e * Q.bernoulli(2 * e + 2) * Q(
        math.factorial(2 * e + 9), math.factorial(8) * math.factorial(2 * e + 2)
    )


def vp_int(value, prime):
    value = abs(int(value))
    if not value:
        return math.inf
    answer = 0
    while value % prime == 0:
        value //= prime
        answer += 1
    return answer


def vp(value, prime):
    value = Q(value)
    return vp_int(value.numer(), prime) - vp_int(value.denom(), prime)


def subset_minor(matrix, indices):
    if not indices:
        return Q(1)
    return Mat([[matrix[i, j] for j in indices] for i in indices]).det()


def determinant_polynomial(A, B, bound):
    answer = Poly([])
    for j in range(bound + 1):
        basis = Poly([1])
        denominator = 1
        for k in range(bound + 1):
            if j != k:
                basis *= T - k
                denominator *= j - k
        answer += basis * ((A + j * B).det() / denominator)
    for point in (-2, -1, bound + 1):
        assert answer(point) == (A + point * B).det()
    return answer


def primitive(delta):
    denominator = math.lcm(*(int(c.denom()) for c in delta))
    integers = [int((c * denominator).numer()) for c in delta]
    content = math.gcd(*integers)
    coefficients = [c // content for c in integers]
    scalar = Q(denominator, content)
    assert math.gcd(*coefficients) == 1
    assert Poly(coefficients) == scalar * delta
    return scalar, coefficients


def ball(coefficients):
    precision = max(512, max(abs(c).bit_length() for c in coefficients) + 256)
    for _ in range(7):
        ctx.prec = precision
        zeta = arb(9).zeta()
        value = arb(0)
        for c in reversed(coefficients):
            value = value * zeta + c
        if value > 0 and value.rel_accuracy_bits() >= 80:
            return value, precision
        precision *= 2
    raise AssertionError("Arb could not certify positive value")


def case(poles, h, numerator=(1,), tag="fixed-pole-count-frontier"):
    return {"poles": list(poles), "h": h, "numerator_coefficients": list(numerator), "tag": tag}


def cases():
    answer = []
    pole_groups = {
        1: [(1,), (2,), (5,), (12,)],
        2: [(1, 2), (1, 3), (2, 3), (7, 8), (2, 11), (11, 15), (15, 24)],
        3: [(1, 2, 3), (2, 3, 4), (2, 11, 15), (11, 15, 24), (2, 5, 9)],
        4: [(1, 2, 3, 4), (2, 11, 15, 24), (1, 5, 9, 13)],
        5: [(1, 2, 3, 4, 5), (1, 2, 11, 15, 24)],
    }
    for m, groups in pole_groups.items():
        for poles in groups:
            for h in (m, m + 1, m + 2):
                answer.append(case(poles, h))
    # Fixed positive numerators: origin and shifted zeros; no pole cancellation.
    for numerator in ((0, 1), (0, 0, 1), (1, 2, 1), (625, 50, 1), (25, 26, 1)):
        for h in (3, 4):
            answer.append(case((2, 3, 4), h, numerator, "fixed-positive-numerator"))
    answer.append(case((1, 2, 3), 3, (1, 1), "fixed-numerator-pole-cancellation"))
    answer.append(case((1, 2, 3, 4), 5, (4, 5, 1), "fixed-numerator-two-pole-cancellations"))
    # Actual all-parameter boundary: m=8,h=2,S=1 makes every X moment vanish.
    for shift in (0, 9, 99):
        answer.append(case(tuple(range(shift + 1, shift + 9)), 2, tag="degree-zero-boundary"))
    # A live-X low-dimensional family, outside h>=m and outside rank-zero controls.
    for shift in range(9):
        answer.append(case(tuple(range(shift + 1, shift + 6)), 1, tag="live-low-dimension-linear"))
    return answer


def construct(record):
    original_poles = tuple(record["poles"])
    h = record["h"]
    numerator = Poly(record["numerator_coefficients"])
    original_numerator = numerator
    effective_poles = []
    cancelled = []
    for a in original_poles:
        if numerator(-a * a) == 0:
            numerator, remainder = divmod(numerator, T + a * a)
            assert remainder == 0
            cancelled.append(a)
        else:
            effective_poles.append(a)
    poles = tuple(effective_poles)
    assert poles and poles == tuple(sorted(set(poles)))
    m, u = len(poles), numerator.degree()
    D = Poly([1])
    original_D = Poly([1])
    for a in poles:
        D *= T + a * a
    for a in original_poles:
        original_D *= T + a * a
    assert numerator * original_D == original_numerator * D
    D_prime = D.derivative()
    beta = {
        a: -a**8 * sum((Q(1, j**9) for j in range(1, a + 1)), Q(0))
           - Q(1, 8) + Q(1, 2 * a)
        for a in poles
    }

    def functional(polynomial):
        quotient, remainder = divmod(polynomial, D)
        aa = sum((quotient[e] * moment(e) for e in range(len(quotient))), Q(0))
        bb = Q(0)
        for a in poles:
            residue = remainder(-a * a) / D_prime(-a * a)
            aa += residue * beta[a]
            bb += residue * a**8
        return aa, bb

    moments = [functional(numerator * T**k) for k in range(2 * h - 1)]
    A = Mat([[moments[i + j][0] for j in range(h)] for i in range(h)])
    B = Mat([[moments[i + j][1] for j in range(h)] for i in range(h)])
    delta = determinant_polynomial(A, B, min(h, m))
    scalar, coefficients = primitive(delta)
    value, precision = ball(coefficients)
    data = {
        **record,
        "effective_poles": list(poles),
        "effective_numerator_coefficients": [str(c) for c in numerator],
        "cancelled_fixed_poles": cancelled,
        "effective_pole_count": m,
        "rank_B": B.rank(),
        "degree": delta.degree(),
        "rational_determinant_coefficients": [str(c) for c in delta],
        "primitive_integer_coefficients": [str(c) for c in coefficients],
        "minimal_positive_rational_multiplier": str(scalar),
        "positive_value_ball": value.str(40),
        "log_positive_value_ball": value.log().str(30),
        "log_positive_value_mid": float(value.log().mid()),
        "strictly_below_one": bool(value < 1),
        "precision_bits": precision,
    }
    if h < m:
        if record["tag"] == "degree-zero-boundary":
            assert m >= u + 2 * h + 4
            assert all(B[i, j] == 0 for i in range(h) for j in range(h))
            assert delta.degree() == 0 and coefficients == [1]
        else:
            assert record["tag"] == "live-low-dimension-linear"
            assert h == 1 and m == 5 and numerator == Poly([1])
            assert B[0, 0] == 1 and delta.degree() == 1
            assert scalar.denom() == 1 and coefficients[1] > 0
            common_checks = []
            for prime in sp.primerange(5, min(poles) + 1):
                prime = int(prime)
                if 2 * prime <= max(poles) or math.prod(poles) % prime == 0:
                    continue
                assert vp(delta[0], prime) == -9 and vp(scalar, prime) >= 9
                common_checks.append({"prime": prime, "constant_coefficient_valuation": -9,
                                      "vp_primitive_multiplier": vp(scalar, prime)})
            data["live_linear_common_prime_checks"] = common_checks
            lower = scalar * Q(1, 4 * 20643840) / (max(poles)**2 + 1)**5
            assert value >= arb(lower)
            data["explicit_primitive_analytic_lower_bound"] = str(lower)
        return data

    assert B.rank() == m and delta.degree() == m
    tail_dimension = h - m
    basis = []
    residues = []
    for a in poles:
        quotient, remainder = divmod(D, T + a * a)
        assert remainder == 0
        basis.append(quotient)
        residues.append(numerator(-a * a) * quotient(-a * a))
    basis += [D * T**j for j in range(tail_dimension)]
    change = Mat([[basis[j][i] for j in range(h)] for i in range(h)])
    change_square = change.det()**2
    vandermonde_square = math.prod(
        (b * b - a * a)**2 for a, b in itertools.combinations(poles, 2)
    )
    assert change_square == vandermonde_square
    new_A_entries = [[functional(numerator * basis[i] * basis[j])[0] for j in range(h)] for i in range(h)]
    new_B_entries = [[functional(numerator * basis[i] * basis[j])[1] for j in range(h)] for i in range(h)]
    new_A, new_B = Mat(new_A_entries), Mat(new_B_entries)
    assert new_A == change.transpose() * A * change
    assert new_B == change.transpose() * B * change
    expected_B = Mat([[Q(0) for _ in range(h)] for _ in range(h)])
    for i, a in enumerate(poles):
        expected_B[i, i] = residues[i] * a**8
    assert new_B == expected_B
    K_entries = [row[:] for row in new_A_entries]
    for i, a in enumerate(poles):
        K_entries[i][i] -= residues[i] * beta[a]
    K = Mat(K_entries)
    tail_indices = list(range(m, h))
    tail_det = subset_minor(K, tail_indices)
    assert tail_det > 0
    signed_product = (-1)**(m * (m - 1) // 2) * math.prod(
        a**8 * numerator(-a * a) for a in poles
    )
    assert delta[m] == tail_det * signed_product

    max_polynomial_moment = max(0, u + 2 * h - m - 2)
    fixed_moment_denominator = math.lcm(*(
        int(moment(e).denom()) for e in range(max_polynomial_moment + 1)
    ))
    leading_clearer = fixed_moment_denominator**tail_dimension
    leading_integer = leading_clearer * delta[m]
    assert leading_integer.denom() == 1
    leading_integer = int(leading_integer.numer())
    assert leading_integer % int(scalar.denom()) == 0

    # Independently recover the whole determinant by the diagonal principal-minor identity.
    subsets = []
    delta_new = Poly([])
    for size in range(m + 1):
        for I in itertools.combinations(range(m), size):
            complement = [j for j in range(h) if j not in I]
            minor = subset_minor(K, complement)
            product = Poly([minor])
            for i in I:
                a = poles[i]
                product *= residues[i] * (beta[a] + a**8 * T)
            delta_new += product
            subsets.append((I, minor))
    assert delta_new == change_square * delta

    prime_checks = []
    forced_product = 1
    b = max(poles)
    for prime in sp.primerange(5, b + 1):
        prime = int(prime)
        if 2 * prime <= b or fixed_moment_denominator % prime == 0 or leading_integer % prime == 0:
            continue
        assert all(vp(K[i, j], prime) >= 0 for i in range(h) for j in range(h))
        assert vp(tail_det, prime) == 0
        assert all(a % prime and vp(numerator(-a * a), prime) == 0 for a in poles)
        pole_orders = [vp(D_prime(-a * a), prime) for a in poles]
        assert all(0 <= order <= 3 for order in pole_orders)
        R = sum(pole_orders)
        assert R == vp(change_square, prime)
        high = [i for i, a in enumerate(poles) if a >= prime]
        k = len(high)
        assert k >= 1
        target = m - k
        assert vp(delta[target], prime) == -9 * k
        assert vp(delta_new[target], prime) == R - 9 * k
        assert vp(scalar, prime) >= 9 * k

        # Enumerate the individual coefficient contributions to certify uniqueness of the minimum.
        term_orders = []
        for I, minor in subsets:
            if len(I) < target or not minor:
                continue
            for X_positions in itertools.combinations(I, target):
                term = minor
                for i in I:
                    a = poles[i]
                    term *= residues[i] * (a**8 if i in X_positions else beta[a])
                if term:
                    term_orders.append(vp(term, prime))
        assert min(term_orders) == R - 9 * k
        assert term_orders.count(R - 9 * k) == 1
        assert all(order == R - 9 * k or order >= R - 9 * k + 6 for order in term_orders)
        forced_product *= prime**(9 * k)
        prime_checks.append({
            "prime": prime, "high_pole_count": k,
            "pole_difference_valuations": pole_orders,
            "change_of_basis_square_valuation": R,
            "forced_original_coefficient_index": target,
            "forced_original_coefficient_valuation": -9 * k,
            "new_basis_coefficient_valuation": R - 9 * k,
            "vp_primitive_multiplier": vp(scalar, prime),
            "unique_minimum_term_count": 1,
            "all_other_terms_at_least_six_higher": True,
        })
    assert scalar >= Q(forced_product, abs(leading_integer))
    data.update({
        "new_basis": [[str(c) for c in polynomial] for polynomial in basis],
        "change_of_basis_square": str(change_square),
        "tail_dimension": tail_dimension,
        "tail_determinant": str(tail_det),
        "fixed_polynomial_moment_denominator": str(fixed_moment_denominator),
        "leading_coefficient_integer_after_fixed_clearing": str(leading_integer),
        "forced_multiplier_lower_bound": str(Q(forced_product, abs(leading_integer))),
        "prime_checks": prime_checks,
        "principal_minor_reconstruction": "passed",
    })
    if numerator == Poly([1]):
        constant = Q(1, 20643840)**h * Q(
            math.prod(math.factorial(j)**2 for j in range(1, h)), (4 * h)**(h * h)
        )
        lower = scalar * constant / (b * b + 1)**(m * h)
        assert value >= arb(lower)
        data["explicit_primitive_analytic_lower_bound"] = str(lower)
        data["explicit_gram_constant_C_h"] = str(constant)
    return data


def main():
    records = [construct(record) for record in cases()]
    prime_checks = [check for record in records for check in record.get("prime_checks", [])]
    four_way = [
        {"poles": record["effective_poles"], "h": record["h"], **check}
        for record in records for check in record.get("prime_checks", [])
        if max(check["pole_difference_valuations"]) == 3
    ]
    assert four_way
    constant_cases = [record for record in records if record["tag"] == "degree-zero-boundary"]
    assert len(constant_cases) == 3 and all(record["primitive_integer_coefficients"] == ["1"] for record in constant_cases)
    summary = {
        "status": "passed", "case_count": len(records),
        "prime_check_count": len(prime_checks),
        "colliding_prime_check_count": sum(check["change_of_basis_square_valuation"] > 0 for check in prime_checks),
        "four_way_square_collision_check_count": len(four_way),
        "fixed_numerator_cancellation_case_count": sum(bool(record["cancelled_fixed_poles"]) for record in records),
        "degree_zero_boundary_case_count": len(constant_cases),
        "live_low_dimension_linear_case_count": sum(record["tag"] == "live-low-dimension-linear" for record in records),
        "below_one_cases": [
            {"poles": record["poles"], "h": record["h"], "numerator_coefficients": record["numerator_coefficients"],
             "positive_value_ball": record["positive_value_ball"]}
            for record in records if record["strictly_below_one"]
        ],
        "four_way_square_collisions": four_way,
        "finite_boundary": "The exact cases() list; fixed m in 1..5, h=m,m+1,m+2; five fixed positive numerators on three poles; two cancellation cases; three rank-zero controls; h=1,m=5 consecutive shifts 0..8.",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "proof_boundary": "All-parameter growth is a written theorem for fixed h>=m and fixed positive numerator; h<m is not covered. No irrationality or Lean claim.",
    }
    output = HERE / "verification" / "pole-dimension-frontier-2026-10-01"
    output.mkdir(parents=True, exist_ok=True)
    (output / "certificate.json").write_text(json.dumps({**summary, "cases": records}, indent=2) + "\n", encoding="utf-8")
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
