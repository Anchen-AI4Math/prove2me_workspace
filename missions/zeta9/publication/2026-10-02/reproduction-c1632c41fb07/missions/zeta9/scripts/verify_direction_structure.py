"""Exact algebra for fixed rational filters and adjacent zero-row structure.

No irrationality assertion, large lattice scan, or Lean invocation.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
import hashlib
import json
import math
import sys

MISSION = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(MISSION / 'scripts'))
from verify_local_connection import fmpq, fmpq_mat, QP, determinant
from probe_exterior_cone import connection, ENT


def mod2(a, b):
    while a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def mul2(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        b >>= 1
    return result


def gcd2(a, b):
    while b:
        a, b = b, mod2(a, b)
    return a


def irreducible_degree5_mod2(coefficients):
    f = sum((int(a) & 1) << i for i, a in enumerate(coefficients))
    assert f.bit_length() == 6
    xpower = 2
    remainders = []
    for j in range(1, 6):
        xpower = mod2(mul2(xpower, xpower), f)
        remainders.append(xpower)
    # Rabin's criterion for prime degree 5: x^(2^5)=x, gcd(x^2-x,f)=1.
    assert xpower == 2 and gcd2(remainders[0] ^ 2, f) == 1
    return {'binary_polynomial': f, 'frobenius_remainders': remainders,
            'gcd_x2_minus_x': 1, 'irreducible': True}


def rational_det(rows):
    return Q(str(fmpq_mat([[fmpq(str(a)) for a in row] for row in rows]).det()))


def binomial(a, k):
    return Q(math.prod(a - j for j in range(k)), math.factorial(k))


def matrix_denominator(a):
    return math.lcm(*(int(a[i, j].denom()) for i in range(a.nrows())
                      for j in range(a.ncols())))


def arithmetic_smoke():
    sys.path.insert(0, str(MISSION / 'round6/scripts'))
    from independent_audit import independent_columns
    matrices = {2: fmpq_mat(independent_columns(2))}
    for n in (2, 4):
        matrices[n + 2] = connection(n) * matrices[n]
    assert matrices[6] == fmpq_mat(independent_columns(6))
    cases = []
    for theta in (fmpq(0), fmpq(1), fmpq(2, 3), fmpq(100, 97)):
        previous = None
        for n in (2, 4, 6):
            f = matrices[n]
            assert all(f[i, 4].denom() == 1 for i in range(5))
            inverse = f.inv()
            row = [inverse[4, j] - theta * inverse[0, j] for j in range(5)]
            assert sum((row[j] * f[j, 4] for j in range(5)), fmpq(0)) == 1
            mu = math.lcm(*(int(a.denom()) for a in row))
            integers = [int(mu * a) for a in row]
            assert math.gcd(*integers) == 1
            if previous:
                old_n, old_mu = previous
                a = matrix_denominator(connection(old_n))
                b = matrix_denominator(connection(old_n).inv())
                assert (b * old_mu) % mu == 0
                assert (a * mu) % old_mu == 0
            cases.append({'theta': str(theta), 'n': n, 'denominator_mu': str(mu),
                          'primitive': True})
            previous = n, mu
    return cases


def main():
    source = MISSION / 'verification/second-mode-direction-2026-09-29/certificate.json'
    old = json.loads(source.read_text())
    g = fmpq_mat([[fmpq(a) for a in row] for row in old['G']])
    # Reconstruct the limiting G from the current actual rational connection.
    leading = []
    for i, row in enumerate(ENT):
        line = []
        for j, (a, b) in enumerate(row):
            degree = a.degree() - b.degree() + 2 * j - 2 * i
            assert degree <= 0
            line.append(fmpq(a.leading_coefficient(), b.leading_coefficient())
                        if degree == 0 else fmpq(0))
        leading.append(line)
    assert g == fmpq_mat(leading).inv()
    characteristic = determinant([[QP([-g[i, j], int(i == j)])
                                   for j in range(5)] for i in range(5)])
    assert list(map(str, characteristic)) == old['characteristic']
    den = math.lcm(*(int(a.denom()) for a in characteristic))
    q_int = [int(a * den) for a in characteristic]
    content = math.gcd(*q_int)
    q_int = [a // content for a in q_int]
    h_cert = irreducible_degree5_mod2(old['h_coefficients'])
    q_cert = irreducible_degree5_mod2(q_int)
    # Exact Cayley-Hamilton: integer Q(G)=0.
    value = fmpq_mat(5, 5)
    identity = fmpq_mat([[int(i == j) for j in range(5)] for i in range(5)])
    for coefficient in reversed(q_int):
        value = value * g + coefficient * identity
    assert value == fmpq_mat(5, 5)
    # Monic h/(y-u) coefficients, ordered from constant to y^4, in basis 1,u,...,u^4.
    h = [Q(a, 7) for a in old['h_coefficients']]
    coefficient_basis = [[h[j + 1 + t] if j + 1 + t <= 5 else Q(0)
                          for t in range(5)] for j in range(5)]
    assert rational_det(coefficient_basis) == 1
    # Leading determinant identity for every subset of coordinate columns.
    minors = []
    for r in range(1, 6):
        R = r * (r - 1) // 2
        for js in combinations(range(5), r):
            exponents = [5 - 2 * j for j in js]
            vandermonde_j = math.prod(js[b] - js[a] for a in range(r) for b in range(a + 1, r))
            lhs = rational_det([[binomial(exponent, ell) for exponent in exponents]
                                for ell in range(r)])
            expected = Q((-2) ** R * vandermonde_j,
                         math.prod(math.factorial(ell) for ell in range(r)))
            assert lhs == expected
            minors.append({'columns': list(js), 'power_of_n': 5 * r - 2 * sum(js) - R,
                           'consecutive_leading_integer': (-4) ** R * vandermonde_j})
    assert minors[-1]['power_of_n'] == -5
    assert minors[-1]['consecutive_leading_integer'] == 301989888
    # Difference-filter constants at highest coordinate, a=-3.
    stencil = []
    for m in range(13):
        assert binomial(-3, m) == (-1) ** m * math.comb(m + 2, 2)
        # The mth forward difference moment: all lower powers vanish.
        for ell in range(m + 1):
            moment = sum((-1) ** (m - r) * math.comb(m, r) * r ** ell
                         for r in range(m + 1))
            assert moment == (math.factorial(m) if ell == m else 0)
        stencil.append({'root_multiplicity': m,
                        'coefficient_of_lambda_power_times_P_derivative':
                        str(2 ** m * binomial(-3, m)), 'n_power': -3 - m})
    result = {'status': 'passed', 'h_mod2': h_cert, 'characteristic_integer': q_int,
              'characteristic_mod2': q_cert, 'actual_limit_reconstructed': True,
              'Cayley_Hamilton_exact': True, 'eigenvector_coefficient_basis_determinant': '1',
              'all_31_coordinate_minors': minors, 'stencil_identity_smoke': stencil,
              'rational_row_denominator_smoke': arithmetic_smoke(),
              'claim_boundary': 'Exact algebra plus written all-order recurrence proof; no irrationality or asymptotic finite-sample claim.',
              'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out = MISSION / 'verification/direction-structure-2026-09-30'
    out.mkdir(parents=True, exist_ok=True)
    (out / 'certificate.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: two irreducibility certificates, exact actual-limit reconstruction, 31 Casoratian minor constants, fixed-filter identities, 12 rational denominator cases.')


if __name__ == '__main__':
    main()
