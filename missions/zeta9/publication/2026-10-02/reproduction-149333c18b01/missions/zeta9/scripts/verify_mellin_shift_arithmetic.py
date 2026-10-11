"""Exact finite checks for the written Mellin right-shift obstruction.

Only Python's standard library is required. These checks do not verify the
PNT or the asymptotic theorem, and do not claim Lean verification.
"""
from __future__ import annotations

from fractions import Fraction as Q
from hashlib import sha256
from math import comb, factorial, gcd, lcm
from pathlib import Path
import json


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification/mellin-shift-arithmetic-2026-10-01"


def det_solve(matrix, rhs=None):
    """Rational elimination; the input matrices have positive leading minors."""
    n = len(matrix)
    a = [list(map(Q, row)) + ([Q(rhs[i])] if rhs is not None else [])
         for i, row in enumerate(matrix)]
    determinant = Q(1)
    for k in range(n):
        pivot = a[k][k]
        assert pivot > 0, (k, pivot)
        determinant *= pivot
        for i in range(k + 1, n):
            multiplier = a[i][k] / pivot
            a[i][k] = Q(0)
            for j in range(k + 1, n + (rhs is not None)):
                a[i][j] -= multiplier * a[k][j]
    if rhs is None:
        return determinant
    solution = [Q(0)] * n
    for i in range(n - 1, -1, -1):
        solution[i] = (a[i][n] - sum(a[i][j] * solution[j]
                                   for j in range(i + 1, n))) / a[i][i]
    return determinant, solution


def primes_upto(n):
    sieve = bytearray(b"\x01") * (n + 1)
    if n >= 0:
        sieve[0] = 0
    if n >= 1:
        sieve[1] = 0
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p:n + 1:p] = b"\x00" * (((n - p * p) // p) + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def vp(n, p):
    count = 0
    while n and n % p == 0:
        count += 1
        n //= p
    return count


def dfact_vp(n, p):
    answer = 0
    while n:
        n //= p
        answer += n
    return answer


def interval_check(N, t):
    ell = lcm(*range(N + 1, N + t + 1))
    dt = lcm(*range(1, t + 1))
    binomial = comb(N + t, t)
    assert binomial * dt % ell == 0
    checked = 0
    for p in primes_upto(N + t):
        k = max(vp(j, p) for j in range(N + 1, N + t + 1))
        a0 = vp(dt, p)
        exponent = (dfact_vp(N + t, p) - dfact_vp(N, p)
                    - dfact_vp(t, p))
        assert k <= a0 + exponent
        for a in range(a0 + 1, k + 1):
            power = p ** a
            assert power > t
            assert (N + t) // power - N // power - t // power == 1
            checked += 1
    return checked


def harmonic_table(n):
    values = [Q(0)]
    for j in range(1, n + 1):
        values.append(values[-1] + Q(1, j ** 9))
    return values


def beta_bound(N, D):
    answer = Q(1, factorial(8) ** D)
    for k in range(D):
        answer *= Q(factorial(k) * factorial(k + 9)
                    * factorial(k + N - 4) * factorial(k + N + 5),
                    factorial(2 * k + N + 5) * factorial(2 * k + N + 6))
    return answer


def beta_matrix(N, D):
    return [[Q(factorial(N - 4 + i + j) * factorial(9),
               factorial(N + 6 + i + j))
             for j in range(D)] for i in range(D)]


def difference_matrix(C):
    D = len(C)
    def entry(i, j):
        return C[i][j] if min(i, j) >= 0 else Q(0)
    return [[entry(i, j) - entry(i - 1, j) - entry(i, j - 1)
             + entry(i - 1, j - 1) for j in range(D)] for i in range(D)]


def schur_check(M, offsets):
    N, W, d = 2 * M, max(offsets), len(offsets)
    H = harmonic_table(N + 2 * W)
    h = H[N]
    b = [h - H[N + i] for i in offsets]
    C = [[H[N + i] + H[N + j] - H[N + i + j] - h
          for j in offsets] for i in offsets]
    determinant, solution = det_solve(C, b)
    r = sum(x * y for x, y in zip(b, solution))
    q = h + r
    assert r > 0
    P, R, T = q.denominator, r.denominator, h.denominator
    assert (T * R) % P == 0 and (P * R) % T == 0

    ell = lcm(*range(N + 1, N + 2 * W + 1))
    L = ell ** 9
    A = [[L * x for x in row] for row in C]
    v = [L * x for x in b]
    assert all(x.denominator == 1 for row in A for x in row)
    assert all(x.denominator == 1 for x in v)
    detA = det_solve(A)
    assert detA == L ** d * determinant and detA.denominator == 1
    multiplier = L * detA.numerator
    assert multiplier % R == 0 and (multiplier * r).denominator == 1

    product_a = 1
    for index, i in enumerate(offsets):
        product_a *= i
        entry = sum(Q(1, (N + k) ** 9) - Q(1, (N + i + k) ** 9)
                    for k in range(1, i + 1))
        assert C[index][index] == entry
        assert entry <= Q(i, (N + 1) ** 9)
        assert entry <= Q(9 * i * i, (N + 1) ** 10)
    diagonal0 = Q(product_a, (N + 1) ** (9 * d))
    diagonal1 = Q(9 ** d * product_a ** 2, (N + 1) ** (10 * d))
    assert determinant <= diagonal0 and determinant <= diagonal1
    B = min(diagonal0, diagonal1)
    beta_checked = False
    if offsets == list(range(1, d + 1)) and N >= 4:
        exact_beta = beta_bound(N, d)
        G = beta_matrix(N, d)
        assert det_solve(G) == exact_beta * factorial(8) ** d
        Cp = difference_matrix(C)
        assert det_solve(Cp) == determinant
        gap = [[G[i][j] / factorial(8) - Cp[i][j]
                for j in range(d)] for i in range(d)]
        assert det_solve(gap) > 0
        assert determinant <= exact_beta
        rough = Q(1, factorial(8) ** d * (N - 3) ** (d * d + 9 * d))
        for k in range(d):
            rough *= factorial(k) * factorial(k + 9)
        assert exact_beta <= rough
        B = min(B, exact_beta)
        beta_checked = True
    U = L ** (d + 1) * B
    assert U >= R >= 1
    assert P * U >= T
    simple_lcm = comb(N + 2 * W, 2 * W) * lcm(*range(1, 2 * W + 1))
    assert simple_lcm % ell == 0
    Ubinomial = simple_lcm ** (9 * (d + 1)) * B
    assert Ubinomial >= U
    prime_base = 1
    for p in primes_upto(N):
        if p > M:
            prime_base *= p ** 9
            assert vp(T, p) == 9
    assert T % prime_base == 0 and P * U >= prime_base

    # The Jacobi lower error bound is rational and requires no zeta evaluation.
    error_denominator = 1
    for j in range(1, 9):
        error_denominator *= (W + j) * (W + N + j)
    lower_primitive = Q(5040 * P, error_denominator)
    return {"M": M, "offsets": offsets, "dimension": d, "width": W,
            "P": str(P), "R": str(R), "T": str(T),
            "L_det_A": str(multiplier),
            "U_numerator": str(U.numerator), "U_denominator": str(U.denominator),
            "beta_comparison_checked": beta_checked,
            "primitive_error_lower_numerator": str(lower_primitive.numerator),
            "primitive_error_lower_denominator": str(lower_primitive.denominator),
            "primitive_error_lower_at_least_one": lower_primitive >= 1,
            "q_hash": sha256(f"{q.numerator}/{q.denominator}".encode()).hexdigest()}


def main():
    interval_count = 0
    prime_term_count = 0
    for N in list(range(61)) + [97, 128, 255, 997, 4096]:
        for t in range(1, 25):
            prime_term_count += interval_check(N, t)
            interval_count += 1
    consecutive = [schur_check(M, list(range(1, D + 1)))
                   for M in [0, 1, 2, 4, 8, 16, 32, 64, 128]
                   for D in range(1, 7)]
    sparse = [schur_check(M, offsets)
              for M in [0, 1, 2, 8, 32, 128]
              for offsets in [[1, 4, 7], [2, 5, 9], [1, 9], [3, 11, 15]]]
    sources = [Path(__file__), ROOT / "research/mellin-shift-arithmetic-2026-10-01.md"]
    certificate = {
        "result": "PASS", "date": "2026-10-01", "arithmetic": "exact Fraction/int",
        "boundary": "finite checks; written proofs plus PNT establish asymptotics; no Lean",
        "interval_lcm_checks": interval_count,
        "high_prime_power_binomial_terms": prime_term_count,
        "consecutive_schur_cases": len(consecutive),
        "sparse_schur_cases": len(sparse),
        "beta_determinant_and_positive_comparison_cases": sum(
            item["beta_comparison_checked"] for item in consecutive),
        "sources": {str(p.relative_to(ROOT)).replace("\\", "/"):
                    sha256(p.read_bytes()).hexdigest() for p in sources},
        "consecutive": consecutive, "sparse": sparse,
    }
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "certificate.json").write_text(
        json.dumps(certificate, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in certificate.items()
                      if k not in {"consecutive", "sparse", "sources"}}, indent=2))


if __name__ == "__main__":
    main()
