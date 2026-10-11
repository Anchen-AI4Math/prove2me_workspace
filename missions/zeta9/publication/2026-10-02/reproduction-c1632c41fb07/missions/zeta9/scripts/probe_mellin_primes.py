"""Exact finite audit of Mellin-Gram denominators for E={0,...,D}.

Uses SymPy rational arithmetic only.  For every D<=12 it computes the Schur
complement q=Q/P in lowest terms, examines specified prime valuations, and checks the predicted
anti-diagonal residue of p^9 C modulo primes D<p<=2D.

Run from the zeta9 directory with:
  C:/Users/anche/AppData/Local/Programs/Python/Python312/python.exe \
    scripts/probe_mellin_primes.py
"""
from __future__ import annotations

import hashlib
import json
from math import gcd, lcm
from pathlib import Path

import sympy as sp


MAX_D = 12
MISSION = Path(__file__).resolve().parents[1]


def vp(n: int, p: int) -> int:
    n = abs(n)
    k = 0
    while n and n % p == 0:
        n //= p
        k += 1
    return k


def vp_rat(x: sp.Rational, p: int) -> int:
    x = sp.Rational(x)
    if not x:
        return 10**9
    return vp(int(sp.numer(x)), p) - vp(int(sp.denom(x)), p)


def mod_fraction(x: sp.Rational, p: int) -> int:
    """Reduce a p-integral rational modulo p."""
    num, den = int(x.p), int(x.q)
    assert den % p
    return (num % p) * pow(den % p, -1, p) % p


def rank_mod(matrix: list[list[int]], p: int) -> int:
    a = [[x % p for x in row] for row in matrix]
    if not a:
        return 0
    rows, cols = len(a), len(a[0])
    r = 0
    for c in range(cols):
        pivot = next((i for i in range(r, rows) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][c], -1, p)
        a[r] = [(v * inv) % p for v in a[r]]
        for i in range(rows):
            if i != r and a[i][c]:
                t = a[i][c]
                a[i] = [(u - t * v) % p for u, v in zip(a[i], a[r])]
        r += 1
        if r == rows:
            break
    return r


def det_mod(matrix: list[list[int]], p: int) -> int:
    a = [[x % p for x in row] for row in matrix]
    n = len(a)
    det = 1
    for c in range(n):
        pivot = next((i for i in range(c, n) if a[i][c]), None)
        if pivot is None:
            return 0
        if pivot != c:
            a[c], a[pivot] = a[pivot], a[c]
            det = -det
        v = a[c][c]
        det = det * v % p
        inv = pow(v, -1, p)
        for i in range(c + 1, n):
            if a[i][c]:
                t = a[i][c] * inv % p
                for j in range(c + 1, n):
                    a[i][j] = (a[i][j] - t * a[c][j]) % p
    return det % p


def main() -> None:
    H = [sp.S.Zero]
    for k in range(1, 2 * MAX_D + 1):
        H.append(H[-1] + sp.Rational(1, k**9))

    records = []
    q_by_degree = [sp.Rational(0)]
    for D in range(1, MAX_D + 1):
        # C is the Gram matrix of x^i-1, 1<=i<=D; b_i=-H_i.
        C = sp.Matrix([
            [H[i] + H[j] - H[i + j] for j in range(1, D + 1)]
            for i in range(1, D + 1)
        ])
        b = sp.Matrix([-H[i] for i in range(1, D + 1)])
        # Clear the common harmonic denominator, then use a bordered
        # determinant identity. This is substantially faster than a dense
        # rational inverse at the top of the requested range.
        L = lcm(*range(1, 2 * D + 1)) ** 9
        Ci = C.applyfunc(lambda x: int(x * L))
        bi = b.applyfunc(lambda x: int(x * L))
        detC = Ci.det(method="domain-ge")
        bordered = sp.zeros(D + 1)
        bordered[1:, 1:] = Ci
        bordered[0, 1:] = bi.T
        bordered[1:, 0] = bi
        det_border = bordered.det(method="domain-ge")
        q = sp.Rational(-det_border, detC * L)
        q_by_degree.append(q)
        P, Q = int(sp.denom(q)), int(sp.numer(q))
        assert P > 0 and gcd(P, Q) == 1
        local = []
        for p in sp.primerange(D + 1, 2 * D + 1):
            scaled = [[mod_fraction(sp.Rational(p**9) * C[i, j], p)
                       for j in range(D)] for i in range(D)]
            staircase = [[(-1 if i + j + 2 >= p else 0) % p
                          for j in range(D)] for i in range(D)]
            assert scaled == staircase, (D, p, scaled, staircase)
            expected_rank = max(0, 2 * D - p + 1)
            actual_rank = rank_mod(scaled, p)
            assert actual_rank == expected_rank, (D, p, actual_rank, expected_rank)
            k = p - D - 1
            if k:
                Ck_rat = C[:k, :k]
                Ck = [[mod_fraction(Ck_rat[i, j], p) for j in range(k)] for i in range(k)]
                low_det = det_mod(Ck, p)
                det_Ck = Ck_rat.det(method="domain-ge")
            else:
                low_det = 1
                det_Ck = sp.S.One
            a = vp_rat(det_Ck, p)
            # For D<p<=2D, v_p(L)=1, so v_p(det C)=v_p(det Ci)-9D.
            det_valuation = vp(int(detC), p) - 9 * D
            qk = q_by_degree[k]
            difference = sp.factor(q - qk)
            difference_valuation = vp_rat(difference, p)
            assert a >= 0
            if a < 9:
                assert difference_valuation >= 9 - 2 * a, (D, p, a, difference_valuation)
            Pk_valuation = vp(int(sp.denom(qk)), p)
            refined_difference_bound = 9 - a - Pk_valuation
            if a < 9:
                assert Pk_valuation <= a
                assert difference_valuation >= refined_difference_bound, (
                    D, p, a, Pk_valuation, difference_valuation, refined_difference_bound
                )
                assert vp(P, p) == Pk_valuation, (D, p, a, vp(P, p), Pk_valuation)
            descent_holds = False
            if low_det:
                assert det_valuation == -9 * expected_rank
                descent_holds = difference_valuation >= 9
                assert descent_holds, (D, p, k, difference)
                assert P % p != 0
            local.append({
                "p": p,
                "rank_p9C_mod_p": actual_rank,
                "predicted_rank": expected_rank,
                "k": k,
                "det_Ck_mod_p": low_det,
                "a=v_p_det_Ck": a,
                "v_p(qk)": vp_rat(qk, p),
                "v_p(qD_minus_qk)": difference_valuation,
                "q_difference_lower_bound": refined_difference_bound if a < 9 else None,
                "v_p(Pk)": Pk_valuation,
                "denominator_recursion_verified": a < 9,
                "v_p_det_C": det_valuation,
                "qD_congruent_qk_mod_p9": descent_holds if low_det else None,
                "v_p(P)": vp(P, p),
                "p_divides_P": vp(P, p) > 0,
                "staircase_rows": [
                    "".join("1" if i + j + 2 >= p else "." for j in range(D))
                    for i in range(D)
                ],
            })

        records.append({
            "D": D,
            "P": str(P),
            "Q": str(Q),
            "P_digits": len(str(P)),
            "tested_primes_D_lt_p_le_2D": local,
        })

    out = {
        "scope": "Exact rational consecutive Mellin Gram cases D=1,...,12",
        "definitions": "q=b^T C^{-1} b, C_ij=H_i+H_j-H_(i+j), b_i=-H_i, q=Q/P reduced",
        "local_check": "p^9 C mod p = -1_{i+j>=p}; rank=2D-p+1 for D<p<=2D",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "records": records,
        "all_checks": "PASS",
    }
    dest = MISSION / "verification" / "mellin-prime-audit-2026-09-30"
    dest.mkdir(parents=True, exist_ok=True)
    cert = dest / "certificate.json"
    cert.write_text(json.dumps(out, indent=2), encoding="utf-8")

    print("D | p:k, det(C_k) mod p, rank(p^9 C mod p), v_p(P), qD-qk in p^9 Z_p")
    for row in records:
        entries = []
        for x in row["tested_primes_D_lt_p_le_2D"]:
            congr = "yes" if x["qD_congruent_qk_mod_p9"] else ("n/a" if x["qD_congruent_qk_mod_p9"] is None else "no")
            entries.append(f"{x['p']}:{x['k']},{x['det_Ck_mod_p']},{x['rank_p9C_mod_p']},{x['v_p(P)']},{congr}")
        print(f"{row['D']:2d} | " + ("; ".join(entries) if entries else "—"))
    print("PASS", cert)


if __name__ == "__main__":
    main()
