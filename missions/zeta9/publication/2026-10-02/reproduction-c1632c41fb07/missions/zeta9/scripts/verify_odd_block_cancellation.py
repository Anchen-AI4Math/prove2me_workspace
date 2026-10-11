"""Exact finite checks of the odd-block cancellation theorem; no zeta numerics."""
from __future__ import annotations
import hashlib
import json
import math
import sys
from pathlib import Path

MISSION = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(MISSION / 'scripts'))
from verify_local_connection import (fmpq, fmpq_mat, P, valuation, prime_list,
                                     local_n_data, local_n_exponent)
sys.path.insert(0, str(MISSION / 'round5/scripts'))
from independent_round5 import mul, power_linear, compose_w


def mod(q, p):
    q = fmpq(q)
    return int(q.numer()) % p * pow(int(q.denom()) % p, -1, p) % p


def raw_poles(n):
    """Direct factor Taylor products, also valid for auxiliary odd n."""
    poles = {s: [] for s in range(1, 10)}
    for j in range(n + 1):
        a = [fmpq(1)] + [fmpq(0)] * 8
        for shift in list(range(-n, 0)) + list(range(n + 1, 2*n + 1)):
            a = mul(a, power_linear(shift-j, 1, 8), 8)
        for k in range(n + 1):
            if k != j:
                a = mul(a, power_linear(k-j, -9, 8), 8)
        for h, value in enumerate(a):
            poles[9-h].append(math.factorial(n)**7 * value)
    return poles


def harmonic(n):
    h = {s: [fmpq(0)] for s in range(1, 10)}
    for s in h:
        for j in range(1, n + 1):
            h[s].append(h[s][-1] + fmpq(1, j**s))
    return h


def local_checks():
    cases = []
    residue_count = 0
    harmonic_count = 0
    cache = {}
    # Includes blocks m=1,3,5,7 and nonempty/empty surviving residue sets.
    for n, p in [(12,7), (28,17), (40,13), (46,13), (96,19), (204,29)]:
        m, r = divmod(n, p)
        assert n % 2 == 0 and m % 2 == 1 and p*p > 7*n/2
        base = raw_poles(n)
        if m not in cache:
            cache[m] = raw_poles(m)
        small = cache[m]
        H, hm = harmonic(n), harmonic(m)
        surviving = [a for a in range(r+1) if a+r < p and 2*r-a < p]
        kappa = {a: mod(p**0*base[9][a],p)*pow(mod(small[9][0],p),-1,p)%p
                 for a in surviving}
        assert all(kappa[r-a] == -kappa[a] % p for a in surviving)
        assert all(sum(small[s],fmpq(0)) == 0 for s in (1,3,5,7,9))
        for s in range(1, 10):
            for j in range(n+1):
                assert mod(p**s*H[s][j],p) == mod(hm[s][j//p],p)
                harmonic_count += 1
        for degree in range(5):
            poles = {s: [] for s in range(1,10)}
            for j in range(n+1):
                w = compose_w([0]*degree+[1], -j, n, 8)
                for s in poles:
                    c = sum((w[h]*base[s+h][j] for h in range(10-s)),fmpq(0))
                    poles[s].append(c)
                    a, q = j % p, j // p
                    expected = (kappa[a]*pow(-a*(r-a),degree,p)*mod(small[s][q],p))%p if a in kappa else 0
                    assert mod(p**(9-s)*c,p) == expected
                    residue_count += 1
            B = -sum((poles[s][j]*H[s][j] for s in poles for j in range(n+1)),fmpq(0))
            assert mod(p**9*B,p) == 0 and valuation(B,p) >= -8
            for s in (3,5,7,9):
                assert valuation(sum(poles[s],fmpq(0)),p) >= s-8
        cases.append({'n': n, 'p': p, 'block': m, 'remainder': r,
                      'surviving_residue_count': len(surviving)})
        print('local residues checked',n,p,flush=True)
    return {'cases': cases, 'normalized_residue_checks': residue_count,
            'harmonic_reduction_checks': harmonic_count}


def matrix_checks():
    source = MISSION / 'verification/local-connection-2026-09-28/symbolic.json'
    rows = json.loads(source.read_text())['connection']
    # A direct n=2 Taylor start, independently of the connection certificate.
    base = raw_poles(2)
    h = harmonic(2)
    raw = []
    for degree in range(5):
        poles = {s: [] for s in range(1,10)}
        for j in range(3):
            w = compose_w([0]*degree+[1],-j,2,8)
            for s in poles:
                poles[s].append(sum((w[k]*base[s+k][j] for k in range(10-s)),fmpq(0)))
        B = -sum((poles[s][j]*h[s][j] for s in poles for j in range(3)),fmpq(0))
        raw.append([B]+[sum(poles[s],fmpq(0)) for s in (3,5,7,9)])
    F = fmpq_mat(raw)
    column_checks = 0
    modulus_cases = []
    for n in range(2,301,2):
        selected = n in (12,28,40,46,96,192,204,234,258,300)
        data = local_n_data(F) if selected else None
        for p in prime_list(n):
            if p*p <= 7*n/2:
                continue
            m, r = divmod(n,p)
            g = int(3*r >= 2*p-1)
            h = max(g,m%2)
            lower = [h-9,h-6,h-4,h-2,h]
            actual = [min(valuation(F[i,j],p) for i in range(5)) for j in range(5)]
            assert all(a >= b for a,b in zip(actual,lower))
            column_checks += 5
            if selected:
                D = valuation(F.det(),p)
                exponent = local_n_exponent(data,p)
                assert exponent <= 30+D-5*h
                modulus_cases.append({'n':n,'p':p,'block':m,'column_valuations':actual,
                                      'N_exponent':exponent,'new_bound':30+D-5*h})
        if n<300:
            F = fmpq_mat([[fmpq(P([int(c) for c in e['numerator']])(n),
                                   P([int(c) for c in e['denominator']])(n))
                          for e in row] for row in rows])*F
    return {'column_checks':column_checks, 'modulus_cases':modulus_cases,
            'connection_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}


def main():
    result = {'status':'passed','local_checks':local_checks(),'matrix_checks':matrix_checks(),
              'warning':'Finite checks are diagnostics; the all-parameter proof is in the companion note.',
              'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out = MISSION/'verification/odd-block-cancellation-2026-09-29'
    out.mkdir(parents=True,exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('passed',result['matrix_checks']['column_checks'],'column checks',flush=True)


if __name__ == '__main__':
    main()
