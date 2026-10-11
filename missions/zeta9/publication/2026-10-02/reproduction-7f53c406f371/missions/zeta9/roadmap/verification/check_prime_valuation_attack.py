"""Exact finite cross-checks of the uniform proof in prime-valuation-attack.md.

Standard library only. No network, zeta evaluation, or old evidence writes.
Finite checks do not establish the asymptotic theorem.
"""
from fractions import Fraction as Q
import argparse
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def primes(x):
    return [p for p in range(2, x + 1)
            if all(p % d for d in range(2, math.isqrt(p) + 1))]


def valuation(x, p):
    assert x
    e = 0
    while x % p == 0:
        x //= p
        e += 1
    return e


def mul(a, b, cut=None, p=None):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if cut is None or i+j < cut:
                c[i+j] += x*y
    if cut is not None:
        c = c[:cut]
    if p:
        c = [x % p for x in c]
    return c


def power(a, k, p=None):
    ans = [1]
    for _ in range(k):
        ans = mul(ans, a, p=p)
    return ans


def exact_forms(n):
    """Reconstruct rational partial fractions from products, without old code."""
    pole = []
    for j in range(n+1):
        c9 = (-1)**j * math.comb(n, j)**9 * math.comb(n+j, n) * math.comb(2*n-j, n)
        series = [Q(c9)]
        for root in list(range(1, n+1)) + list(range(-2*n, -n)):
            series = mul(series, [Q(1), Q(1, -j-root)], cut=9)
        for i in range(n+1):
            if i != j:
                d = i-j
                series = mul(series, [Q((-1)**h*math.comb(8+h, h), d**h)
                                      for h in range(9)], cut=9)
        pole.append(series)
    forms = []
    for r in range(5):
        sums = [Q(0)]*10
        constant = Q(0)
        for j in range(n+1):
            local_w = power([-j*(n-j), n-2*j, 1], r)
            series = mul(pole[j], local_w, cut=9)
            for s in range(1, 10):
                c = series[9-s]
                sums[s] += c
                constant -= c*sum((Q(1, k**s) for k in range(1, j+1)), Q(0))
        assert sums[1] == 0 and all(sums[s] == 0 for s in (2, 4, 6, 8))
        forms.append([constant] + [sums[s] for s in (3, 5, 7, 9)])
    return forms


def det(rows):
    if len(rows) == 1:
        return rows[0][0]
    return sum((-1)**j*rows[0][j]*det([r[:j]+r[j+1:] for r in rows[1:]])
               for j in range(len(rows)))


def residue(q, p):
    assert q.denominator % p
    return q.numerator * pow(q.denominator, -1, p) % p


def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def trace_identity(n, p, forms):
    # H/Q is the monic product over the complementary field elements.
    roots_q = {(-j) % p for j in range(n+1)}
    quotient = [1]
    for a in range(p):
        if a not in roots_q:
            quotient = mul(quotient, [-a, 1], p=p)
    numerator = [pow(math.factorial(n), 7, p)]
    for root in list(range(1, n+1)) + list(range(-2*n, -n)):
        numerator = mul(numerator, [-root, 1], p=p)
    base = mul(numerator, power(quotient, 9, p), p=p)
    H = [0]* (p+1)
    H[1], H[p] = p-1, 1
    rows = []
    for r in range(5):
        poly = mul(base, power([0, n, 1], r, p), p=p)
        trace = [0]*len(poly)
        for i, c in enumerate(poly):
            for k in range(p-1, i+1, p-1):
                trace[i-k] = (trace[i-k]-c*math.comb(i, k)) % p
        expected = [0]*max(len(poly), 6*p+1)
        for col, exponent in ((1, 6), (2, 4), (3, 2), (4, 0)):
            coefficient = residue(forms[r][col], p)
            for i, c in enumerate(power(H, exponent, p)):
                expected[i] = (expected[i]-coefficient*c) % p
        trace, expected = trim(trace), trim(expected)
        assert trace == expected
        assert len(trace)-1 <= 8*p-7*n
        rows.append({'r': r, 'trace_degree': len(trace)-1,
                     'A3_A5_A7_A9_mod_p': [residue(x, p) for x in forms[r][1:]]})
    return {'n': n, 'p': p, 'degree_bound': 8*p-7*n, 'rows': rows}


def check_case(n, forms, N, delta3, delta4, determinant):
    rows = []
    for p in primes(7*n//2):
        if p <= n:
            continue
        k = 7*n//(2*p)
        assert all(residue(row[col], p) == 0 for row in forms for col in range(1, k+1))
        e3, e4, eD, eN = [valuation(x, p) for x in (delta3, delta4, determinant, N)]
        assert e3 >= k and e4 >= e3
        assert eN == eD+e3-2*e4
        assert eD == 3*n//(2*p)+k
        assert eN <= 3*n//(2*p)
        rows.append({'p': p, 'forced_zero_columns': k, 'v_delta3': e3,
                     'v_delta4': e4, 'v_det': eD, 'v_N': eN, 'N_bound': 3*n//(2*p)})
    return {'n': n, 'prime_checks': rows}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write-audit', action='store_true')
    args = parser.parse_args()
    fresh = []
    fresh_forms = {}
    for n in (8, 10, 12):
        forms = exact_forms(n)
        fresh_forms[n] = forms
        q = math.lcm(*range(1, n+1))**9
        A = [[x*q for x in row] for row in forms]
        assert all(x.denominator == 1 for row in A for x in row)
        A = [[int(x) for x in row] for row in A]
        low = [det([[A[i][j] for j in (1, 2, 3)] for i in I])
               for I in itertools.combinations(range(5), 3)]
        mixed = [det([[A[i][j] for j in (1, 2, 3, c)] for i in I])
                 for I in itertools.combinations(range(5), 4) for c in (0, 4)]
        d3, d4, D = math.gcd(*low), math.gcd(*mixed), abs(det(A))
        assert D*d3 % d4**2 == 0
        N = D*d3//d4**2
        fresh.append(check_case(n, forms, N, d3, d4, D))
    source = ROOT/'missions/zeta9/round7/verification/minor-smoothness-audit.json'
    frozen = []
    for case in json.loads(source.read_text(encoding='utf-8'))['cases']:
        n = case['n']
        path = ROOT/f'missions/zeta9/round6/verification/search-input-n{n}.json.gz'
        with gzip.open(path, 'rt', encoding='utf-8') as stream:
            data = json.load(stream)
        forms = [[Q(*map(int, pair)) for pair in row] for row in data['raw_monomial_vectors']]
        if n in fresh_forms:
            assert forms == fresh_forms[n]
        result = check_case(n, forms, *[int(case[k]) for k in ('N', 'delta3', 'delta4_star', 'determinant_cleared')])
        result['input_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        frozen.append(result)
    # p=11 is the smallest possible prime in the uniform theorem.
    traces = [trace_identity(8, p, fresh_forms[8]) for p in (11, 13, 17, 23, 29)]
    result = {'status': 'passed', 'scope': 'finite exact cross-check only; proof is in the accompanying note',
              'fresh_cases': fresh, 'frozen_cases': frozen, 'polynomial_trace_checks': traces,
              'minor_source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    audit_path = HERE/'prime-valuation-attack-audit.json'
    rendered = json.dumps(result, indent=2)+'\n'
    if args.write_audit:
        audit_path.write_text(rendered, encoding='utf-8')
    else:
        assert audit_path.read_text(encoding='utf-8') == rendered, 'audit file differs; rerun with --write-audit'
    print(json.dumps({'status': 'passed', 'fresh_n': [x['n'] for x in fresh],
                      'frozen_n': [x['n'] for x in frozen],
                      'prime_checks': sum(len(x['prime_checks']) for x in fresh+frozen),
                      'exact_polynomial_trace_checks': sum(len(x['rows']) for x in traces)}))


if __name__ == '__main__':
    main()
