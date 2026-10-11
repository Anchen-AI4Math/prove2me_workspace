"""Exact checks for harmonic denominator blocks and perturbation stability.

The asymptotic theorem is proved in the companion note using PNT.
This script uses only the Python standard library and performs no networking.
"""
from fractions import Fraction as F
from pathlib import Path
from math import gcd, isqrt, lcm
import hashlib
import json

MISSION = Path(__file__).resolve().parents[1]


def primes(limit):
    composite = bytearray(limit + 1)
    result = []
    for p in range(2, limit + 1):
        if composite[p]:
            continue
        result.append(p)
        for j in range(p * p, limit + 1, p):
            composite[j] = 1
    return result


def valuation_int(n, p):
    if n == 0:
        raise ValueError('Use an explicit zero branch, not an infinite sentinel.')
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def valuation(q, p):
    return valuation_int(q.numerator, p) - valuation_int(q.denominator, p)


def check_perturbation(h, r):
    q = h + r
    a, b, c = h.denominator, r.denominator, q.denominator
    assert (b * c) % a == 0 and (a * b) % c == 0
    assert a <= b * c and c <= a * b
    return {'h': str(h), 'r': str(r), 'q': str(q),
            'den_h': str(a), 'den_r': str(b), 'den_q': str(c),
            'two_divisibilities': True}


def main():
    max_n = 256
    ps = primes(max_n)
    blocks = 0
    units = 0
    exceptions = []
    perturbation_cases = 0
    displayed = []
    for s in (1, 3, 5, 7, 9):
        hs = [F(0)]
        ell = 1
        for n in range(1, max_n + 1):
            h = hs[-1] + F(1, n ** s)
            hs.append(h)
            ell = lcm(ell, n)
            assert ell ** s % h.denominator == 0
            for p in ps:
                if p <= isqrt(n) or p > n:
                    continue
                k = n // p
                assert k < p
                delta = p ** s * h - hs[k]
                assert delta == p ** s * sum(
                    (F(1, j ** s) for j in range(1, n + 1) if j % p), F(0))
                assert delta.denominator % p != 0
                assert delta.numerator % (p ** s) == 0
                blocks += 1
                if hs[k].numerator % p:
                    assert valuation(h, p) == -s
                    units += 1
                else:
                    exceptions.append({'s': s, 'N': n, 'p': p, 'k': k,
                                       'v_p_H_N': valuation(h, p),
                                       'H_k': str(hs[k])})
            for r in (F(0), F(1, n + 1), F(-1, 2 * n + 1),
                      F(10 ** 20 + n, n + 2), -h, F(1) - h):
                record = check_perturbation(h, r)
                perturbation_cases += 1
                if s == 9 and n in (2, 40, 128, 256) and r in (F(1, n + 1), -h):
                    displayed.append(record)
    counterexample = next(e for e in exceptions
                          if (e['s'], e['N'], e['p'], e['k']) == (9, 40, 19, 2))
    assert counterexample['v_p_H_N'] == -8
    source = MISSION / 'research/harmonic-denominator-stability-2026-10-01.md'
    out = MISSION / 'verification/harmonic-denominator-stability-2026-10-01'
    out.mkdir(parents=True, exist_ok=True)
    certificate = {'status': 'PASS', 'max_N': max_n, 's_values': [1, 3, 5, 7, 9],
                   'harmonic_denominator_divisibility_cases': 5 * max_n,
                   'exact_prime_block_checks': blocks, 'unit_prime_block_checks': units,
                   'exception_count': len(exceptions), 'exceptional_blocks': exceptions,
                   'perturbation_divisibility_cases': perturbation_cases,
                   'displayed_perturbations': displayed,
                   'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   'note_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                   'boundary': 'Finite exact checks only. The all-N denominator asymptotic uses the written proof and standard PNT; no Lean or irrationality claim.'}
    (out / 'certificate.json').write_text(json.dumps(certificate, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: certificate[k] for k in
                      ('status', 'exact_prime_block_checks', 'unit_prime_block_checks',
                       'exception_count', 'perturbation_divisibility_cases')}))


if __name__ == '__main__':
    main()
