"""Exact minimum L1 height in the two-dimensional degree-4 cancellation lattice.

This is a finite certificate, not an asymptotic obstruction. No zeta values are
used in Gauss reduction, enumeration, or selection of the shortest L1 vector.
"""
from __future__ import annotations
import gzip
import hashlib
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from independent_round5 import ROOT, OUT, iv
from flint import arb, ctx, fmpq, fmpz_mat


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def nearest(q):
    return (2*q.numerator + q.denominator) // (2*q.denominator)


def floor_sqrt_rational(q):
    assert q >= 0
    return math.isqrt(q.numerator // q.denominator)


def gauss(basis):
    b = [list(v) for v in basis]
    transform = [[1, 0], [0, 1]]
    while True:
        if dot(b[1], b[1]) < dot(b[0], b[0]):
            b.reverse()
            transform.reverse()
        q = nearest(Fraction(dot(b[0], b[1]), dot(b[0], b[0])))
        if not q:
            break
        b[1] = [y-q*x for x, y in zip(b[0], b[1])]
        transform[1] = [y-q*x for x, y in zip(transform[0], transform[1])]
    T = fmpz_mat(transform)
    assert abs(int(T.det())) == 1
    assert T * fmpz_mat(basis) == fmpz_mat(b)
    assert 2 * abs(dot(*b)) <= dot(b[0], b[0]) <= dot(b[1], b[1])
    return b, transform


def audit(n):
    path = OUT / f'weighted-p9-n{n}-m{n}-R4.json.gz'
    with gzip.open(path, 'rt', encoding='utf-8') as stream:
        data = json.load(stream)
    basis = [list(map(int, row)) for row in data['low_hnf']['basis']]
    assert len(basis) == 2 and int(data['full_hnf']['rank']) == 5
    b, transform = gauss(basis)
    A, B, C = dot(b[0], b[0]), dot(*b), dot(b[1], b[1])
    determinant = A*C-B*B
    assert determinant > 0
    initial = min(sum(map(abs, v)) for v in b)
    # If ||x b0 + y b1||_1 <= H, then its squared Euclidean norm <= H^2.
    # Cauchy-Schwarz in the Gram metric gives |x| <= H sqrt(G^-1_00),
    # and similarly for y. Thus this finite rectangle covers every improvement.
    bx = floor_sqrt_rational(Fraction(initial**2 * C, determinant))
    by = floor_sqrt_rational(Fraction(initial**2 * A, determinant))
    best = None
    minima = []
    examined = 0
    for x, y in itertools.product(range(-bx, bx+1), range(-by, by+1)):
        if not (x or y) or (x < 0 or (x == 0 and y < 0)):
            continue
        v = [x*a+y*c for a, c in zip(*b)]
        norm = sum(map(abs, v))
        examined += 1
        if best is None or norm < best:
            best, minima = norm, [dict(combo=[x, y], W=list(map(str, v)))]
        elif norm == best:
            minima.append(dict(combo=[x, y], W=list(map(str, v))))
    assert best is not None and best <= initial
    with ctx.workprec(256):
        height = arb(best).log()/n
        assert height.lower() > arb(fmpq(13, 10)).upper()
        return dict(n=n, R=4, p=9,
                    source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                    saturated_kernel_basis=[list(map(str, v)) for v in basis],
                    gauss_basis=[list(map(str, v)) for v in b],
                    unimodular_transform=[list(map(str, v)) for v in transform],
                    gram=[str(A), str(B), str(C)], gram_determinant=str(determinant),
                    initial_L1=str(initial), exhaustive_rectangle=[bx, by],
                    sign_canonical_vectors_examined=examined,
                    exact_minimum_nonzero_W_L1=str(best), minimizers=minima,
                    log_minimum_L1_per_n=iv(height),
                    every_nonzero_integer_cancelling_W_exceeds_finite_1_30_threshold=True,
                    asymptotic_conclusion=False)


def main():
    rows = [audit(n) for n in (12, 24, 48)]
    (OUT / 'independent-height-barrier.json').write_text(
        json.dumps(dict(status='passed', scope='finite n only; all integer W of degree at most 4',
                        checks=rows), indent=2)+'\n', encoding='utf-8')
    print(json.dumps([dict(n=r['n'], minimum_log_height=r['log_minimum_L1_per_n'],
                           exhaustive_rectangle=r['exhaustive_rectangle']) for r in rows]))


if __name__ == '__main__':
    main()
