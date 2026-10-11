"""Root review of archived coefficients, saturated lattices and Arb intervals."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from independent_round5 import ROOT, OUT, iv, qpair, scale, product_form, direct_sum_audit
from flint import arb, ctx, fmpq, fmpq_poly, fmpz_mat


def Q(pair):
    return fmpq(int(pair[0]), int(pair[1]))


def integers(rows):
    return [list(map(int, row)) for row in rows]


def matrix(rows, cols):
    return fmpz_mat(rows) if rows else fmpz_mat(0, cols)


def saturation_by_minors(rows, ambient):
    """An independent saturation test, without recomputing HNF transforms."""
    d = len(rows)
    if not d:
        return dict(rank=0, gcd_maximal_minors=1, minors_examined=0)
    assert matrix(rows, ambient).rank() == d
    g, count = 0, 0
    for choice in itertools.combinations(range(ambient), d):
        sub = fmpz_mat([[row[j] for j in choice] for row in rows])
        g = math.gcd(g, int(sub.det()))
        count += 1
        if g == 1:
            break
    assert g == 1
    return dict(rank=d, gcd_maximal_minors=g, minors_examined=count)


def archived_polynomial_identities(data):
    p, n, m, R = (int(data[k]) for k in ('p', 'n', 'm', 'R'))
    t = fmpq_poly([0, 1])
    u = t * (t + n)
    numerator = fmpq_poly([scale(p, n, [(m, 10 - p)])])
    for shift in list(range(-m, 0)) + list(range(n + 1, n + m + 1)):
        numerator *= (t + shift) ** (10 - p)
    denominator = fmpq_poly([1])
    for j in range(n + 1):
        denominator *= (t + j) ** p
    divisors = {}
    for j in range(n + 1):
        for s in range(1, p + 1):
            quot, rem = divmod(denominator, (t + j) ** s)
            assert not rem
            divisors[j, s] = quot
    polys = data['monomial_pole_coefficients_r_by_j_by_s1_to_p']
    for r in range(R + 1):
        reconstructed = fmpq_poly([0])
        for j in range(n + 1):
            for s in range(1, p + 1):
                reconstructed += Q(polys[r][j][s - 1]) * divisors[j, s]
        assert reconstructed == numerator, (data['case_id'], r)
        numerator *= u
    return R + 1


def interval_bounds(saved):
    mid, radius, exponent = int(saved['mid']), int(saved['rad']), int(saved['exp'])
    unit = fmpq(10) ** exponent
    return (mid - radius) * unit, (mid + radius) * unit


def audit(path, do_direct=False):
    start = time.monotonic()
    with gzip.open(path, 'rt', encoding='utf-8') as stream:
        data = json.load(stream)
    p, n, m, R = (int(data[k]) for k in ('p', 'n', 'm', 'R'))
    N = R + 1
    raw = [[Q(x) for x in row] for row in data['raw_monomial_vectors']]
    lower = integers(data['lower_integer_matrix'])
    full = integers(data['full_integer_matrix'])
    assert 2 * (10 - p) * m + 2 * R <= p * (n + 1) - 2
    for rows, keys, denoms in [(lower, range(1, len(raw[0])-1), data['lower_row_denominators']),
                               (full, range(len(raw[0])), data['full_row_denominators'])]:
        assert len(rows) == len(keys)
        for row, key, den in zip(rows, keys, denoms):
            assert all(fmpq(row[r]) == int(den) * raw[r][key] for r in range(N))
    minors = {}
    for label, rows in [('low', lower), ('full', full)]:
        stored = data[label + '_hnf']
        T = fmpz_mat(integers(stored['T']))
        H = matrix(integers(stored['H']), len(rows))
        M = matrix(rows, N)
        basis = integers(stored['basis'])
        assert abs(int(T.det())) == 1 and T * M.transpose() == H
        assert len(basis) == N - M.rank()
        assert M * matrix(basis, N).transpose() == fmpz_mat(len(rows), len(basis))
        minors[label] = saturation_by_minors(basis, N)
    K = integers(data['low_hnf']['basis'])
    image = data['image_lattice']
    common = int(image['image_common_denominator'])
    generators = integers(image['image_generator_rows'])
    expected = [[common * sum((raw[r][key] * w[r] for r in range(N)), fmpq(0))
                 for key in (0, len(raw[0])-1)] for w in K]
    assert all(expected[i][j] == generators[i][j] for i in range(len(K)) for j in range(2))
    U = fmpz_mat(integers(image['image_U']))
    H = matrix(integers(image['image_H']), 2)
    assert abs(int(U.det())) == 1 and U * matrix(generators, 2) == H
    preimages = integers(image['image_preimages'])
    assert U * matrix(K, N) == matrix(preimages, N)
    search = data['candidate_search']
    zero = integers(search['full_zero_lll_basis'])
    weights = list(map(int, search['weight_diagonal']))
    assert weights == [n ** (2 * r) for r in range(N)]
    for before, after, transform in [
        (integers(image['full_zero_from_image']), zero, integers(search['full_zero_lll_transform'])),
        (integers(search['image_reduced_preimages']), integers(search['image_weighted_lll_basis']),
         integers(search['image_weighted_lll_transform']))]:
        if before:
            T = fmpz_mat(transform)
            assert abs(int(T.det())) == 1
            assert T * matrix(before, N) == matrix(after, N)
    basis = integers(search['image_weighted_lll_basis'])
    checked = []
    direct_row = None
    for index, row in enumerate(search['selected']):
        w = list(map(int, row['w']))
        exact = [sum((raw[r][k] * w[r] for r in range(N)), fmpq(0)) for k in range(len(raw[0]))]
        assert exact == [Q(x) for x in row['raw_vector']]
        assert not any(exact[1:-1]) and exact[-1] != 0
        original = [sum(int(row['combo'][i]) * basis[i][r] for i in range(len(basis))) for r in range(N)]
        after = [original[r] - sum(int(row['zero_reduction_multiples'][j]) * zero[j][r]
                 for j in range(len(zero))) for r in range(N)]
        assert w == after or w == [-x for x in after]
        norm = sum((w[r] * weights[r]) ** 2 for r in range(N))
        assert norm == int(row['weighted_W_norm_squared'])
        normalized = row['normalized']
        A, B = map(int, normalized['pair'])
        assert A > 0 and math.gcd(A, B) == 1
        multiplier = Q(normalized['multiplier'])
        assert exact[-1] * multiplier == A and exact[0] * multiplier == B
        assert all((math.lcm(*range(1, n+1)) ** 9 * x).denom() == 1 for x in exact)
        bits = max(1024, abs(A).bit_length() + abs(B).bit_length() + 256)
        with ctx.workprec(bits):
            # Factor the expression differently from score_value.
            value = arb(A) * (arb(9).zeta() + arb(fmpq(B, A)))
            assert value.lower() > 0 or value.upper() < 0
            lower, upper = interval_bounds(row['arb']['value_interval'])
            stored = arb((lower + upper) / 2, arb((upper-lower)/2).upper())
            assert value.overlaps(stored)
            logr = abs(value).log() / n
            checked.append(dict(candidate=index, r_interval=iv(logr),
                                independent_value_interval=iv(value),
                                log_W_l1_per_n=iv(arb(sum(map(abs, w))).log()/n),
                                primitive_sha256=hashlib.sha256(','.join(map(str, [A, B])).encode()).hexdigest()))
        if do_direct and (direct_row is None or float(row['arb']['abs_log_per_n']) < direct_row[0]):
            direct_row = (float(row['arb']['abs_log_per_n']), index, w, exact)
    direct = None
    if direct_row:
        _, index, w, exact = direct_row
        while len(w) > 1 and not w[-1]:
            w.pop()
        independent = product_form(p, n, [(m, 10-p)], w)
        assert independent['raw_vector'] == exact
        direct = dict(candidate=index, independent_taylor_raw_equal=True,
                      **direct_sum_audit(independent, T=max(256, 8*n), bits=4096))
    identities = archived_polynomial_identities(data)
    return dict(case_id=data['case_id'], status='passed',
                archive_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                polynomial_identities=identities, kernel_minors=minors,
                effective_image_rank=int(image['image_rank']), candidate_count=len(checked),
                candidates=checked, direct=direct, seconds=time.monotonic()-start)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--path', type=Path)
    parser.add_argument('--direct', action='store_true')
    args = parser.parse_args()
    paths = [args.path] if args.path else sorted(OUT.glob('weighted-p*.json.gz'))
    checks = []
    for path in paths:
        row = audit(path, do_direct=args.direct)
        checks.append(row)
        print(json.dumps({k: row[k] for k in ('case_id', 'status', 'candidate_count', 'seconds')}), flush=True)
    target = OUT / ('independent-archives-'+paths[0].name.replace('.json.gz', '')+'.json' if args.path else 'independent-archives.json')
    target.write_text(json.dumps(dict(status='passed', checks=checks), indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
