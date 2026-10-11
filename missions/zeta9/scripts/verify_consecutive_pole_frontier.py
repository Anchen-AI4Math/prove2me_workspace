"""Exact rank, Schur-table and normalization checks for the consecutive frontier.

Complete quotient/residue construction is shared with the independently reviewed
cluster verifier. Rank identities and whole-harmonic retention are checked here.
The infinite theorem is in the manuscript, not inferred from this finite grid.
"""
from functools import lru_cache
from itertools import product
from pathlib import Path
import hashlib
import json
import math

from verify_cluster_pole_frontier import (
    ROOT, Q, Mat, Poly, construct, interpolate, moment, primes, vp, vp_int,
)


def schur_table_sum(partition, variables):
    """Branch over horizontal strips: tableaux using the last variable's label."""
    partition = tuple(partition)
    variables = tuple(variables)

    @lru_cache(None)
    def branch(shape, n):
        if not any(shape):
            return 1
        if n == 0:
            return 0
        weight = sum(shape)
        # shape / inner is a horizontal strip iff these interlacing inequalities hold.
        ranges = [range(shape[i+1] if i+1 < len(shape) else 0, value+1)
                  for i, value in enumerate(shape)]
        return sum(branch(inner, n-1)*variables[n-1]**(weight-sum(inner))
                   for inner in product(*ranges))

    return branch(partition, len(variables))


def check_rank(B, poles, h):
    m = len(poles)
    r = max(0, min(m, h, 2*h+4-m))
    maximum = max(0, 2*h+3-m)
    complete = [1] + [0]*maximum
    for a in poles:
        for n in range(1, maximum+1):
            complete[n] += (-a*a)*complete[n-1]
    expected = Mat([[complete[i+j+5-m] if i+j+5-m >= 0 else 0
                     for j in range(h)] for i in range(h)])
    assert B == expected and B.rank() == r
    label = "zero"
    schur = None
    if m <= h:
        top = Mat([[B[i,j] for j in range(m)] for i in range(m)])
        sign = -1 if m*(m-1)//2 % 2 else 1
        assert top.det() == sign*math.prod(a**8 for a in poles)
        label = "vandermonde"
    elif m <= h+4:
        width = h+4-m
        schur = schur_table_sum((width,)*h, (a*a for a in poles))
        sign = -1 if (h*(5-m)+h*(h-1)//2) % 2 else 1
        assert schur > 0 and B.det() == sign*schur
        label = "schur_full_rank"
    elif m <= 2*h+3:
        q = m-h-4
        assert r == h-q
        assert all(B[i,j] == 0 for i in range(q) for j in range(h))
        assert all(B[i,j] == 0 for j in range(q) for i in range(h))
        active = Mat([[B[q+i,q+j] for j in range(r)] for i in range(r)])
        assert all(active[i,j] == 0 for i in range(r) for j in range(r)
                   if i+j < r-1)
        assert all(active[i,r-1-i] == 1 for i in range(r))
        sign = -1 if r*(r-1)//2 % 2 else 1
        assert active.det() == sign
        label = "live_low_rank"
    else:
        assert B == Mat(h,h)
    return r, label, str(schur) if schur is not None else None


def check_case(M, offsets, h, S, tag, consecutive):
    poles = [M+c for c in offsets]
    row, C, B = construct(poles, h, S, tag)
    if S == [1]:
        r, kind, schur = check_rank(B, poles, h)
        assert row['degree'] == r
    else:
        r, kind, schur = row['degree'], 'fixed_numerator', None
    row.update({'M':M, 'offsets':offsets, 'consecutive':consecutive,
                'rank_branch':kind, 'schur_table_value':schur})
    if not consecutive:
        return row
    assert offsets == list(range(1, len(poles)+1)) and S == [1]
    a = M+1
    harmonic = sum((Q(1,j**9) for j in range(1,a+1)),Q(0))
    R = C + harmonic*B
    F = interpolate(R,B,h)
    assert F.degree() == r
    K = math.lcm(*(int(moment(e).denominator) for e in range(2*h-1)))
    V = math.prod(poles[j]**2-poles[i]**2
                  for i in range(len(poles)) for j in range(i+1,len(poles)))
    clearer = 8*K*math.prod(poles)*V*math.prod(c**9 for c in poles[1:])
    assert clearer > 0
    assert all((clearer*R[i,j]).denominator == 1
               and (clearer*B[i,j]).denominator == 1
               for i in range(h) for j in range(h))
    N = clearer**h
    coefficients = [N*F[j] for j in range(r+1)]
    assert all(c.denominator == 1 for c in coefficients)
    top = abs(int(coefficients[-1].numerator))
    assert top > 0
    scalar = Q(row['minimal_positive_multiplier'])
    delta = Poly([int(c) for c in row['primitive_coefficients']])/scalar
    assert top % int(scalar.denominator) == 0
    T = int(harmonic.denominator)
    upper = Q(N*T**r)
    ratio = upper/scalar
    assert ratio.denominator == 1 and ratio >= 1
    exceptional = 1
    checks = []
    for p in primes(a):
        e = vp_int(T,p)
        if not e:
            continue
        if (N*top) % p == 0:
            exceptional *= p**e
        else:
            assert vp(scalar,p) == r*e
            assert vp(delta[0],p) == -r*e
            assert all(vp(delta[i],p) >= -(r-i)*e for i in range(r+1))
            checks.append({'p':p, 'harmonic_order':e, 'scalar_order':r*e})
    lower = Q((T//exceptional)**r,top)
    assert lower <= scalar <= upper
    if r == 0:
        assert row['primitive_coefficients'] == ['1']
    row.update({'consecutive_entry_clearer':str(clearer),
                'consecutive_top_integer':str(int(coefficients[-1].numerator)),
                'whole_harmonic_good_prime_checks':checks,
                'whole_harmonic_bad_part':str(exceptional),
                'consecutive_scalar_lower':str(lower),
                'consecutive_scalar_upper':str(upper)})
    return row


def main():
    rows = []
    for h in range(1,6):
        for m in range(1,2*h+5):
            for M in (0,7,31):
                rows.append(check_case(M,list(range(1,m+1)),h,[1],
                                       'consecutive complete rank grid',True))
        for m in sorted({h+4,h+5,2*h+3,2*h+4}):
            if 1 <= m <= 2*h+4:
                rows.append(check_case(127,list(range(1,m+1)),h,[1],
                                       'large shift rank endpoint',True))
    specs = [
        (1,list(range(1,7)),[0,1],'t numerator restores degree one'),
        (2,list(range(1,9)),[0,1],'t numerator restores rank one'),
        (2,list(range(1,9)),[1,0,1],'positive quadratic numerator'),
        (3,[1,3,8],[1],'fixed nonconsecutive offsets'),
        (2,[1,2,4,7,10,12,18],[1],'fixed nonconsecutive live low rank'),
        (2,[1,3,6],[2,-2,1],'fixed strictly positive signed coefficients'),
        (2,[1,2,3],[4,1],'fixed positive numerator'),
    ]
    for h,offsets,S,tag in specs:
        for M in (7,31):
            rows.append(check_case(M,offsets,h,S,tag,False))
    sources = [Path(__file__),ROOT/'scripts/verify_cluster_pole_frontier.py',
               ROOT/'research/consecutive-pole-frontier-2026-10-01.md']
    statistics = {
        'result':'PASS', 'date':'2026-10-01', 'case_count':len(rows),
        'consecutive_cases':sum(row['consecutive'] for row in rows),
        'fixed_numerator_or_offset_cases':sum(not row['consecutive'] for row in rows),
        'rank_branch_counts':{kind:sum(row['rank_branch']==kind for row in rows)
                             for kind in sorted({row['rank_branch'] for row in rows})},
        'whole_harmonic_prime_checks':sum(len(row.get('whole_harmonic_good_prime_checks',[]))
                                         for row in rows),
        'degree_zero_cases':sum(row['degree']==0 for row in rows),
        'arithmetic':'exact FLINT rationals; independent Schur tableau branching; Arb',
        'boundary':'Bounded cases verify implementation; infinite classification uses the written proof. No Lean or irrationality claim.',
        'source_hashes':{str(p.relative_to(ROOT)).replace('\\','/'):
                         hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
    }
    destination = ROOT/'verification/consecutive-pole-frontier-2026-10-01'
    destination.mkdir(parents=True,exist_ok=True)
    (destination/'certificate.json').write_text(json.dumps({**statistics,'cases':rows},indent=2)+'\n',encoding='utf-8')
    (destination/'summary.json').write_text(json.dumps(statistics,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(statistics,indent=2))


if __name__ == '__main__':
    main()
