"""Exact polynomial connection and local lattice audit; no zeta numerics."""
from __future__ import annotations
import hashlib
import json
import math
import sys
from itertools import combinations
from fractions import Fraction as Q
from pathlib import Path

MISSION = Path(__file__).resolve().parents[1]
ROOT = MISSION.parents[1]
sys.path.insert(0, str(ROOT / 'tmp/zeta7/exact_packages'))
from flint import fmpq, fmpq_mat, fmpz, fmpz_poly as P, fmpq_poly as QP


def exact(a, b):
    q, r = divmod(a, b)
    assert not r
    return q


def factor(p):
    unit, fs = p.factor()
    return {'unit': str(unit), 'factors': [
        {'coefficients': [str(c) for c in f], 'exponent': e}
        for f, e in fs]}


def determinant(matrix):
    a = [row[:] for row in matrix]
    previous = P([1]); sign = 1
    for k in range(len(a)-1):
        if not a[k][k]:
            candidates = [j for j in range(k+1, len(a)) if a[j][k]]
            if not candidates:
                return P([])
            j = candidates[0]
            a[k], a[j] = a[j], a[k]; sign = -sign
        pivot = a[k][k]
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                a[i][j] = exact(pivot*a[i][j]-a[i][k]*a[k][j], previous)
        previous = pivot
    return sign*a[-1][-1]


def determinantal_certificates(matrix):
    result = []
    for size in range(1, 6):
        indices = list(combinations(range(5), size))
        minors = [determinant([[matrix[i][j] for j in J] for i in I])
                  for I in indices for J in indices]
        # Independent numeric determinant implementation, all minors.
        for point in (2, 4, 12):
            for pol, (I, J) in zip(minors, ((I, J) for I in indices for J in indices)):
                direct = fmpq_mat([[matrix[i][j](point) for j in J] for i in I]).det()
                assert direct == pol(point)
        common = P([])
        for v in minors:
            common = common.gcd(v)
        reduced = [exact(v, common) for v in minors]
        special = {}
        for root in (-1, -2):
            value_gcd = math.gcd(*(int(v(root)) for v in reduced))
            special[str(root)] = {'gcd': str(value_gcd),
                                 'factors': [[str(p), e] for p, e in fmpz(value_gcd).factor()]}
        # Over Q[x], find a finite Bezout certificate. Its denominator gives
        # the finite exceptional prime set for specialization over Z_(p).
        g = QP([]); coefficients = []
        used = []
        for idx, v in enumerate(reduced):
            if not v:
                continue
            newg, s, t = g.xgcd(QP(v))
            coefficients = [s*c for c in coefficients] + [t]
            used.append(idx); g = newg
            if g == 1:
                break
        assert g == 1
        clearing = 1
        for pol in coefficients:
            for c in pol:
                clearing = math.lcm(clearing, int(c.denom()))
        integers = [P([int(c*clearing) for c in pol]) for pol in coefficients]
        assert sum((a*reduced[i] for a, i in zip(integers, used)), P([])) == clearing
        result.append({'size': size, 'minor_count': len(minors),
                       'gcd': factor(common),
                       'specialization_gcd': special,
                       'bezout_constant': str(clearing),
                       'bezout_terms': [{'minor_index': i, 'multiplier': [str(c) for c in pol]}
                                        for i, pol in zip(used, integers)]})
        print('minor size', size, 'gcd', common.factor(), 'specializations', special, flush=True)
    return result


def valuation(x, p):
    x = fmpq(x)
    if not x:
        return 10**9
    def integer_v(z):
        z = abs(int(z)); count = 0
        while z % p == 0:
            z //= p; count += 1
        return count
    return integer_v(x.numer())-integer_v(x.denom())


def prime_list(limit):
    return [p for p in range(2, limit+1)
            if all(p % d for d in range(2, math.isqrt(p)+1))]


def minor_values(matrix, size, fixed_columns=None):
    cols = list(combinations(range(5), size)) if fixed_columns is None else fixed_columns
    return [fmpq_mat([[matrix[i,j] for j in J] for i in I]).det()
            for I in combinations(range(5), size) for J in cols]


def local_n_data(matrix):
    return (matrix.det(), minor_values(matrix, 3, [(1,2,3)]),
            minor_values(matrix, 4, [(1,2,3,0), (1,2,3,4)]))


def local_n_exponent(data, p):
    d, small, mixed = data
    return valuation(d,p)+min(valuation(v,p) for v in small)-2*min(valuation(v,p) for v in mixed)


def finite_audit(rows, integer_matrix, denominator):
    def connection(n):
        return fmpq_mat([[fmpq(P([int(c) for c in e['numerator']])(n),
                                  P([int(c) for c in e['denominator']])(n))
                          for e in row] for row in rows])
    sys.path.insert(0, str(MISSION/'round6/scripts'))
    from independent_audit import independent_columns
    f = fmpq_mat(independent_columns(2))
    assert f.det() == 2160
    previous = local_n_data(f)
    plateau_count = 0; boundary_cases = []; upper_cases = []
    raw_checks = []
    snapshots = {p-1: p for p in prime_list(80) if p > 7}
    selected = {12,24,48,96,192,234,258}
    for n in range(2, 259, 2):
        if n in (12, 36, 258):
            assert f == fmpq_mat(independent_columns(n))
            raw_checks.append(n)
        if n in snapshots:
            p = snapshots[n]
            assert all(valuation(f[i,j],p) >= 1 for i in range(5) for j in range(1,5))
            sums = [min(valuation(v,p) for v in minor_values(f,k)) for k in range(1,6)]
            profile = [sums[0]]+[sums[k]-sums[k-1] for k in range(1,5)]
            assert profile == [0,1,1,1,1]
            boundary_cases.append({'n':n,'p':p,'profile':profile})
        if n in selected:
            data = local_n_data(f)
            for p in prime_list(n):
                if p > max(7,n//2):
                    actual = local_n_exponent(data,p)
                    bound = 13 + (3*n)//(2*p)+(7*n)//(2*p)
                    assert actual <= bound
                    upper_cases.append({'n':n,'p':p,'exponent':actual,'upper_bound':bound})
            if n in (234,258):
                p, expected = (29,13) if n == 234 else (257,12)
                assert local_n_exponent(data,p) == expected
        if n == 258:
            break
        f = connection(n)*f
        if n <= 58:
            current = local_n_data(f)
            singular = n*(n+1)*(n+2)*(3*n+2)*(3*n+4)*math.prod(7*n+2*j for j in range(1,7))
            for p in prime_list(97):
                if p > 7 and singular % p:
                    assert local_n_exponent(current,p) == local_n_exponent(previous,p)
                    plateau_count += 1
            previous = current
    return {'raw_product_crosschecks':raw_checks,'boundary_smith_cases':boundary_cases,
            'plateau_checks':plateau_count,'new_bound_cases':upper_cases,
            'previous_counterexamples_reproduced':[[234,29,13],[258,257,12]],
            'independent_polynomial_minor_checks':3*sum(math.comb(5,k)**2 for k in range(1,6))}


def budget_audit():
    def envelope(y):
        return 19+(3*y)//2+(7*y)//2-10*(y//2)-5*int(y-y//1 >= Q(2,3))
    cuts = sorted({Q(0),Q(1),Q(2),Q(2,3),Q(5,3)} |
                  {Q(2*j,d) for d in (3,7) for j in range(d+1)})
    primitive = Q(0)
    for a,b in zip(cuts,cuts[1:]):
        primitive += (b-a)*(envelope((a+b)/2)-Q(64,3))
        assert -Q(50,21) <= primitive <= 0
    assert primitive == 0
    total = Q(0); gain = Q(0)
    for k in range(1,100):
        cuts = {Q(k),Q(k+1),Q(k)+Q(2,3)}
        for d in (3,7):
            cuts.update(Q(2*j,d) for j in range(d*k//2,d*(k+1)//2+2)
                        if k < Q(2*j,d) < k+1)
        cuts = sorted(cuts)
        for a,b in zip(cuts,cuts[1:]):
            y = (a+b)/2
            old = envelope(y)
            new = 2+(3*y)//2+(7*y)//2 if y < 2 else old
            total += new*(1/a-1/b)
            gain += (old-new)*(1/a-1/b)
    assert gain == 8
    upper = total+Q(64,300)
    lower = upper-Q(50,210000)
    assert Q(14336,1000) < lower <= upper < Q(14337,1000)
    return {'envelope_integral_lower':str(lower),'envelope_integral_upper':str(upper),
            'strict_upper':'14.337','exact_improvement':str(gain),
            'warning':'This is an upper bound, not the actual budget or a proof of VC.'}


def main():
    source = MISSION / 'round7/verification/arithmetic-connection-symbolic.json'
    data = json.loads(source.read_text())
    cols = [[P([int(a) for a in v]) for v in col]
            for col in data['system_columns_old_then_H']]
    # Reconstruct all target columns from the displayed connection identity.
    sys.path.insert(0, str(MISSION / 'round7/scripts'))
    from arithmetic_connection_symbolic import mul, power, invariant, add, neg
    x = P([0, 1]); zero = P([]); one = P([1])
    v = [zero, x-1, one]; vp = [x, x+1, one]
    hs = [invariant(add(mul(mul([-x-1, one], power([x+1, one], 10)), power(v, a)),
                        neg(mul(mul([2*x+1, one], power([-one, one], 10)), power(vp, a)))))
          for a in range(10)]
    assert cols == [[zero]*r + power([-x-1, one], 10) for r in range(5)] + hs
    z = [one]
    for a in range(1, 4):
        z = mul(z, [-(x+a)*(2*x+a), one])
    target_cols = [[((x+1)*(x+2))**7*c for c in mul(z, power([-x-1, one], r))]
                   for r in range(5)]
    matrix = [[col[i] if i < len(col) else zero for col in cols] for i in range(15)]
    rhs = [[col[i] if i < len(col) else zero for col in target_cols] for i in range(15)]
    a = [matrix[i] + rhs[i] for i in range(15)]
    previous = one
    swaps = 0
    for k in range(14):
        if not a[k][k]:
            j = next(j for j in range(k+1, 15) if a[j][k])
            a[k], a[j] = a[j], a[k]
            swaps += 1
        pivot = a[k][k]
        for i in range(k+1, 15):
            for j in range(k+1, 20):
                a[i][j] = exact(pivot*a[i][j]-a[i][k]*a[k][j], previous)
            a[i][k] = zero
        previous = pivot
        print('polynomial elimination', k+1, flush=True)
    det = a[14][14]
    assert (-1)**swaps*det == x**10*(x+1)**45*(x+2)**55
    sol = [[zero for _ in range(5)] for _ in range(15)]
    for i in reversed(range(15)):
        for r in range(5):
            numerator = det*a[i][15+r] - sum((a[i][j]*sol[j][r] for j in range(i+1, 15)), zero)
            sol[i][r] = exact(numerator, a[i][i])
    for i in range(15):
        for r in range(5):
            assert sum((matrix[i][j]*sol[j][r] for j in range(15)), zero) == det*rhs[i][r]
    rows = []
    denominator = one
    for r in range(5):
        row = []
        for j in range(5):
            g = sol[j][r].gcd(det)
            num, den = exact(sol[j][r], g), exact(det, g)
            if den.leading_coefficient() < 0:
                num, den = -num, -den
            row.append({'numerator': [str(c) for c in num],
                        'denominator': [str(c) for c in den]})
            denominator = exact(denominator*den, denominator.gcd(den))
        rows.append(row)
    result = {'status': 'passed', 'method': 'fraction-free polynomial solve, all 75 identities checked',
              'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'common_denominator': factor(denominator), 'connection': rows}
    integer_matrix = [[P([int(c) for c in entry['numerator']]) *
                       exact(denominator, P([int(c) for c in entry['denominator']]))
                       for entry in row] for row in rows]
    result['determinantal_certificates'] = determinantal_certificates(integer_matrix)
    result['finite_audit'] = finite_audit(rows, integer_matrix, denominator)
    result['budget_audit'] = budget_audit()
    result['script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    out = MISSION/'verification/local-connection-2026-09-28'
    out.mkdir(parents=True, exist_ok=True)
    (out/'symbolic.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result['common_denominator'], indent=2), flush=True)
    print('finite audit passed; budget strictly below',result['budget_audit']['strict_upper'],flush=True)


if __name__ == '__main__':
    main()
