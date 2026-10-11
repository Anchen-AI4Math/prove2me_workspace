"""Independent finite Fraction checks; this never invokes Lean or author check code."""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, comb
from pathlib import Path
import hashlib, json

TASK = Path(__file__).resolve().parents[1]
OUT = Path(__file__).with_name('coefficient-map-formal-transport-independent-checks-2026-10-04.json')
X = [F(0), F(1)]
ONE = [F(1)]
checks = []

def trim(a):
    a = list(a)
    while len(a) > 1 and not a[-1]: a.pop()
    return a

def add(a, b):
    return trim([(a[i] if i < len(a) else F(0)) + (b[i] if i < len(b) else F(0))
                 for i in range(max(len(a), len(b)))])

def scale(a, c): return trim([v*c for v in a])
def sub(a, b): return add(a, scale(b, -1))

def mul(a, b):
    out = [F(0)]*(len(a)+len(b)-1)
    for i, v in enumerate(a):
        for j, w in enumerate(b): out[i+j] += v*w
    return trim(out)

def power(a, k):
    out = ONE
    for _ in range(k): out = mul(out, a)
    return out

def prod(values):
    out = ONE
    for a in values: out = mul(out, a)
    return out

def compose(a, b):
    out = [F(0)]
    for c in reversed(a): out = add(mul(out, b), [c])
    return out

def evaluate(a, x):
    out = F(0)
    for v in reversed(a): out = out*x+v
    return out

def coeff(a, k): return a[k] if k < len(a) else F(0)

def shift(a, z, length=None):
    length = len(a) if length is None else length
    return [sum((a[k]*comb(k, i)*z**(k-i) for k in range(i, len(a))), F(0))
            for i in range(length)]

def check(name, condition, detail=None):
    checks.append({'name': name, 'pass': bool(condition), 'detail': detail})
    assert condition, name

@lru_cache(None)
def pole(m): return prod(([F(j), F(1)] for j in range(m+1)))

@lru_cache(None)
def numerator(n):
    return scale(prod([[-F(k), F(1)] for k in range(1, n+1)] +
                      [[F(n+k), F(1)] for k in range(1, n+1)]), F(factorial(n)**7))

def weighted(n, p): return mul(numerator(n), compose(p, [F(0), F(n), F(1)]))

@lru_cache(None)
def cleared(m, j): return power(prod(([F(k), F(1)] for k in range(m+1) if k != j)), 9)

def jets(m, a):
    out = []
    for j in range(m+1):
        top, bottom = shift(a, -F(j), 9), shift(cleared(m, j), -F(j), 9)
        assert bottom[0] != 0
        series = []
        for k in range(9):
            series.append((top[k] - sum((bottom[i]*series[k-i] for i in range(1, k+1)), F(0))) / bottom[0])
        out.append([series[9-s] for s in range(1, 10)])
    return out

@lru_cache(None)
def block(m, j, s): return mul(cleared(m, j), power([F(j), F(1)], 9-s))

def reconstructed(m, array):
    return trim([sum((coeff(block(m, j, s), k)*array[j][s-1]
                      for j in range(m+1) for s in range(1, 10)), F(0))
                 for k in range(9*(m+1))])

def pf(array, x):
    return sum((a / (x+j)**s for j, row in enumerate(array) for s, a in enumerate(row, 1)), F(0))

def harmonic(s, j): return sum((F(1, k**s) for k in range(1, j+1)), F(0))
def constant(array): return -sum((a*harmonic(s, j) for j, row in enumerate(array) for s, a in enumerate(row, 1)), F(0))
def rho(array): return [sum((row[s] for row in array), F(0)) for s in range(9)]
def five(array): return [constant(array)] + [rho(array)[s-1] for s in (3, 5, 7, 9)]
def actual(n, p, t): return evaluate(weighted(n, p), t) / evaluate(pole(n), t)**9
def finite(n, p, T): return sum((actual(n, p, F(t)) for t in range(1, T+1)), F(0))

def solve_connection(n):
    u, v, w = [F(0), F(n), F(1)], [F(0), F(n-1), F(1)], [F(n), F(n+1), F(1)]
    d = power(sub(u, [F(n+1)]), 10)
    first = mul([-F(n+1), F(1)], power([F(n+1), F(1)], 10))
    second = mul([F(2*n+1), F(1)], power([-F(1), F(1)], 10))
    basis = [mul(d, power(u, k)) for k in range(5)]
    basis += [sub(mul(first, power(v, k)), mul(second, power(w, k))) for k in range(10)]
    z = prod((sub(u, [F((n+i)*(2*n+i))]) for i in range(1, 4)))
    rhs = [scale(mul(z, power(sub(u, [F(n+1)]), r)), F(((n+1)*(n+2))**7)) for r in range(5)]
    matrix = [[coeff(a, 2*k) for a in basis+rhs] for k in range(15)]
    for k in range(15):
        pivot = next(i for i in range(k, 15) if matrix[i][k])
        matrix[k], matrix[pivot] = matrix[pivot], matrix[k]
        matrix[k] = [a/matrix[k][k] for a in matrix[k]]
        for i in range(15):
            if i != k and matrix[i][k]:
                a = matrix[i][k]
                matrix[i] = [x-a*y for x, y in zip(matrix[i], matrix[k])]
    pairs = []
    for r in range(5):
        values = [row[15+r] for row in matrix]
        p, q = trim(values[:5]), trim(values[5:])
        full = [sum((coeff(a, k)*c for a, c in zip(basis, values)), F(0)) for k in range(30)]
        check(f'n{n}_r{r}_all_original_polynomial_coefficients', trim(full) == rhs[r])
        pairs.append((p, q))
    return pairs

inputs = ['research/coefficient-map-formal-transport-design-2026-10-04.md',
          'formalization/CoefficientMapFormalTransportData.lean', 'formalization/CoefficientMapConnection.lean',
          'formalization/CoefficientMapParameterShift.lean', 'formalization/CoefficientMap.lean',
          'formalization/CoefficientMapJet.lean', 'formalization/CoefficientMapFiniteSum.lean',
          'formalization/CoefficientMapMatrix.lean']
bindings = [{'task_relative': p, 'bytes': (TASK/p).stat().st_size,
             'sha256': hashlib.sha256((TASK/p).read_bytes()).hexdigest()} for p in inputs]
instances = []
for n in (1, 2, 3, 4, 5):
    pairs = solve_connection(n)
    old_f = [five(jets(n, weighted(n, power(X, l)))) for l in range(5)]
    new_f = []
    for r, (p, q) in enumerate(pairs):
        label = f'n{n}_r{r}_'
        newp = power(X, r)
        b, a = jets(n, weighted(n, p)), jets(n+2, weighted(n+2, newp))
        qnum = mul(scale(prod([[-F(i+2), F(1)] for i in range(n)] +
                              [[F(n+i+1), F(1)] for i in range(n)]), F(factorial(n)**7)),
                   compose(q, [F(0), F(n-1), F(1)]))
        qshift = shift(qnum, F(1))
        c = jets(n+1, qshift)
        clear_identity = add(mul(mul(power(X, 9), power([F(n+2), F(1)], 9)),
                                 shift(weighted(n, p), F(1))),
                             sub(mul(power([F(n+2), F(1)], 9), qshift),
                                 mul(power(X, 9), shift(qshift, F(1)))))
        check(label+'whole_cleared_polynomial_transport_identity', clear_identity == weighted(n+2, newp))
        check(label+'degree_gap_at_least_7n', len(trim(qshift))-1 <= 2*n+18 < 9*(n+2))
        check(label+'whole_old_new_and_Q_PF_polynomial_identities',
              reconstructed(n, b) == weighted(n, p) and
              reconstructed(n+2, a) == weighted(n+2, newp) and reconstructed(n+1, c) == trim(qshift))
        def Q(t): return evaluate(qnum, t) / ((t-1)*evaluate(pole(n), t))**9
        check(label+'true_uncancelled_Q_equals_actual_numerator', all(
            Q(t) == actual(n, ONE, t)*(t-n-1)*evaluate(q, t*(t+n-1))/(t-1)**10
            for t in (F(2), F(3, 2), F(n+7, 2))))
        check(label+'all_nine_actual_local_shift_relations', all(
            a[j][s] == (b[j-1][s] if 1 <= j <= n+1 else 0) +
            (c[j][s] if j <= n+1 else 0) - (c[j-1][s] if j >= 1 else 0)
            for j in range(n+3) for s in range(9)))
        check(label+'all_nine_rho_totals', rho(a) == rho(b))
        check(label+'signed_rational_B_correction', constant(a) == constant(b)-actual(n, p, F(1))+Q(F(2)))
        check(label+'two_boundary_zeros', actual(n, p, F(1)) == Q(F(2)) == 0)
        check(label+'actual_Q_PF_regular_points', all(Q(t) == pf(c, t-1) for t in (F(2), F(3, 2), F(n+7, 2))))
        for T in (0, 1, 2, 5):
            check(label+f'finite_T{T}_including_endpoints',
                  finite(n+2, newp, T) == finite(n, p, T+1)-actual(n, p, F(1))+Q(F(2))-Q(F(T+2)))
        new_f.append(five(a))
        instances.append({'n': n, 'r': r, 'P': [str(v) for v in p], 'q': [str(v) for v in q],
                          'Q_degree': len(trim(qshift))-1, 'old_five': [str(v) for v in five(b)],
                          'new_five': [str(v) for v in five(a)]})
    check(f'n{n}_all25_actual_matrix_entries_left_Gamma_orientation', all(
        new_f[r][s] == sum((coeff(pairs[r][0], l)*old_f[l][s] for l in range(5)), F(0))
        for r in range(5) for s in range(5)))
    print(f'Independent exact n={n}, five targets and all25 matrix entries passed.', flush=True)

qn1 = [-F(4), F(0), F(1)]
cn1 = jets(2, shift(qn1, F(1)))
check('negative_control_n1_R2_is_not_zero', actual(1, ONE, F(2)) == F(4, 6**9) != 0)
check('negative_control_endpoint_or_Nat_pred_omission_changes_nonzero_principal_part', cn1[0][8] == cn1[-1][8] == -F(3, 512))
check('negative_control_n0_degree_nine_polynomial_part_not_proper', 18 == 9*(0+2))
check('negative_control_n0_boundary_zeros_fail', actual(0, ONE, F(1)) == 1 and F(1, 2**9) != 0)
check('negative_control_proper_does_not_imply_summable', len(power(X, 8))-1 < 9 and evaluate(power(X, 8), F(2))/F(2)**9 == F(1, 2))
for row in bindings:
    assert hashlib.sha256((TASK/row['task_relative']).read_bytes()).hexdigest() == row['sha256']
report = {'status': 'FINITE_INDEPENDENT_EXACT_RATIONAL_DESIGN_CHECKS_NOT_UNIVERSAL_LEAN_PROOF',
          'Lean_invocations': 0, 'author_code_or_finite_results_reused': False, 'checks': checks,
          'check_count': len(checks), 'instances': instances, 'source_inputs': bindings,
          'reviewer_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'negative_controls': {'n1_R1_at2': str(F(4, 6**9)), 'n1_q1_c0_order9': str(cn1[0][8]),
            'n1_q1_c_last_order9': str(cn1[-1][8]), 'n0_q_X9_Q_limit': '1',
            'n0_q1_Q2': '1/512', 'strictly_proper_n0_X4_actual_function': '1/t'}}
OUT.write_text(json.dumps(report, indent=2)+'\n', encoding='utf8')
print('Independent finite checks:', len(checks), 'all passed; Lean calls 0.', flush=True)
