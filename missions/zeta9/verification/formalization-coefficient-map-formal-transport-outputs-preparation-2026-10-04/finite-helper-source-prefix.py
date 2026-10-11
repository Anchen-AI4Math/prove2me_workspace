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
