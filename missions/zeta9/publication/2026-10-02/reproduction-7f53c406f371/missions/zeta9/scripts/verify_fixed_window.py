"""Exact checks for research/fixed-window-asymptotic.md; no Lean or numerical zeta input."""
from fractions import Fraction as Q
from math import comb, factorial, prod
from pathlib import Path
import hashlib
import json
import sys

sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/fixed-window-2026-09-28'


def harmonic(n):
    return sum((Q(1, j) for j in range(1, n+1)), Q(0))


def beta(a, b):
    assert a > 0 and b > 0
    return Q(factorial(a-1), prod(range(b, b+a)))


def value(n, m, k):
    return Q(prod(k-j for j in range(1, m+1))**7
             * prod(k+n+j for j in range(1, m+1))**7,
             factorial(m)**14) * beta(k, n+1)**3


def log_derivatives(n, m, k):
    return [Q(0)] + [(-1)**(ell-1)*factorial(ell-1)*(
        7*sum((Q(1, (k-j)**ell) for j in range(1, m+1)), Q(0))
        + 7*sum((Q(1, (k+n+j)**ell) for j in range(1, m+1)), Q(0))
        - 3*sum((Q(1, (k+j)**ell) for j in range(n+1)), Q(0)))
        for ell in range(1, 7)]


def bell6(g):
    _, a, b, c, d, e, f = g
    return (a**6+15*a**4*b+20*a**3*c+45*a*a*b*b+15*a*a*d
            +60*a*b*c+6*a*e+15*b**3+10*c*c+15*b*d+f)


def coefficient_product(n, m, k):
    factors = [(k-j, 7) for j in range(1, m+1)]
    factors += [(k+n+j, 7) for j in range(1, m+1)]
    factors += [(k+j, -3) for j in range(n+1)]
    p = [Q(1)] + [Q(0)]*6
    for a, exponent in factors:
        q = [Q(comb(7, i) if exponent == 7 else (-1)**i*comb(i+2, 2), a**i)
             for i in range(7)]
        p = [sum((p[j]*q[i-j] for j in range(i+1)), Q(0)) for i in range(7)]
    return p[6]


def tail_bound(n, m):
    K, D = m+2, 14*m
    assert n > D
    C = (2*m+2)**D*factorial(D)
    return Q(C*(n+1)**(7*m), factorial(m)**14)*beta(K, n+1)**2*beta(K, n-D)


def threshold_constant(m):
    return (2*m+2)**(14*m)*factorial(14*m)*2**(11*m+5)*(m+1)**3


def ceil(q):
    return -(-q.numerator//q.denominator)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    M = {ell: 34*factorial(ell-1) for ell in range(2, 7)}
    x = 40
    # Sum of absolute values of every nonleading Bell term, divided by x^6.
    err = Q(15*x**4*M[2]+20*x**3*M[3]+45*x*x*M[2]**2
            +15*x*x*M[4]+60*x*M[2]*M[3]+6*x*M[5]
            +15*M[2]**3+10*M[3]**2+15*M[2]*M[4]+M[6], x**6)
    assert err < Q(1, 2)
    assert 1440*Q(5, 2)**6 == Q(703125, 2)

    checks = []
    for n in (2, 4, 6, 14, 28, 56):
        for m in range(4):
            if 14*m > 3*n+1:
                continue
            for k in (m+1, m+2):
                g = log_derivatives(n, m, k)
                b = bell6(g)/720
                assert b == coefficient_product(n, m, k)
                assert all(abs(g[ell]) <= M[ell] for ell in range(2, 7))
                S = 14*harmonic(m)+3*harmonic(n+1)
                assert abs(b) <= S**6
                if k == m+1:
                    assert g[1] == (10*harmonic(m)-3*harmonic(n+m+1)
                                   +7*(harmonic(n+2*m+1)-harmonic(n+m+1)))
                checks.append({'n': n, 'm': m, 'k': k, 'derivative_identity': True})

    tails = []
    for m in range(4):
        n = max(8, 28*m)
        upper = tail_bound(n, m)
        partial = sum((value(n, m, k) for k in range(m+2, m+18)), Q(0))
        assert partial < upper
        assert upper/value(n, m, m+1) <= Q(threshold_constant(m), n**3)
        tails.append({'n': n, 'm': m, 'partial_below_proved_infinite_tail_bound': True,
                      'simplified_bound_verified': True})

    thresholds = []
    for m in range(9):
        hm = harmonic(m)
        D = threshold_constant(m)
        q = max(30, ceil(Q(3, 2)*(10*hm+3)),
                max(2, 28*m, m+1).bit_length(),
                (int(703126*D).bit_length()+2)//3)
        n = 2**q
        assert Q(2*q, 3) >= max(20, 10*hm+3)
        assert n >= max(2, 28*m, m+1)
        assert n**3 >= 703126*D
        assert tail_bound(n, m)/value(n, m, m+1) <= Q(D, n**3)
        lower = value(n, m, m+1)*Q(4*q, 3)**6/2880
        assert lower > 0
        thresholds.append({'m': m, 'N_power_of_two': q, 'N': str(n),
                           'all_even_n_at_least_N_have_positive_L': True,
                           'positive_L_lower_bound_at_N': str(lower)})

    result = {'scope': 'Exact finite checks of a written uniform proof; no irrationality claim',
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'bell_relative_error_at_40': str(err), 'bell_error_less_than_half': True,
              'derivative_checks': checks, 'tail_checks': tails, 'thresholds': thresholds,
              'universal_statement_location': 'research/fixed-window-asymptotic.md',
              'lean_formalized': False, 'irrationality_proved': False}
    (OUT/'certificate.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'derivative_checks': len(checks), 'tail_checks': len(tails),
                      'thresholds': [{'m': t['m'], 'q': t['N_power_of_two']} for t in thresholds],
                      'bell_error': str(err), 'all_passed': True}))


if __name__ == '__main__':
    main()
