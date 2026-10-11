"""Independent product/Taylor implementation for round 5, including layered zeros.

This module deliberately does not use the harmonic-number pole algorithm.
Its API accepts raw integer W coefficients in increasing order.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'tmp/zeta7/exact_packages'))
sys.set_int_max_str_digits(0)
from flint import arb, ctx, fmpq, fmpq_poly

BASE = ROOT / 'missions/zeta9/round5'
OUT = BASE / 'verification'


def qpair(q):
    q = fmpq(q)
    return [str(q.numer()), str(q.denom())]


def iv(x):
    a, b, e = x.mid_rad_10exp()
    return dict(mid=str(a), rad=str(b), exp=int(e))


def mul(a, b, d):
    out = [fmpq(0)] * (d + 1)
    for i, x in enumerate(a[:d + 1]):
        for j, y in enumerate(b[:d + 1 - i]):
            out[i + j] += x * y
    return out


def power_linear(c, power, d):
    if power >= 0:
        return [fmpq(math.comb(power, h) * c ** (power - h))
                if h <= power else fmpq(0) for h in range(d + 1)]
    assert c
    p = -power
    return [fmpq((-1) ** h * math.comb(p + h - 1, h), c ** (p + h))
            for h in range(d + 1)]


def compose_w(W, center, n, d):
    u = [fmpq(center * (center + n)), fmpq(2 * center + n), fmpq(1)]
    out = [fmpq(0)] * (d + 1)
    for w in reversed(W):
        out = mul(out, u, d)
        out[0] += int(w)
    return out


def validate(p, n, layers, W):
    if p not in (3, 5, 7, 9) or n <= 0 or n % 2:
        raise ValueError('p must be 3,5,7,9 and n positive even')
    if not W or any(int(w) != w for w in W):
        raise ValueError('W must be a nonempty list of integer coefficients')
    if not W[-1] and any(W):
        raise ValueError('Strip trailing zeros from W')
    if any(m < 0 or b <= 0 or int(m) != m or int(b) != b for m, b in layers):
        raise ValueError('layers must contain nonnegative integer m and positive integer b')
    R = len(W) - 1
    if 2 * sum(m * b for m, b in layers) + 2 * R > p * (n + 1) - 2:
        raise ValueError('Improper rational function or insufficient decay')


def scale(p, n, layers):
    return fmpq(math.factorial(n) ** p,
                math.prod(math.factorial(m) ** (2 * b) for m, b in layers))


def product_form(p, n, layers, W=(1,)):
    """Exact full PF vector from factor-by-factor truncated Taylor series."""
    W, layers = list(map(int, W)), [tuple(x) for x in layers]
    validate(p, n, layers, W)
    d = 9 - p
    poles = {s: [] for s in range(1, p + 1)}
    prefactor = scale(p, n, layers)
    for j in range(n + 1):
        local = compose_w(W, -j, n, p - 1)
        for m, b in layers:
            for shift in list(range(-m, 0)) + list(range(n + 1, n + m + 1)):
                local = mul(local, power_linear(shift - j, b, p - 1), p - 1)
        for i in range(n + 1):
            if i != j:
                local = mul(local, power_linear(i - j, -p, p - 1), p - 1)
        for h, value in enumerate(local):
            poles[p - h].append(prefactor * value)
    sums = {s: sum(cs, fmpq(0)) for s, cs in poles.items()}
    assert sums[1] == 0
    assert all(sums[s] == 0 for s in range(2, p + 1, 2))
    assert all(poles[s][n - j] == (-1) ** (s + 1) * poles[s][j]
               for s in poles for j in range(n + 1))
    B = fmpq(0)
    for s, cs in poles.items():
        H = fmpq(0)
        beta = math.comb(d + s - 1, d)
        for j, c in enumerate(cs):
            if j:
                H += fmpq(1, j ** (d + s))
            B -= beta * c * H
    orders = list(range(d + 3, 10, 2))
    vector = [B] + [math.comb(z - 1, d) * sums[z - d] for z in orders]
    return dict(p=p, n=n, layers=layers, W=W, d=d, zeta_orders=orders,
                raw_vector=vector, pole_coeffs=poles)


def polynomial_identity(form):
    p, n, layers, W = (form[k] for k in ('p', 'n', 'layers', 'W'))
    t = fmpq_poly([0, 1])
    u = t * (t + n)
    wp = fmpq_poly([0])
    for w in reversed(W):
        wp = wp * u + w
    numerator = wp * scale(p, n, layers)
    for m, b in layers:
        for shift in list(range(-m, 0)) + list(range(n + 1, n + m + 1)):
            numerator *= (t + shift) ** b
    denominator = fmpq_poly([1])
    for j in range(n + 1):
        denominator *= (t + j) ** p
    check = fmpq_poly([0])
    for s, cs in form['pole_coeffs'].items():
        for j, c in enumerate(cs):
            q, r = divmod(denominator, (t + j) ** s)
            assert not r
            check += c * q
    assert check == numerator
    payload = [qpair(x) for x in numerator]
    return dict(equal=True, numerator_degree=numerator.degree(),
                denominator_degree=denominator.degree(),
                numerator_sha256=hashlib.sha256(json.dumps(payload).encode()).hexdigest())


def direct_coefficient(p, n, layers, W, k):
    """d-th Taylor coefficient at k, evaluated directly from the products."""
    d = 9 - p
    out = compose_w(W, k, n, d)
    for m, b in layers:
        for shift in list(range(-m, 0)) + list(range(n + 1, n + m + 1)):
            out = mul(out, power_linear(k + shift, b, d), d)
    for shift in range(n + 1):
        out = mul(out, power_linear(k + shift, -p, d), d)
    return scale(p, n, layers) * out[d]


def product_tail(p, n, layers, W, T):
    """Cauchy product bound independent of all partial-fraction coefficients.

    For |z-k|=k/2 and k>=2(n+max(m)), each numerator factor <=2k,
    denominator factor >=k/2, |z(z+n)|<=3k^2. Integral test follows.
    """
    assert T >= 2 * (n + max([m for m, _ in layers] + [0]))
    d = 9 - p
    D = 2 * sum(m * b for m, b in layers)
    C = scale(p, n, layers) * 2 ** (D + p * (n + 1) + d)
    total = fmpq(0)
    for r, w in enumerate(W):
        gamma = p * (n + 1) + d - D - 2 * r
        assert gamma > 1
        total += C * abs(w) * 3 ** r * fmpq(1, (gamma - 1) * T ** (gamma - 1))
    return total


def direct_sum_audit(form, T=512, bits=2048):
    p, n, layers, W = (form[k] for k in ('p', 'n', 'layers', 'W'))
    start = time.monotonic()
    with ctx.workprec(bits):
        total = arb(0)
        if p == 9:
            # Undifferentiated product updated by its exact rational shift ratio.
            k = 1
            mmax = max([m for m, _ in layers] + [0])
            k = mmax + 1
            base = direct_coefficient(p, n, layers, [1], k)
            for k in range(k, T + 1):
                u = k * (k + n)
                value = 0
                for w in reversed(W):
                    value = value * u + w
                total += arb(base) * value
                # R(k+1)/R(k), cancelling every consecutive product.
                ratio = fmpq(k, k + n + 1) ** p
                for m, b in layers:
                    ratio *= (fmpq(k, k - m) * fmpq(k + n + m + 1, k + n + 1)) ** b
                base *= ratio
        else:
            for k in range(1, T + 1):
                if any(k <= m and b > 9 - p for m, b in layers):
                    continue
                total += arb(direct_coefficient(p, n, layers, W, k))
        radius = product_tail(p, n, layers, W, T)
        enclosing = total + arb(0, arb(radius).upper())
        raw = arb(form['raw_vector'][0])
        for z, c in zip(form['zeta_orders'], form['raw_vector'][1:]):
            raw += arb(z).zeta() * arb(c)
        assert enclosing.overlaps(raw)
        return dict(T=T, bits=bits, raw_zeta_interval=iv(raw),
                    original_product_sum_interval=iv(enclosing),
                    tail_radius=qpair(radius),
                    interval_overlap=True,
                    direct_excludes_zero=bool(enclosing.lower() > 0 or enclosing.upper() < 0),
                    seconds=time.monotonic() - start)


def bootstrap():
    # W=1 old interface regression; custom W and layered cases are independent.
    sys.path.insert(0, str(ROOT / 'missions/zeta9/round2/scripts'))
    from general_poles import exact_vector
    checks = []
    for p, n, m, W in [(9, 4, 4, [1]), (7, 4, 2, [1]), (5, 4, 1, [1]),
                       (9, 4, 4, [3, -2, 1]), (7, 4, 2, [2, 1])]:
        f = product_form(p, n, [(m, 10 - p)], W)
        row = dict(p=p, n=n, m=m, W=W, polynomial_identity=polynomial_identity(f))
        if W == [1]:
            old = exact_vector(p, n, m)
            assert f['raw_vector'] == old['raw_vector']
            assert f['pole_coeffs'] == old['pole_coeffs']
            row['old_raw_and_poles_equal'] = True
        row['direct_sum'] = direct_sum_audit(f, T=256)
        checks.append(row)
    f = product_form(3, 12, [(2, 7), (1, 2)])
    checks.append(dict(p=3, n=12, layers=f['layers'],
                       polynomial_identity=polynomial_identity(f),
                       direct_sum=direct_sum_audit(f, T=256)))
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'independent-bootstrap.json').write_text(json.dumps(dict(status='passed', checks=checks), indent=2)+'\n')
    print(json.dumps(dict(status='passed', cases=len(checks))))


if __name__ == '__main__':
    bootstrap()
