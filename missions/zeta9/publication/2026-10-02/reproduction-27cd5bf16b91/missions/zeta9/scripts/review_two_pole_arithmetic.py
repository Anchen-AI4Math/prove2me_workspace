"""Independent Fraction-only check of the two-pole coefficient valuations.

This avoids the existing functional implementation and floating-point values.
The uniform growth theorem is a written proof, not a consequence of this grid.
"""
from fractions import Fraction as F
from pathlib import Path
from math import gcd, lcm, prod
import hashlib
import json

MISSION = Path(__file__).resolve().parents[1]


def vp_int(n, p):
    if not n:
        raise ValueError('zero valuation needs a separate branch')
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def vp(q, p):
    return vp_int(q.numerator, p) - vp_int(q.denominator, p)


def main():
    limit = 64
    primes = [p for p in range(5, limit + 1)
              if all(p % d for d in range(2, int(p ** 0.5) + 1))]
    hs = [F(0)]
    for n in range(1, limit + 1):
        hs.append(hs[-1] + F(1, n ** 9))
    pair_count = 0
    valuation_count = 0
    low_count = 0
    high_count = 0
    singular_difference_count = 0
    displayed = []
    for b in range(2, limit + 1):
        for a in range(1, b):
            aa, bb, d = a ** 8, b ** 8, b ** 2 - a ** 2
            ua = -aa * hs[a] - F(1, 8) + F(1, 2 * a)
            ub = -bb * hs[b] - F(1, 8) + F(1, 2 * b)
            coeffs = [F(3, 4) * (ua - ub) / d - ua * ub,
                      F(3, 4) * (aa - bb) / d - aa * ub - bb * ua,
                      F(-aa * bb)]
            # A direct 2x2 moment determinant at three rational values checks
            # the quadratic identity separately from coefficient extraction.
            for x in (0, 1, -1):
                fa, fb = aa * x + ua, bb * x + ub
                m0 = (fa - fb) / d
                m1 = (-a ** 2 * fa + b ** 2 * fb) / d
                m2 = F(3, 4) + (a ** 4 * fa - b ** 4 * fb) / d
                assert m0 * m2 - m1 ** 2 == sum(c * x ** j for j, c in enumerate(coeffs))
            denominator = lcm(*(c.denominator for c in coeffs))
            ints = [int(c * denominator) for c in coeffs]
            content = gcd(*ints)
            multiplier = F(denominator, content)
            primitive = [v // content for v in ints]
            assert gcd(*primitive) == 1
            assert (aa * bb) % multiplier.denominator == 0
            forced = 1
            for p in primes:
                if 2 * p <= b or p > b or (a * b) % p == 0:
                    continue
                if p <= a:
                    assert vp(coeffs[0], p) == -18
                    assert vp(multiplier, p) >= 18
                    exponent = 18
                    low_count += 1
                else:
                    assert vp(coeffs[1], p) == -9
                    assert vp(multiplier, p) >= 9
                    exponent = 9
                    high_count += 1
                if d % p == 0:
                    assert vp_int(d, p) == 1
                    singular_difference_count += 1
                forced *= p ** exponent
                valuation_count += 1
            assert multiplier >= F(forced, aa * bb)
            pair_count += 1
            if (a, b) in ((1, 2), (2, 3), (6, 9), (20, 31), (40, 59), (63, 64)):
                displayed.append({'a': a, 'b': b, 'primitive_coefficients': list(map(str, primitive)),
                                  'primitive_multiplier': str(multiplier),
                                  'forced_prime_product': str(forced),
                                  'exact_lower_bound': str(F(forced, aa * bb))})
    assert displayed[0]['primitive_coefficients'] == ['-6163', '22568', '-16384']
    out = MISSION / 'verification/two-pole-independent-review-2026-10-01'
    out.mkdir(parents=True, exist_ok=True)
    cert = {'status': 'PASS', 'max_b': limit, 'all_pairs': pair_count,
            'direct_determinant_checks': 3 * pair_count,
            'prime_valuation_checks': valuation_count,
            'constant_coefficient_order_minus18': low_count,
            'linear_coefficient_order_minus9': high_count,
            'prime_divides_pole_difference_cases': singular_difference_count,
            'exact_multiplier_lower_bound_cases': pair_count,
            'displayed_cases': displayed,
            'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'boundary': 'Bounded Fraction-only independent checks. The all-pairs growth claim requires the written p-adic proof, positive Gram lower bound and standard PNT.'}
    (out / 'certificate.json').write_text(json.dumps(cert, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: cert[k] for k in ('status', 'all_pairs', 'prime_valuation_checks',
                                          'prime_divides_pole_difference_cases')}))


if __name__ == '__main__':
    main()
