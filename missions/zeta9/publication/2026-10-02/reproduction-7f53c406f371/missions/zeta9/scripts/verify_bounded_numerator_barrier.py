"""Independent monomial/interpolation checks for moving positive numerators.

The all-parameter theorem is in the companion proof. No finite extrapolation.
"""
from pathlib import Path
import hashlib
import json
import math
import sys

MISSION = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(MISSION / 'scripts'))
from probe_positive_hankel import Q, P, Mat, arb, ctx, moment
import sympy as sp

x = P([0, 1])


def functional_polynomial(poly):
    return sum((c * moment(9, e) for e, c in enumerate(poly)), Q(0))


def v_int(n, p):
    n = abs(int(n))
    if not n:
        return math.inf
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def valuation(q, p):
    return v_int(q.numer(), p) - v_int(q.denom(), p)


def interpolate(values):
    answer = P([0])
    for i, value in enumerate(values):
        term = P([1])
        scale = Q(1)
        for j in range(len(values)):
            if j != i:
                term *= x - j
                scale *= i - j
        answer += term * (value / scale)
    return answer


def ball(q):
    return arb(int(q.numer())) / int(q.denom())


def check(poles, h, numerator, tag):
    m = len(poles)
    q = h - m
    assert h >= m and poles[-1] == max(poles)
    assert math.gcd(*(int(c.numer()) for c in numerator)) == 1
    D = P([1])
    for a in poles:
        D *= x + a * a
    derivative = D.derivative()
    Si = [numerator(-a*a) for a in poles]
    assert all(Si)
    harmonics = {a: sum((Q(1, j**9) for j in range(1, a+1)), Q(0)) for a in poles}
    fa = {a: (-a**8 * harmonics[a] - Q(1, 8) + Q(1, 2*a), Q(a**8)) for a in poles}
    entries = []
    for degree in range(2*h-1):
        quotient, remainder = divmod(numerator * x**degree, D)
        const = functional_polynomial(quotient)
        linear = Q(0)
        for a in poles:
            residue = remainder(-a*a) / derivative(-a*a)
            const += residue * fa[a][0]
            linear += residue * fa[a][1]
        entries.append((const, linear))
    A = Mat([[entries[i+j][0] for j in range(h)] for i in range(h)])
    B = Mat([[entries[i+j][1] for j in range(h)] for i in range(h)])
    delta = interpolate([(A + j*B).det() for j in range(m+1)])
    assert delta.degree() == m
    for j in (-1, m+1):
        assert delta(j) == (A+j*B).det()
    emax = max(-1, numerator.degree()+2*h-m-2)
    C0 = math.lcm(*(int(moment(9,e).denom()) for e in range(emax+1))) if emax >= 0 else 1
    bottom = Mat([[functional_polynomial(numerator*D*x**(i+j)) for j in range(q)] for i in range(q)])
    det_bottom = bottom.det() if q else Q(1)
    assert det_bottom > 0
    Jrat = C0**q * det_bottom
    assert Jrat.denom() == 1
    J = int(Jrat.numer())
    expected_lead = Q((-1)**(m*(m-1)//2))*det_bottom
    for a, value in zip(poles, Si):
        expected_lead *= a**8 * value
    assert delta[m] == expected_lead
    # Independent exact basis transformation checks all matrix entries.
    basis = [D // (x+a*a) for a in poles] + [D*x**j for j in range(q)]
    T = Mat([[p[j] for j in range(h)] for p in basis])
    vand2 = math.prod((b*b-a*a)**2 for i,a in enumerate(poles) for b in poles[i+1:])
    assert T.det()**2 == vand2
    wide_B = T*B*T.transpose()
    expected_B = Mat(h, h)
    for i,(a,value) in enumerate(zip(poles,Si)):
        di = math.prod(b*b-a*a for b in poles if b != a)
        expected_B[i,i] = di*value*a**8
    assert wide_B == expected_B
    # Re-evaluate each basis product through division and all pole residues.
    # This checks the constant entries too, independently of matrix congruence.
    direct_A = Mat(h, h)
    direct_B = Mat(h, h)
    for i in range(h):
        for j in range(h):
            quotient, remainder = divmod(numerator*basis[i]*basis[j], D)
            const = functional_polynomial(quotient)
            linear = Q(0)
            for a in poles:
                residue = remainder(-a*a) / derivative(-a*a)
                const += residue*fa[a][0]
                linear += residue*fa[a][1]
            direct_A[i,j] = const
            direct_B[i,j] = linear
    assert direct_A == T*A*T.transpose() and direct_B == wide_B
    denominator = math.lcm(*(int(c.denom()) for c in delta))
    integers = [int((denominator*c).numer()) for c in delta]
    content = math.gcd(*integers)
    coefficients = [c//content for c in integers]
    scalar = Q(denominator, content)
    assert math.gcd(*coefficients) == 1 and P(coefficients) == scalar*delta
    leading_numerator = J * math.prod(a**8 * abs(int(value.numer())) for a,value in zip(poles,Si))
    assert leading_numerator % int(scalar.denom()) == 0
    bad = C0 * J * math.prod(a * int(value.numer()) for a,value in zip(poles,Si))
    checks = []
    for p in sp.primerange(max(5, poles[-1]//2+1), poles[-1]+1):
        p = int(p)
        if bad % p == 0:
            continue
        k = sum(a >= p for a in poles)
        orders = [v_int(math.prod(b*b-a*a for b in poles if b != a),p) for a in poles]
        assert max(orders, default=0) <= 3
        assert valuation(delta[m-k],p) == -9*k
        assert valuation(scalar,p) >= 9*k
        checks.append({'p':p,'high_poles':k,'pole_difference_valuations':orders,
                       'coefficient_order':int(valuation(delta[m-k],p)),
                       'multiplier_order':int(valuation(scalar,p))})
    ctx.prec = max(512, max(abs(c).bit_length() for c in coefficients)+256)
    z = arb(9).zeta()
    value = arb(0)
    for coefficient in reversed(coefficients):
        value = value*z+coefficient
    assert value > 0 and value.rel_accuracy_bits() > 80
    return {'poles':poles,'h':h,'numerator_tag':tag,'numerator_coefficients':[str(c) for c in numerator],
            'height':str(max(abs(int(c.numer())) for c in numerator)),
            'degree':delta.degree(),'primitive_multiplier':str(scalar),
            'primitive_coefficients':list(map(str,coefficients)),'value_ball':value.str(30),
            'below_one':bool(value < 1),'polynomial_moment_clearer':str(C0),
            'bottom_integer_J':str(J),'prime_checks':checks,
            'basis_and_leading_checks':True}


def main():
    pole_sets=[(1,), (2,), (1,2), (1,3), (2,3), (1,4), (2,5), (4,7),
               (1,2,3), (1,3,4), (2,4,7), (1,6,7,8),
               (17,), (23,31), (1,23,31),
               (30,31,91,92,120), (2,95,99,192)]
    rows=[]
    for poles in pole_sets:
        b=poles[-1]
        for extra in (0,1,2):
            h=len(poles)+extra
            nums=[('one',P([1])),('t_plus_two',x+2),
                  ('positive_square_moving', (x-(b*b-1))**2+1),
                  ('positive_square_fixed', (x-1)**2+1)]
            for tag,S in nums:
                if any(not S(-a*a) for a in poles):
                    continue
                rows.append(check(poles,h,S,tag))
    count=sum(len(row['prime_checks']) for row in rows)
    collisions=sum(any(v for v in test['pole_difference_valuations'])
                   for row in rows for test in row['prime_checks'])
    note=MISSION/'research/bounded-numerator-barrier-2026-10-01.md'
    cert={'status':'PASS','cases':rows,'case_count':len(rows),'prime_valuation_checks':count,
          'collision_prime_checks':collisions,'below_one_cases':[
              {'poles':row['poles'],'h':row['h'],'numerator_tag':row['numerator_tag'],'value':row['value_ball']}
              for row in rows if row['below_one']],
          'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'note_sha256':hashlib.sha256(note.read_bytes()).hexdigest(),
          'boundary':'Fixed bounded grid and exact identities. All-parameter barrier uses the written unique-lowest-term proof, compact positive polynomial cone and standard PNT; no Lean or irrationality result.'}
    out=MISSION/'verification/bounded-numerator-barrier-2026-10-01'
    out.mkdir(parents=True,exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(cert,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:cert[k] for k in ('status','case_count','prime_valuation_checks','collision_prime_checks','below_one_cases')},indent=2))


if __name__=='__main__':
    main()
