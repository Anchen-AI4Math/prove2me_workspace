"""Exact Gram cancellation and denominator-minimal one-sided projections.

The finite records are implementation evidence, not an irrationality proof.
"""
from pathlib import Path
from fractions import Fraction
from math import gcd, lcm
from itertools import combinations
import hashlib
import json
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from probe_exterior_cone import Q, Mat, connection
from verify_direction_frontier import as_ball, ball_record, log_rate
from flint import arb, ctx
sys.path.insert(0, str(ROOT / "round6/scripts"))
from independent_audit import independent_columns
sys.set_int_max_str_digits(0)
OUT = ROOT / "verification/direction-arithmetic-next-2026-10-02"


def integer_content(v):
    return gcd(*map(abs, v))


def valuation(x, p):
    x = Fraction(x)
    if not x:
        return float("inf")
    value = 0
    numerator, denominator = abs(x.numerator), x.denominator
    while numerator % p == 0:
        numerator //= p
        value += 1
    while denominator % p == 0:
        denominator //= p
        value -= 1
    return value


def dot(u, v):
    return sum(x*y for x, y in zip(u, v))


def primitive_gram(u, v, test_primes):
    """Separate row content, wedge content and saturated Gram degeneracy."""
    content_u, content_v = integer_content(u), integer_content(v)
    assert content_u > 0 and content_v > 0
    u0 = [x//content_u for x in u]
    v0 = [x//content_v for x in v]
    assert integer_content(u0) == integer_content(v0) == 1
    t, c, r = dot(u0,u0), dot(u0,v0), dot(v0,v0)
    minors = [u0[i]*v0[j]-u0[j]*v0[i]
              for i,j in combinations(range(len(u0)),2)]
    delta = integer_content(minors)
    area2 = sum(x*x for x in minors)
    assert delta > 0 and area2 == t*r-c*c
    sat = area2//(delta*delta)
    assert area2 == delta*delta*sat
    gram_gcd = gcd(t,c)
    assert (delta*sat) % gram_gcd == 0
    ratio_content = gcd(content_u,content_v)
    a, b = content_u//ratio_content, content_v//ratio_content
    center = Fraction(b*c,a*t)
    lower = t//gcd(t,b*delta*sat)
    assert center.denominator % lower == 0
    checks = []
    for p in test_primes:
        s = valuation(delta,p)
        j = next(j for j,x in enumerate(u0) if x % p)
        lam = Fraction(v0[j],u0[j])
        w = [(Fraction(y)-lam*x)/(p**s) for x,y in zip(u0,v0)]
        assert min(valuation(x,p) for x in w) == 0
        cross = dot(u0,w)
        t_order, e_order = valuation(t,p), valuation(cross,p)
        q_order = valuation(sat,p)
        assert valuation(gram_gcd,p) == min(t_order,s+e_order)
        assert valuation(Fraction(c,t).denominator,p) == max(0,t_order-s-e_order)
        assert valuation(dot(u0,u0)*dot(w,w)-cross*cross,p) == q_order
        if t_order > q_order:
            assert q_order == 2*e_order
        assert valuation(gram_gcd,p) <= s+q_order
        if t_order and not s and not q_order:
            assert valuation(Fraction(c,t).denominator,p) == t_order
        checks.append(dict(p=p,norm_order=t_order,wedge_order=s,
                           cross_order="infinity" if e_order == float("inf") else e_order,
                           saturated_discriminant_order=q_order))
    return dict(primitive_first_norm=str(t), primitive_gram_gcd=str(gram_gcd),
                primitive_wedge_content=str(delta), saturated_gram_discriminant=str(sat),
                row_content_ratio=[str(b),str(a)], denominator_lower_divisor=str(lower),
                local_checks=checks)


def denominator_minimal_interval(left, right):
    """Accelerated Stern--Brocot search; positive, closed rational interval."""
    left, right = Fraction(left), Fraction(right)
    assert 0 < left <= right
    lp,lq,rp,rq = 0,1,1,0
    steps = 0
    while True:
        assert rp*lq-lp*rq == 1
        p,q = lp+rp,lq+rq
        med = Fraction(p,q)
        if left <= med <= right:
            assert Fraction(lp,lq) < left
            assert not rq or right < Fraction(rp,rq)
            return med,(lp,lq,rp,rq),steps
        if med < left:
            x = left.numerator*lq-left.denominator*lp
            y = left.denominator*rp-left.numerator*rq
            assert y > 0
            k = (x-1)//y
            assert k >= 1
            lp,lq = lp+k*rp,lq+k*rq
        else:
            x = right.denominator*rp-right.numerator*rq
            y = right.numerator*lq-right.denominator*lp
            assert y > 0
            k = (x-1)//y
            assert k >= 1
            rp,rq = rp+k*lp,rq+k*lq
        steps += 1


def toy_checks():
    rng = random.Random(20261002)
    gram_cases = local_cases = 0
    for dimension in (2,3,5):
        for _ in range(120):
            u = [rng.randrange(-20,21) for _ in range(dimension)]
            v = [rng.randrange(-20,21) for _ in range(dimension)]
            if not integer_content(u) or not integer_content(v):
                continue
            if not integer_content([u[i]*v[j]-u[j]*v[i]
                                    for i,j in combinations(range(dimension),2)]):
                continue
            rec = primitive_gram(u,v,(2,3,5,7,11,13,17,19))
            gram_cases += 1
            local_cases += len(rec['local_checks'])
    intervals = 0
    for _ in range(160):
        x = Fraction(rng.randrange(1,80),rng.randrange(1,36))
        y = Fraction(rng.randrange(1,80),rng.randrange(1,36))
        left,right = sorted((x,y))
        witness,parents,steps = denominator_minimal_interval(left,right)
        # Exhaust all smaller denominators by integer numerator feasibility.
        for q in range(1,witness.denominator):
            smallest = -((-left.numerator*q)//left.denominator)
            largest = right.numerator*q//right.denominator
            assert smallest > largest
        lp,lq,rp,rq = parents
        assert witness == Fraction(lp+rp,lq+rq)
        if rq:
            assert (right-left)*witness.denominator <= Fraction(1,lq)+Fraction(1,rq)
        intervals += 1
    return dict(gram_cases=gram_cases,local_cases=local_cases,
                denominator_minimal_interval_cases=intervals)


def actual_case(n,f):
    inverse = f.inv()
    e = Mat([[inverse[i,j]*n**(2*j) for j in range(5)] for i in (0,4)])
    common = lcm(*(int(e[i,j].denom()) for i in range(2) for j in range(5)))
    u = [int(common*e[0,j]) for j in range(5)]
    v = [int(common*e[1,j]) for j in range(5)]
    rec = primitive_gram(u,v,(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47))
    t,c,r = dot(u,u),dot(u,v),dot(v,v)
    center = Fraction(c,t)
    assert u[0] and u[1]
    ratios = [Fraction(v[j],u[j]) for j in (0,1)]
    left,right = sorted(ratios)
    witness,parents,steps = denominator_minimal_interval(left,right)
    p,q = witness.numerator,witness.denominator
    lo,hi = sorted((0,1),key=lambda j:ratios[j])
    ell = [0]*5
    ell[lo] = q*v[hi]-p*u[hi]
    ell[hi] = p*u[lo]-q*v[lo]
    det = u[lo]*v[hi]-u[hi]*v[lo]
    assert dot(u,ell) == q*det and dot(v,ell) == p*det
    if u[lo] > 0 and u[hi] > 0:
        assert min(ell) >= 0 and det > 0
    a,b = left,right
    lower = int(rec['denominator_lower_divisor'])
    with ctx.workprec(max(512,32*n+512)):
        theta = arb(9).zeta()
        error_left = theta-as_ball(Q(a.numerator,a.denominator))
        error_right = theta-as_ball(Q(b.numerator,b.denominator))
        assert not error_left.contains(0) and not error_right.contains(0)
        same_side = bool(error_left*error_right > 0)
        assert same_side
        primitive = abs(q*theta-p)
        assert primitive > 0
        primitive_record = ball_record(primitive)
        primitive_rate = ball_record(primitive.log()/n)
        eta2 = Q(t*r-c*c,t*t)
        eta = as_ball(eta2).sqrt()
        width_ratio = as_ball(Q((b-a).numerator,(b-a).denominator))/eta
        width_ratio_record = ball_record(width_ratio)
        q_eta_record = ball_record(q*eta)
    rec.update(n=n,center_denominator=str(center.denominator),
               denominator_lower_rate=log_rate(Q(lower),n),
               center_denominator_rate=log_rate(Q(center.denominator),n),
               interval=[str(a),str(b)],interval_width_over_eta=width_ratio_record,
               interval_minimum_denominator=str(q),interval_minimum_numerator=str(p),
               interval_minimum_denominator_rate=log_rate(Q(q),n),
               farey_parents=[str(z) for z in parents],search_steps=steps,
               rank_one_projector_integer_vector=[str(z) for z in ell],
               interval_q_eta=q_eta_record,primitive_abs=primitive_record,
               primitive_abs_log_rate=primitive_rate,primitive_abs_below_one=bool(primitive<1))
    return rec


def main():
    toy = toy_checks()
    targets = {2,12,20,48,96,192}
    f = Mat(independent_columns(2))
    rows = []
    for n in range(2,max(targets)+1,2):
        if n in targets:
            rows.append(actual_case(n,f))
            print(json.dumps({k:rows[-1][k] for k in
                              ('n','denominator_lower_rate','center_denominator_rate',
                               'interval_minimum_denominator_rate','primitive_abs_log_rate')},
                             ensure_ascii=False),flush=True)
        if n < max(targets):
            f = connection(n)*f
    sources = [Path(__file__),ROOT/'scripts/verify_direction_frontier.py',
               ROOT/'scripts/probe_exterior_cone.py',
               ROOT/'verification/local-connection-2026-09-28/symbolic.json']
    report = dict(result='PASS',date='2026-10-02',actual_matrix_cases=len(rows),
                  actual_local_checks=sum(len(x['local_checks']) for x in rows),
                  **toy,primitive_values_below_one=sum(x['primitive_abs_below_one'] for x in rows),
                  boundary='Finite exact/Arb checks; infinite gcd mass and irrationality remain unproved. No Lean.',
                  source_hashes={str(p.relative_to(ROOT)).replace('\\','/'):
                                 hashlib.sha256(p.read_bytes()).hexdigest() for p in sources})
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'certificate.json').write_text(json.dumps(dict(**report,cases=rows),indent=2)+'\n',encoding='utf-8')
    (OUT/'summary.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2),flush=True)


if __name__ == '__main__':
    main()
