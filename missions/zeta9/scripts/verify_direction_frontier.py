"""Exact moving rational projection and Gram gcd frontier; finite evidence only."""
from pathlib import Path
from fractions import Fraction
from math import gcd, lcm
import hashlib, json, sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from probe_exterior_cone import Q, Mat, connection
from flint import arb, ctx, fmpz
sys.path.insert(0, str(ROOT / 'round6/scripts'))
from independent_audit import independent_columns
sys.set_int_max_str_digits(0)
OUT = ROOT / 'verification/direction-frontier-2026-10-01'


def as_ball(q):
    return arb(fmpz(q.numer())) / arb(fmpz(q.denom()))


def ball_record(x):
    mid, rad, exp = x.mid_rad_10exp(35)
    return dict(mid=str(mid), rad=str(rad), exp=int(exp), approx=float(x))


def log_rate(q, n):
    with ctx.workprec(256):
        return ball_record((arb(fmpz(q.numer())).log() - arb(fmpz(q.denom())).log()) / n)


def analyze(n, f):
    inv = f.inv()
    e = Mat([[inv[i,j] * n**(2*j) for j in range(5)] for i in (0,4)])
    gram = e * e.transpose()
    a, b, c = gram[0,0], gram[0,1], gram[1,1]
    det = a*c-b*b
    assert a>0 and det>0
    xi = b/a
    eta2 = det/(a*a)
    center_p, center_q = int(xi.numer()), int(xi.denom())
    assert gcd(center_p, center_q)==1 and center_q>0
    common = lcm(*(int(e[i,j].denom()) for i in range(2) for j in range(5)))
    u = [int(common*e[0,j]) for j in range(5)]
    v = [int(common*e[1,j]) for j in range(5)]
    t_int = sum(x*x for x in u)
    s_int = sum(x*y for x,y in zip(u,v))
    v_int = sum(x*x for x in v)
    det_int = t_int*v_int-s_int*s_int
    g = gcd(t_int, s_int)
    assert t_int==common**2*a and s_int==common**2*b
    assert det_int==common**4*det and det_int>0
    assert center_q==t_int//g and center_p==s_int//g
    normalized_gcd2 = Q(g*g, det_int)
    assert normalized_gcd2 == 1/(center_q**2*eta2)
    projected = [-center_p*e[0,j]+center_q*e[1,j] for j in range(5)]
    projected_norm2 = sum(x*x for x in projected)
    assert projected_norm2 == center_q**2*det/a
    assert sum(projected[j]*e[0,j] for j in range(5))==0
    for scale in (2,7):
        t2,s2,d2 = t_int*scale**2, s_int*scale**2, det_int*scale**4
        assert Q(gcd(t2,s2)**2,d2)==normalized_gcd2
    # Under a hypothetical rational theta=c/d, the gcd always divides d*S-c*T.
    for cp,dq in ((1,1),(513,512),(1003,1000),(-2,7)):
        assert (dq*s_int-cp*t_int)%g==0
    fixed = []
    for j in range(5):
        if e[0,j]:
            r=e[1,j]/e[0,j]
            fixed.append(dict(j=j, denominator=str(r.denom()),
                              denominator_rate=log_rate(Q(r.denom()),n)))
    with ctx.workprec(max(512,32*n+512)):
        err=arb(9).zeta()-as_ball(xi)
        primitive=abs(err)*center_q
        assert not err.contains(0) and primitive>0
        kappa2=err*err/as_ball(eta2)
        assert (primitive*primitive-kappa2/as_ball(normalized_gcd2)).contains(0)
        primitive_ball=ball_record(primitive)
        primitive_log=ball_record(primitive.log()/n)
        kappa_ball=ball_record(kappa2)
        below_one=bool(primitive<1)
        error_sign=1 if err>0 else -1
    return dict(n=n, center_numerator=str(center_p), center_denominator=str(center_q),
                center_denominator_rate=log_rate(Q(center_q),n), eta_squared=str(eta2),
                common_integer_scale=str(common), integer_gram=[str(t_int),str(s_int),str(v_int)],
                gram_gcd=str(g), integer_gram_determinant=str(det_int),
                normalized_gcd_squared=str(normalized_gcd2),
                normalized_gcd_squared_rate=log_rate(normalized_gcd2,n),
                normalized_gcd_squared_above_one=bool(normalized_gcd2>1),
                primitive_abs=primitive_ball, primitive_abs_log_rate=primitive_log,
                kappa_squared=kappa_ball, primitive_abs_below_one=below_one,
                error_sign=error_sign, coordinate_denominators=fixed)


def main():
    targets={2,12,14,20,48,50,96,98,192,194}
    f=Mat(independent_columns(2)); records=[]
    for n in range(2,max(targets)+1,2):
        if n in targets:
            records.append(analyze(n,f))
            r=records[-1]
            print(json.dumps({k:r[k] for k in ('n','center_denominator_rate','normalized_gcd_squared_rate',
                                               'primitive_abs_log_rate','error_sign')},ensure_ascii=False),flush=True)
        if n<max(targets): f=connection(n)*f
    signs={r['n']:r['error_sign'] for r in records}
    for left,right in ((12,14),(48,50),(96,98),(192,194)):
        assert signs[left]==-signs[right]
    toy_cases=0
    for m in range(2,25):
        # Both row modules have Smith factors (1,1), same t^2 and area ratio ->1.
        t=m*m+1
        assert gcd(1,m)==1
        assert Q(gcd(t,0)**2,t)==t
        assert Q(gcd(t,m)**2,m*m+2)==Q(1,m*m+2)
        toy_cases+=1
    cone_path=ROOT/'verification/exterior-cone-2026-09-29/certificate.json'
    cone=json.loads(cone_path.read_text(encoding='utf-8'))
    al,ah=map(Q,cone['eigenvalue_intervals']['A'])
    bl,bh=map(Q,cone['eigenvalue_intervals']['B'])
    with ctx.workprec(256):
        threshold_lower=(as_ball(al).log()-as_ball(bh).log())/2
        threshold_upper=(as_ball(ah).log()-as_ball(bl).log())/2
        threshold=dict(lower=ball_record(threshold_lower),upper=ball_record(threshold_upper))
    result=dict(result='PASS', date='2026-10-01',
                boundary='Finite exact/Arb validation; all-sequence conclusions require written proofs. No Lean.',
                cases=records, matrix_cases=len(records), adjacent_sign_checks=4, smith_gcd_toy_cases=toy_cases,
                primitive_center_values_below_one=sum(r['primitive_abs_below_one'] for r in records),
                normalized_gcd_ratios_above_one=sum(r['normalized_gcd_squared_above_one'] for r in records),
                alpha_minus_beta_interval=threshold,
                source_hashes={str(p.relative_to(ROOT)).replace('\\','/'):hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in [Path(__file__), cone_path,
                            ROOT/'verification/local-connection-2026-09-28/symbolic.json']})
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'certificate.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','source_hashes')},indent=2),flush=True)

if __name__=='__main__':main()
