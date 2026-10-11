"""Finite primitive integer forms from the positive single-square-pole measure.

The affine determinant identity is checked against three direct determinants.
This is a bounded experiment, not an asymptotic irrationality criterion.
"""
from pathlib import Path
import sys, math, json, hashlib
M = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(M/'scripts'))
from probe_positive_hankel import moment, Q, Mat, arb, ctx


def case(s, a, h):
    harmonic = sum((Q(1,j**s) for j in range(1,a+1)), Q(0))
    pole0 = -a**(s-1)*harmonic-Q(1,s-1)+Q(1,2*a)
    # t^k/(t+a^2) = sum_{j=0}^{k-1}(-a^2)^j t^(k-1-j)
    #                  + (-a^2)^k/(t+a^2).
    v = []
    for k in range(2*h-1):
        v.append(sum(((-a*a)**j*moment(s,k-1-j) for j in range(k)),Q(0))
                 +(-a*a)**k*pole0)
    A=Mat([[v[i+j] for j in range(h)] for i in range(h)])
    B=Mat([[Q(a**(s-1)*(-a*a)**(i+j)) for j in range(h)] for i in range(h)])
    c0=A.det(); c1=(A+B).det()-c0
    assert c1 > 0
    for x in (-1,2,3): assert (A+x*B).det()==c0+x*c1
    den=math.lcm(int(c0.denom()),int(c1.denom()))
    ints=[int((c*den).numer()) for c in (c0,c1)]
    common=math.gcd(*ints); ints=[c//common for c in ints]
    assert math.gcd(*ints)==1 and ints[1]>0
    precision=max(512,max(abs(c).bit_length() for c in ints)+256)
    for _ in range(5):
        ctx.prec=precision
        value=ints[0]+ints[1]*arb(s).zeta()
        if value>0 and value.rel_accuracy_bits()>80: break
        precision*=2
    else: raise AssertionError('insufficient ball precision')
    return {'s':s,'pole':a,'dimension':h,'degree':1,
            'integer_constant':str(ints[0]),'integer_slope':str(ints[1]),
            'positive_scalar':str(Q(den,common)),
            'value_ball':value.str(35),'log_value_ball':value.log().str(35),
            'log_value_display':float(value.log().mid()),'precision_bits':precision,
            'direct_determinant_checks':3}


def main():
    cases=[case(s,a,h) for s in (3,9) for a in (1,2,4,8,16)
           for h in (2,4,8,12,16,24)]
    for s in (3,9):
        subset=[c for c in cases if c['s']==s]
        best=min(subset,key=lambda c:c['log_value_display'])
        print(json.dumps({'s':s,'count':len(subset),'best':best}),flush=True)
    out=M/'verification/positive-hankel-2026-09-29/single-pole.json'
    out.write_text(json.dumps({'cases':cases,
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'moment_dependency_sha256':hashlib.sha256((M/'scripts/probe_positive_hankel.py').read_bytes()).hexdigest(),
      'boundary':'Finite exact primitive forms and Arb evaluations only; no asymptotic conclusion.'},indent=2)+'\n',encoding='utf-8')


if __name__=='__main__': main()
