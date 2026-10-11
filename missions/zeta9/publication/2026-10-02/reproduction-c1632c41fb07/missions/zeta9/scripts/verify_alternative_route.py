"""Exact Mellin tail Gram experiment, plus dilation/derivative obstructions.

All polynomial coefficients are rational/integer; displayed decimals only
summarize exact rational enclosures obtained from Euler--Maclaurin.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial, prod, lcm, gcd
import json
import sympy as sp

ROOT=Path(__file__).resolve().parents[1]

def zeta_interval(s=9, M=120, K=80):
    z=sum((sp.Rational(1,k**s) for k in range(1,M)),sp.S.Zero)
    z+=sp.Rational(1,(s-1)*M**(s-1))+sp.Rational(1,2*M**s)
    terms=[]
    for j in range(1,K+1):
        term=sp.bernoulli(2*j)*sp.rf(s,2*j-1)/factorial(2*j)/M**(s+2*j-1)
        terms.append(term)
        z+=term
    # The periodic-Bernoulli remainder after K terms has absolute value
    # at most abs(last term); this deliberately avoids using alternation.
    err=abs(terms[-1])
    return z-err,z+err

def gram_case(exponents, zlo,zhi):
    e=tuple(exponents)
    assert len(e)==len(set(e)) and min(e)>=0
    H=[sp.S.Zero]
    for j in range(1,2*max(e)+1): H.append(H[-1]+sp.Rational(1,j**9))
    if len(e)==1:
        q=H[2*e[0]]; cdet=sp.S.One
    else:
        h0=H[2*e[0]]
        b=sp.Matrix([h0-H[e[0]+j] for j in e[1:]])
        C=sp.Matrix([[-H[i+j]+H[i+e[0]]+H[j+e[0]]-h0
                      for j in e[1:]] for i in e[1:]])
        cdet=C.det(method='domain-ge')
        assert cdet>0
        q=h0+(b.T*C.inv(method='DM')*b)[0]
    p=int(sp.denom(q)); a=int(sp.numer(q))
    assert gcd(p,a)==1
    lo=p*zlo-a; hi=p*zhi-a
    assert lo>0, ('precision insufficient',e)
    D=max(e)
    kernel=sum((2*k+8)*sp.binomial(k+7,7)**2 for k in range(D+1))
    assert kernel==sp.Rational((D+8)**2,8)*sp.binomial(D+7,7)**2
    return {'exponents':e,'P':str(p),'Q':str(a),'P_digits':len(str(p)),
            'primitive_value_interval':[str(lo),str(hi)],
            'primitive_value_decimal':[str(lo.evalf(20)),str(hi.evalf(20))],
            'below_one':bool(hi<1), 'cofactor_positive':bool(cdet>0),
            'jacobi_lower_bound':str(sp.Rational(p,factorial(8)*kernel)),
            'exact_height_obstruction_ge_one':bool(p>=factorial(8)*kernel)}

def main():
    zlo,zhi=zeta_interval()
    patterns=[list(range(n)) for n in range(1,11)]
    patterns += [[0,1,3],[0,2,3],[0,1,2,4],[0,1,3,4],
                 [0,2,3,4],[0,2,4,6],[0,1,2,3,5],[0,1,3,5,7],
                 [1,2,3,4],[2,3,4,5],[0,2,4,6,8],[0,1,4,7,10]]
    rows=[gram_case(e,zlo,zhi) for e in patterns]
    assert all(r['exact_height_obstruction_ge_one'] for r in rows if len(r['exponents'])>=3)
    # Rodrigues norms and endpoint values: independent finite witnesses for
    # the all-degree integration-by-parts argument in the note.
    x=sp.Symbol('x')
    for k in range(7):
        J=sp.cancel((-1)**k*sp.diff(x**k*(1-x)**(k+7),x,k)/factorial(k)/(1-x)**7)
        assert J.subs(x,1)==sp.binomial(k+7,7)
        assert sp.integrate(sp.expand(J**2*(1-x)**7),(x,0,1))==sp.Rational(1,2*k+8)
    D=sp.Symbol('D',integer=True,positive=True)
    kernel_closed=lambda d:(d+8)**2*sp.prod(d+j for j in range(1,8))**2/(8*factorial(7)**2)
    assert sp.factor(kernel_closed(D)-kernel_closed(D-1)-(2*D+8)*sp.prod(D+j for j in range(1,8))**2/factorial(7)**2)==0
    # Independent symbolic determinants for the first genuinely quadratic
    # and cubic examples, rather than only rechecking our Schur formula.
    X=sp.Symbol('X')
    for e in [(0,1),(0,1,2),(0,1,3)]:
        mat=sp.Matrix([[X-sum((sp.Rational(1,k**9) for k in range(1,i+j+1)),sp.S.Zero)
                        for j in e] for i in e])
        poly=sp.Poly(mat.det(),X)
        assert poly.degree()==1
        q=-poly.nth(0)/poly.nth(1)
        row=next(r for r in rows if tuple(r['exponents'])==e)
        assert q==sp.Rational(row['Q'],row['P'])
    # Dilation: four distinct positive nodes give rank 3 for nuisance
    # exponents 3,5,7, with nonzero ninth and first profiles.
    nodes=[1,2,3,6]
    nuisance=sp.Matrix([[d**s for d in nodes] for s in [3,5,7]])
    w=nuisance.nullspace()[0]
    den=sp.ilcm(*[sp.denom(x) for x in w])
    w=[int(x*den) for x in w]
    assert nuisance*sp.Matrix(w)==sp.zeros(3,1)
    profiles={s:sum(c*d**s for c,d in zip(w,nodes)) for s in [1,3,5,7,9]}
    assert profiles[1]!=0 and profiles[9]!=0
    assert len(sp.divisors(6))==4 and all(len(sp.divisors(d))<4 for d in range(1,6))
    # Completely monotone derivative family: exact residue cancellation.
    derivative=[]
    for poles in [(0,1),(0,1,2),(0,1,3),(1,3,4)]:
        a2=[F(1,prod((b-a)**2 for b in poles if b!=a)) for a in poles]
        a1=[-2*c*sum((F(1,b-a) for b in poles if b!=a),F(0)) for a,c in zip(poles,a2)]
        assert sum(a1)==0
        t=sp.Symbol('t')
        R=1/prod((t+a)**2 for a in poles)
        partial=sum(sp.Rational(c.numerator,c.denominator)/(t+a)**2+
                    sp.Rational(d.numerator,d.denominator)/(t+a)
                    for a,c,d in zip(poles,a2,a1))
        assert sp.cancel(R-partial)==0
        derivative.append({'poles':poles,'double':[str(x) for x in a2],
                           'simple':[str(x) for x in a1]})
    out={'scope':'22 exact patterns, universal Jacobi height obstruction proved in companion note',
         'gram_cases':rows,'dilation':{'nodes':nodes,'weights':w,'profiles':profiles},
         'derivative_partial_fractions':derivative,
         'zeta_enclosure':{'M':120,'K':80,'lower':str(zlo),'upper':str(zhi)},
         'all_checks':'PASS'}
    dest=ROOT/'verification'/'alternative-route-2026-09-29'
    dest.mkdir(parents=True,exist_ok=True)
    (dest/'certificate.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
    for r in rows: print(r['exponents'],r['P_digits'],r['primitive_value_decimal'][0],r['below_one'])
    print('dilation',w,profiles)
    print('PASS',dest/'certificate.json')

if __name__=='__main__':main()
