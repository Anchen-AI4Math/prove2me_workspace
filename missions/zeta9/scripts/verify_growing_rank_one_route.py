"""Exact growing-dimension isolated zeta(9) forms and certified error bounds."""
from pathlib import Path
import hashlib
import json
import math
from probe_positive_hankel import Q, Mat, arb, ctx, moment

ROOT=Path(__file__).resolve().parents[1]


def ball(q):
    q=Q(q)
    return arb(int(q.numer()))/int(q.denom())


def primes(n):
    return [p for p in range(2,n+1) if all(p%q for q in range(2,math.isqrt(p)+1))]


def large_part(n, small_primes):
    n=abs(int(n))
    assert n>0
    for p in small_primes:
        while n%p==0: n//=p
    return n


def constants(c):
    ctx.prec=512
    pi=arb.pi()
    def derivative(t):
        return 4/t-2*((c+2)/t).atan()+2*(c/t).atan()-2*pi
    lo,hi=Q(1,1000),Q(10)
    assert derivative(ball(lo))>0 and derivative(ball(hi))<0
    for _ in range(160):
        mid=(lo+hi)/2
        value=derivative(ball(mid))
        if value>0: lo=mid
        elif value<0: hi=mid
        else: raise AssertionError('derivative sign precision')
    bracket=(ball(lo)+ball(hi))/2+arb(0,ball(hi-lo)/2)
    def antiderivative(x):
        return x*(bracket*bracket+x*x).log()-2*x+2*bracket*(x/bracket).atan()
    integral=antiderivative(arb(c+2))-antiderivative(arb(c))
    value=4*bracket.log()-integral-2*pi*bracket
    assert value<0
    return {'c':c,'maximizer_lower':str(lo),'maximizer_upper':str(hi),
            'f_c_ball':value.str(35),'sufficient_denominator_rate_threshold':(-value).str(35),
            'sufficient_failure_rate_threshold':(arb(16).log()-value).str(35)}


def construct(h,M):
    m=2*h+3
    poles=list(range(M+1,M+m+1))
    harmonics={}
    running=Q(0)
    for j in range(1,poles[-1]+1):
        running+=Q(1,j**9)
        if j in poles: harmonics[j]=running
    residues={a:Q(1,math.prod(b*b-a*a for b in poles if b!=a)) for a in poles}
    constants_a={a:-a**8*harmonics[a]-Q(1,8)+Q(1,2*a) for a in poles}
    entries=[]
    for k in range(2*h-1):
        const=sum((residues[a]*(-a*a)**k*constants_a[a] for a in poles),Q(0))
        linear=sum((residues[a]*(-a*a)**k*a**8 for a in poles),Q(0))
        assert linear==int(k==2*h-2)
        entries.append(const)
    A=Mat([[entries[i+j] for j in range(h)] for i in range(h)])
    B=Mat(h,h); B[h-1,h-1]=1
    if h>1:
        C=Mat([[A[i,j] for j in range(h-1)] for i in range(h-1)])
        v=Mat([[A[i,h-1]] for i in range(h-1)])
        slope=C.det()
        solved=C.inv()*v
        q=-A[h-1,h-1]+(v.transpose()*solved)[0,0]
        minors=[slope]+[slope*solved[i,0] for i in range(h-1)]
    else:
        slope=Q(1);q=-A[0,0];minors=[Q(1)]
    assert slope>0
    for z in (-1,0,1,2):
        assert (A+z*B).det()==slope*(z-q)
    T,U=int(q.denom()),int(q.numer())
    assert T>0 and math.gcd(T,U)==1
    scalar=Q(T)/slope
    assert scalar*(-slope*q)==-U and scalar*slope==T
    small_primes=primes(2*poles[-1])
    assert all(large_part(c.denom(),small_primes)==1 for c in A.entries())
    F=large_part(slope.numer(),small_primes)
    gcd_numerators=math.gcd(*(abs(int(c.numer())) for c in minors))
    J=large_part(gcd_numerators,small_primes)
    T_large=large_part(T,small_primes)
    assert T_large*J*J%F==0 and F%T_large==0
    assert Q(T)>=Q(F,J*J)
    if J==1: assert T_large==F
    ctx.prec=max(512,max(T.bit_length(),abs(U).bit_length())+384)
    zeta=arb(9).zeta()
    error=zeta-ball(q)
    value=T*zeta-U
    assert error>0 and value>0 and error.rel_accuracy_bits()>80
    assert (value-T*error).contains(0)
    # All-parameter computable upper bound using the monomial trial.
    simple_upper=moment(9,2*h-2)/math.prod(a*a for a in poles)
    assert error < ball(simple_upper)
    # Exact monic Legendre norm on a scaled positive interval.
    alpha,beta=Q(1,10),Q(1,2)
    length=beta*beta-alpha*alpha
    monic_norm=length**(2*h-1)/((2*h-1)*math.comb(2*h-2,h-1)**2)
    D_beta=math.prod(beta*beta*h*h+a*a for a in poles)
    prefactor=alpha**9/(2*beta)*Q(h**(4*h+6))/D_beta*monic_norm
    lower=2*(2*arb.pi())**8/math.factorial(8)*ball(prefactor)*(-2*arb.pi()*ball(beta)*h).exp()
    assert error > lower
    return {'h':h,'M':M,'m':m,'degree':1,'exact_approximation_numerator':str(U),
            'exact_approximation_denominator':str(T),'denominator_digits':len(str(T)),
            'gram_leading_slope':str(slope),'primitive_positive_multiplier':str(scalar),
            'error_ball':error.str(30),'primitive_value_ball':value.str(30),
            'log_error_over_h':(error.log()/h).str(25),
            'log_denominator_over_h':(ball(T).log()/h).str(25),
            'log_primitive_over_h':(value.log()/h).str(25),
            'finite_legendre_lower_ball':lower.str(25),'monomial_upper':str(simple_upper),
            'below_one':bool(value<1),'precision_bits':ctx.prec,
            'large_prime_cutoff':2*poles[-1],'large_determinant_numerator_F':str(F),
            'large_rectangular_minor_gcd_J':str(J),'large_primitive_denominator':str(T_large),
            'all_large_prime_identity_if_J_one':bool(J==1 and T_large==F)}


def main():
    rows=[]
    for h in range(1,13):
        for c in (0,1,2):
            row=construct(h,c*h); rows.append(row)
            print(json.dumps({k:row[k] for k in ('h','M','log_error_over_h','log_denominator_over_h','log_primitive_over_h')}),flush=True)
    for h in (16,24,32):
        row=construct(h,0); rows.append(row)
        print(json.dumps({k:row[k] for k in ('h','M','log_error_over_h','log_denominator_over_h','log_primitive_over_h')}),flush=True)
    note=ROOT/'research/growing-rank-one-route-2026-10-02.md'
    summary={'result':'PASS','case_count':len(rows),'below_one_cases':sum(row['below_one'] for row in rows),
             'large_minor_gcd_one_cases':sum(row['large_rectangular_minor_gcd_J']=='1' for row in rows),
             'exponential_constants':[constants(c) for c in (0,1,2)],
             'source_hashes':{str(p.relative_to(ROOT)).replace('\\','/'):hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in (Path(__file__),note,ROOT/'scripts/probe_positive_hankel.py')},
             'boundary':'Finite exact/Arb checks; infinite error squeeze is written proof. Required primitive denominator asymptotic remains open; no Lean.'}
    out=ROOT/'verification/growing-rank-one-route-2026-10-02';out.mkdir(parents=True,exist_ok=True)
    (out/'certificate.json').write_text(json.dumps({**summary,'cases':rows},indent=2)+'\n',encoding='utf-8')
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
