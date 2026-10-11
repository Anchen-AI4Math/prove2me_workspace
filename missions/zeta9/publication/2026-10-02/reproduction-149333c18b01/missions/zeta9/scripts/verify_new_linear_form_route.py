"""Bounded exact verification of an isolated Apery-type zeta(9) form."""
from __future__ import annotations
import hashlib
import json
import math
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT.parents[1]/"tmp/zeta7/exact_packages"))
from flint import fmpq as Q, fmpq_poly as Poly, arb, ctx

X=Poly([0,1])

def qball(q):
    return arb(str(q.numerator))/arb(str(q.denominator))

def vp_int(a,p):
    a=abs(int(a))
    if not a:
        return 10**9
    v=0
    while a%p==0:
        a//=p; v+=1
    return v

def vp(q,p):
    return vp_int(q.numerator,p)-vp_int(q.denominator,p)

def primes(n):
    return [p for p in range(2,n+1)
            if all(p%q for q in range(2,math.isqrt(p)+1))]

LIMIT=256
H={s:[Q(0)] for s in (1,8,9)}
for s,values in H.items():
    for j in range(1,2*LIMIT+1):
        values.append(values[-1]+Q(1,j**s))

def coefficients(n):
    aj=[math.comb(n,j)**2*math.comb(n+j,j)**2 for j in range(n+1)]
    bj=[2*aj[j]*(2*H[1][j]-H[1][n+j]-H[1][n-j])
        for j in range(n+1)]
    assert sum(bj,Q(0))==0
    a=sum(aj)
    b=sum((aj[j]*H[9][j]+bj[j]*H[8][j]/8
           for j in range(n+1)),Q(0))
    return aj,bj,a,b

def endpoint(n):
    # Taylor coefficients of log(R_n(1+z)/[z^2 c_(n,1)]).
    g=[Q(0)]
    for m in range(1,6):
        value=2*Q((-1)**(m-1),m)*(sum((Q(1,(1-j)**m)
                   for j in range(2,n+1)),Q(0))
                 -sum((Q(1,(1+j)**m) for j in range(n+1)),Q(0)))
        g.append(value)
    assert g[1]==-2*H[1][n-1]-2*H[1][n+1]
    expg=[Q(1)]
    for k in range(1,6):
        expg.append(sum((i*g[i]*expg[k-i] for i in range(1,k+1)),Q(0))/k)
    return -Q(math.factorial(7),math.factorial(8)*n*n*(n+1)*(n+1))*expg[5]

def run():
    rows=[]; good_checks=0; prime_checks=0; residue_checks=0
    for n in range(1,25):
        aj,bj,a,b=coefficients(n)
        denominator=Poly([1]); numerator=Poly([1])
        for j in range(n+1):
            denominator*=(X+j)**2
        for j in range(1,n+1):
            numerator*=(X-j)**2
        reconstructed=Poly([0])
        for j in range(n+1):
            quotient,remainder=divmod(denominator,(X+j)**2)
            assert not remainder
            reconstructed+=quotient*(aj[j]+bj[j]*(X+j))
            residue_checks+=1
        assert reconstructed==numerator
        dn=math.lcm(*range(1,n+1))
        assert all((dn*z).denominator==1 for z in bj)
        clearer=8*dn**9
        assert (clearer*b).denominator==1
        g=math.gcd(clearer*a,int(clearer*b))
        c=Q(clearer,g); p=clearer*a//g; q=int(clearer*b)//g
        assert math.gcd(p,q)==1 and p>0 and c*a==p and c*b==q
        assert c==Q(b.denominator,math.gcd(a,int(b.numerator)))
        ctx.prec=20*n+256
        raw=arb(a)*arb(9).zeta()-qball(b)
        primitive=qball(c)*raw
        assert raw>0 and primitive>0
        local=[]
        for ell in primes(n):
            if ell<11 or ell*2<=n:
                continue
            r=n-ell
            ar=sum(math.comb(r,j)**2*math.comb(r+j,j)**2 for j in range(r+1))
            assert (a-5*ar)%ell==0
            scaled=b*ell**9
            assert vp(scaled,ell)>=0
            residue=(int(scaled.numerator)*pow(int(scaled.denominator),-1,ell))%ell
            assert residue==(9*pow(2,-1,ell)*ar)%ell
            good=ar%ell!=0
            if good:
                assert vp(b,ell)==-9 and vp(Q(a),ell)==0 and vp(c,ell)==9
                good_checks+=1
            prime_checks+=1
            local.append({"p":ell,"r":r,"A_r_mod_p":ar%ell,"good":good,
                          "vp_c":vp(c,ell)})
        rows.append({"n":n,"A":str(a),"b":str(b),"safe_clearer":str(clearer),
                     "full_gcd":str(g),"primitive_scale":str(c),"P":str(p),"Q":str(q),
                     "raw_ball":str(raw),"primitive_ball":str(primitive),
                     "primitive_above_one":bool(primitive>1),"large_primes":local})
    # Extra exact prime checks extend only this local theorem, not PF reconstruction.
    extra=[]
    for n in (32,48,64,96,128):
        aj,bj,a,b=coefficients(n)
        c=Q(b.denominator,math.gcd(a,int(b.numerator)))
        for ell in primes(n):
            if ell<11 or ell*2<=n:
                continue
            r=n-ell
            ar=sum(math.comb(r,j)**2*math.comb(r+j,j)**2 for j in range(r+1))
            assert (a-5*ar)%ell==0
            scaled=b*ell**9
            assert vp(scaled,ell)>=0
            assert (int(scaled.numerator)*pow(int(scaled.denominator),-1,ell))%ell==(
                    9*pow(2,-1,ell)*ar)%ell
            if ar%ell:
                assert vp(b,ell)==-9 and vp(c,ell)==9
                good_checks+=1
            prime_checks+=1
        ctx.prec=20*n+256
        raw=arb(a)*arb(9).zeta()-qball(b)
        assert raw>0
        e=endpoint(n)
        normalization=arb(n)**4/arb(n).log()**5
        extra.append({"n":n,"raw_ball":str(raw),"raw_scaled_ball":str(raw*normalization),
                      "endpoint_ball":str(qball(e)),
                      "endpoint_scaled_ball":str(qball(e)*normalization),
                      "relative_remainder_ball":str((raw-qball(e))/raw),
                      "primitive_scale":str(c),"primitive_ball":str(qball(c)*raw)})
    asympt=[]
    for n in (16,32,64,128,256):
        ctx.prec=256
        e=endpoint(n)
        assert e>0
        asympt.append({"n":n,"endpoint_exact":str(e),
                      "endpoint_scaled_ball":str(qball(e)*arb(n)**4/arb(n).log()**5)})
    proof=ROOT/"research/new-linear-form-route-2026-10-02.md"
    script=Path(__file__).resolve()
    certificate={"status":"PASS","lean_verified":False,
                 "partial_fraction_parameters":list(range(1,25)),
                 "residue_polynomial_checks":residue_checks,
                 "prime_congruence_checks":prime_checks,"good_prime_exact_valuation_checks":good_checks,
                 "extra_local_and_ball_parameters":[32,48,64,96,128],
                 "endpoint_parameters":[16,32,64,128,256],
                 "proof_sha256":hashlib.sha256(proof.read_bytes()).hexdigest(),
                 "script_sha256":hashlib.sha256(script.read_bytes()).hexdigest(),
                 "main_cases":rows,"selected_larger_cases":extra,"endpoint_cases":asympt,
                 "limits":"Finite checks do not prove a bound on exceptional-prime mass or full primitive gcd."}
    out=ROOT/"verification/new-linear-form-route-2026-10-02"
    out.mkdir(parents=True,exist_ok=True)
    (out/"certificate.json").write_text(json.dumps(certificate,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:certificate[k] for k in ("status","residue_polynomial_checks",
                     "prime_congruence_checks","good_prime_exact_valuation_checks")},indent=2))

if __name__=="__main__":
    run()
