"""Small exact checks for the eightfold-zero isolated zeta(9) repair."""
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

def ball(q):
    return arb(str(q.numerator))/arb(str(q.denominator))

def run():
    H={s:[Q(0)] for s in (1,8,9)}
    for s,v in H.items():
        for j in range(1,31):
            v.append(v[-1]+Q(1,j**s))
    rows=[]; zeros=0; residues=0
    for n in range(1,7):
        aj=[math.comb(4*n,j)**2*math.comb(n+j,n)**8 for j in range(4*n+1)]
        bj=[aj[j]*(10*H[1][j]-8*H[1][n+j]-2*H[1][4*n-j])
            for j in range(4*n+1)]
        assert sum(bj,Q(0))==0
        numerator=Poly([Q(math.factorial(4*n)**2,math.factorial(n)**8)])
        denominator=Poly([1])
        for j in range(1,n+1):
            numerator*=(X-j)**8
        for j in range(4*n+1):
            denominator*=(X+j)**2
        reconstructed=Poly([0])
        for j in range(4*n+1):
            quotient,remainder=divmod(denominator,(X+j)**2)
            assert not remainder
            reconstructed+=quotient*(aj[j]+bj[j]*(X+j))
            residues+=1
        assert numerator==reconstructed
        derivative=numerator
        for order in range(8):
            for j in range(1,n+1):
                assert derivative(j)==0 and denominator(j)!=0
                zeros+=1
            derivative=derivative.derivative()
        dn=math.lcm(*range(1,4*n+1))
        assert all((dn*b).denominator==1 for b in bj)
        a=sum(aj)
        b=sum((aj[j]*H[9][j]+bj[j]*H[8][j]/8
               for j in range(4*n+1)),Q(0))
        clearer=8*dn**9
        assert (clearer*b).denominator==1
        g=math.gcd(clearer*a,int(clearer*b))
        c=Q(clearer,g)
        p=clearer*a//g; q=int(clearer*b)//g
        assert math.gcd(p,q)==1 and c==Q(b.denominator,math.gcd(a,int(b.numerator)))
        ctx.prec=512+64*n
        raw=arb(a)*arb(9).zeta()-ball(b)
        assert raw>0 or raw<0
        primitive=ball(c)*raw
        rows.append({"n":n,"A":str(a),"b":str(b),"safe_clearer":str(clearer),
                     "full_content":str(g),"primitive_scale":str(c),"P":str(p),"Q":str(q),
                     "raw_ball":str(raw),"primitive_ball":str(primitive),
                     "observed_positive":bool(raw>0),"primitive_abs_above_one":bool(abs(primitive)>1)})
    note=ROOT/"research/new-linear-form-route-repair-2026-10-02.md"
    cert={"status":"PASS","lean_verified":False,"parameters":list(range(1,7)),
          "residue_polynomial_checks":residues,"endpoint_zero_derivative_checks":zeros,
          "proof_sha256":hashlib.sha256(note.read_bytes()).hexdigest(),
          "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          "cases":rows,"limits":"No all-parameter sign, nonvanishing, error rate or primitive-content estimate is proved by these cases."}
    out=ROOT/"verification/new-linear-form-route-repair-2026-10-02"
    out.mkdir(parents=True,exist_ok=True)
    (out/"certificate.json").write_text(json.dumps(cert,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({"status":"PASS","residue_polynomial_checks":residues,
                      "endpoint_zero_derivative_checks":zeros,
                      "signs":[[r["n"],r["observed_positive"]] for r in rows],
                      "primitive_abs_above_one":[[r["n"],r["primitive_abs_above_one"]] for r in rows]},indent=2))

if __name__=="__main__":
    run()
