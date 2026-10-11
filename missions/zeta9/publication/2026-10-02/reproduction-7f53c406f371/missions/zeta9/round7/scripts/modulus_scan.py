"""Exact finite modulus hierarchy for the rank-two zeta(9) Round6 kernel."""
from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"tmp/zeta7/exact_packages"))
from flint import arb,ctx,fmpz  # type: ignore

R6=ROOT/"missions/zeta9/round6/verification"
OUT=ROOT/"missions/zeta9/round7/verification/modulus-scan.json"
BASE=R6/"arithmetic-congruence-audit.json"


def read_input(n):
    path=R6/f"search-input-n{n}.json.gz"
    with gzip.open(path,"rt",encoding="utf-8") as stream:
        return json.load(stream),path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def matmul_2(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(len(B[0]))]
            for i in range(2)]


def gram(rows,weights):
    a=sum((rows[0][j]*weights[j])**2 for j in range(len(weights)))
    b=sum(rows[0][j]*rows[1][j]*weights[j]**2 for j in range(len(weights)))
    c=sum((rows[1][j]*weights[j])**2 for j in range(len(weights)))
    if a<=0 or c<=0 or a*c<=b*b:
        raise AssertionError("Gram is not positive definite")
    return a,b,c


def nearest(x,y):
    """Nearest integer to x/y, with half ties toward +infinity."""
    if y<=0:
        raise ValueError("denominator must be positive")
    return (2*x+y)//(2*y)


def inner(v,w,G):
    a,b,c=G
    return a*v[0]*w[0]+b*(v[0]*w[1]+v[1]*w[0])+c*v[1]*w[1]


def gauss(G):
    x,y=[1,0],[0,1]
    for steps in range(10000):
        A=inner(x,x,G)
        C=inner(y,y,G)
        if C<A:
            x,y=y,x
            continue
        m=nearest(inner(x,y,G),A)
        if m:
            y=[y[i]-m*x[i] for i in range(2)]
            continue
        B=inner(x,y,G)
        if 2*abs(B)>A or abs(x[0]*y[1]-x[1]*y[0])!=1:
            raise AssertionError("Gauss reduction certificate failed")
        return [x,y],[A,B,C],steps
    raise RuntimeError("Gauss iteration cap")


def log_bound_ball(n,D,s1,delta_squared,mu_squared):
    bits=256
    while bits<=4096:
        with ctx.workprec(bits):
            value=(arb(2).log()-arb(3).log()/2+arb(fmpz(D)).log()
                   -arb(fmpz(s1)).log()+arb(fmpz(delta_squared)).log()/2
                   -arb(fmpz(mu_squared)).log()/2)/n
            decisions={}
            for label,numer,denom in (("10.43",1043,100),
                                      ("10.564",2641,250)):
                target=arb(fmpz(numer))/denom
                if value.upper()<target.lower():
                    decisions[label]="below"
                elif value.lower()>target.upper():
                    decisions[label]="above"
            if len(decisions)<2:
                bits*=2
                continue
            mid,rad,exp=value.mid_rad_10exp(40)
            return {"threshold_comparisons":decisions,
                    "status":decisions["10.43"]+"_10.43",
                    "mid":str(mid),"rad":str(rad),
                    "exp":int(exp),"approx":float(value),"arb_bits":bits}
    raise ArithmeticError("Threshold interval unresolved")


def log_ratio_ball(n,numerator,denominator,half=False):
    with ctx.workprec(256):
        value=(arb(fmpz(numerator)).log()-arb(fmpz(denominator)).log())/n
        if half:
            value/=2
        mid,rad,exp=value.mid_rad_10exp(40)
        return {"mid":str(mid),"rad":str(rad),"exp":int(exp),
                "approx":float(value),"arb_bits":256}


def smooth_part(N,small,cutoff):
    part=1
    used=[]
    for p,e in small:
        p,e=int(p),int(e)
        if p<=cutoff:
            part*=p**e
            used.append([p,e])
    if N%part:
        raise AssertionError("Recorded small-prime part does not divide N")
    return part,used


def tiers(n,N,input_data):
    d=math.lcm(*range(1,n+1))
    options=[("g1",1)]
    for e in (1,2,4,8,16):
        options.append((f"gcd_N_d_n_pow_{e}",math.gcd(N,d**e)))
    recorded=input_data["small_prime_part"]["s2"]["prime_powers"]
    for cutoff in (100,2*n,int(input_data["small_prime_part"]["s2"]["trial_bound"])):
        val,used=smooth_part(N,recorded,cutoff)
        options.append((f"recorded_smooth_le_{cutoff}",val))
    options.append(("full_N",N))
    by_value={}
    for name,g in options:
        if N%g:
            raise AssertionError("Candidate modulus does not divide N")
        by_value.setdefault(g,[]).append(name)
    return [(g,names) for g,names in sorted(by_value.items())],d


def one_case(n,audit):
    began=time.monotonic()
    inp,path=read_input(n)
    smith=audit["smith_certificate"]
    K=[[int(x) for x in row] for row in inp["integer_W_basis_K_rows"]]
    J=[[int(x) for x in row] for row in inp["J_rows_B_A"]]
    U=[[int(x) for x in row] for row in smith["U"]]
    V=[[int(x) for x in row] for row in smith["V"]]
    D=int(inp["common_denominator_Q"])
    s1,s2,N=(int(smith[key]) for key in ("s1","s2","N"))
    if audit["input_sha256"]!=digest(path) or int(audit["D"])!=D:
        raise AssertionError("Smith archive refers to different input")
    assert matmul_2(matmul_2(U,J),V)==[[s1,0],[0,s2]]
    assert s2==s1*N and abs(U[0][0]*U[1][1]-U[0][1]*U[1][0])==1
    assert abs(V[0][0]*V[1][1]-V[0][1]*V[1][0])==1
    UK=matmul_2(U,K)
    factors=[[int(p),int(e)] for p,e in inp["small_prime_part"]["s2"]["prime_powers"]]
    cofactor=int(inp["small_prime_part"]["s2"]["unresolved_cofactor"])
    assert s1==1 and cofactor==1 and math.prod(p**e for p,e in factors)==N
    assert all(p>1 and all(p%d for d in range(2,math.isqrt(p)+1))
               for p,e in factors)
    candidates,d=tiers(n,N,inp)
    modes=[]
    for label,weights in (("unweighted",[1]*5),
                          ("n2r",[n**(2*r) for r in range(5)])):
        Kgram=gram(K,weights)
        delta_squared=Kgram[0]*Kgram[2]-Kgram[1]**2
        rows=[]
        for g,names in candidates:
            basis=[[g*x for x in UK[0]],list(UK[1])]
            initial=gram(basis,weights)
            H,red,steps=gauss(initial)
            reduced_rows=matmul_2(H,basis)
            if tuple(red)!=gram(reduced_rows,weights):
                raise AssertionError("Gauss row/Gram transformation mismatch")
            assert red[0]*red[2]-red[1]**2==g*g*delta_squared
            mu_squared=red[0]
            bound_squared=Fraction(4*D*D*delta_squared,
                                   3*s1*s1*mu_squared)
            log_ball=log_bound_ball(n,D,s1,delta_squared,mu_squared)
            rows.append({"g":g,"labels":names,"g_divides_N_quotient":N//g,
                         "basis_rows_diag_g_1_UK":basis,
                         "initial_gram_A_B_C":list(initial),
                         "gauss_unimodular_H":H,"gauss_reduced_rows":reduced_rows,
                         "gauss_reduced_gram_A_B_C":red,"gauss_steps":steps,
                         "mu1_squared":mu_squared,
                         "det_gram_equals_g_squared_deltaK_squared":True,
                         "lambda2_upper_squared_numerator_denominator":
                             [bound_squared.numerator,bound_squared.denominator],
                         "log_lambda2_upper_per_n":log_ball})
        first=next((r for r in rows if r["log_lambda2_upper_per_n"]["status"]
                    =="below_10.43"),None)
        first_new=next((r for r in rows if r["log_lambda2_upper_per_n"]
                        ["threshold_comparisons"]["10.564"]=="below"),None)
        one=next(r for r in rows if "g1" in r["labels"])
        two=next(r for r in rows if "gcd_N_d_n_pow_2" in r["labels"])
        ratio=Fraction(two["mu1_squared"],one["mu1_squared"])
        structure={"g2":two["g"],"g2_digits":len(str(two["g"])),
                   "mu1_g2_over_mu1_K_squared":
                       [ratio.numerator,ratio.denominator],
                   "log_g2_per_n":log_ratio_ball(n,two["g"],1),
                   "log_mu1_ratio_per_n":log_ratio_ball(
                       n,two["mu1_squared"],one["mu1_squared"],half=True),
                   "balanced_half_log_g2_per_n":log_ratio_ball(n,two["g"],1,half=True),
                   "trivial_guaranteed_gain_lower":0}
        modes.append({"mode":label,"weights":weights,"K_gram_A_B_C":list(Kgram),
                      "deltaK_squared":delta_squared,"tiers":rows,
                      "g2_structure":structure,
                      "first_tested_crossing_g":first["g"] if first else None,
                      "first_tested_crossing_labels":first["labels"] if first else [],
                      "first_tested_crossing_10_564_g":first_new["g"] if first_new else None,
                      "first_tested_crossing_10_564_labels":first_new["labels"] if first_new else []})
    return {"n":n,"input_sha256":digest(path),"smith_audit_sha256":digest(BASE),
            "K_rows":K,"J_rows_B_A":J,"D":D,"s1":s1,"s2":s2,"N":N,
            "N_complete_small_prime_factorization":factors,
            "N_factorization_cofactor":cofactor,
            "N_largest_prime":max(p for p,e in factors),
            "smith_U":U,"smith_V":V,"d_n":d,
            "tier_count_distinct":len(candidates),"modes":modes,
            "seconds":round(time.monotonic()-began,3)}


def serializable(value):
    if isinstance(value,bool):
        return value
    if isinstance(value,int):
        return str(value)
    if isinstance(value,list):
        return [serializable(x) for x in value]
    if isinstance(value,dict):
        return {k:serializable(x) for k,x in value.items()}
    return value


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--n",type=int,nargs="*",default=[12,24,48,96,192])
    parser.add_argument("--timeout-seconds",type=int,default=120)
    parser.add_argument("--force",action="store_true")
    args=parser.parse_args()
    if any(n not in (12,24,48,96,192) for n in args.n):
        parser.error("Only five archived n values are allowed")
    audit=json.loads(BASE.read_text(encoding="utf-8"))
    by_n={int(c["n"]):c for c in audit["cases"]}
    existing={}
    if OUT.exists() and not args.force:
        old=json.loads(OUT.read_text(encoding="utf-8"))
        existing={int(c["n"]):c for c in old["cases"]}
    started=time.monotonic()
    for n in args.n:
        if n in existing:
            continue
        case=one_case(n,by_n[n])
        if case["seconds"]>args.timeout_seconds:
            raise TimeoutError(f"n={n} exceeded per-case time cap")
        existing[n]=serializable(case)
        result={"schema":"zeta9-round7-modulus-scan-v1",
                "scope":"finite exact modulus hierarchy; no zeta numeric evaluation",
                "cases":[existing[k] for k in sorted(existing)],
                "source_sha256":{"modulus_scan":digest(Path(__file__)),
                                 "smith_audit":digest(BASE)},
                "elapsed_seconds":round(time.monotonic()-started,3)}
        OUT.parent.mkdir(parents=True,exist_ok=True)
        OUT.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding="utf-8")
        print(json.dumps({"n":n,"status":"ok","seconds":case["seconds"],
                          "tiers":case["tier_count_distinct"],
                          "crossings":{x["mode"]:x["first_tested_crossing_labels"]
                                       for x in case["modes"]},
                          "crossings_10_564":{x["mode"]:x["first_tested_crossing_10_564_labels"]
                                              for x in case["modes"]}},ensure_ascii=False),flush=True)


if __name__=="__main__":
    main()
