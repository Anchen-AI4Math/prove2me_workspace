"""Exact multi-zeta vectors for odd triple-to-nine pole-order families.

This is finite arithmetic and signed Arb evaluation, not an irrationality proof.
The pole order p is 3, 5, 7, or 9; s=9 is fixed for the elimination target.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/"tmp/zeta7/exact_packages"))
from flint import arb,ctx,fmpq,fmpz  # type: ignore

BASE=ROOT/"missions/zeta9/round2/verification"
POLES=(3,5,7,9)


def harmonic_arrays(limit:int,orders:range) -> dict[int,list[fmpq]]:
    H={v:[fmpq(0)] for v in orders}
    for k in range(1,limit+1):
        for v,row in H.items():
            row.append(row[-1]+fmpq(1,k**v))
    return H


def qpair(x:fmpq) -> list[str]:
    return [str(x.numer()),str(x.denom())]


def interval(x:arb,digits:int=36) -> dict:
    mid,rad,exp=x.mid_rad_10exp(digits)
    return {"mid":str(mid),"rad":str(rad),"exp":int(exp)}


def score_value(orders:list[int],coefficients:list[int],constant:int,
                extra_digits:int=40) -> dict:
    height=max([len(str(abs(constant)))]+[len(str(abs(c))) for c in coefficients])
    bits=max(256,math.ceil(3.5*(height+extra_digits)))
    for _ in range(8):
        with ctx.workprec(bits):
            value=arb(fmpz(constant))
            for order,c in zip(orders,coefficients):
                value+=arb(fmpz(c))*arb(order).zeta()
            sign=1 if value.lower()>0 else (-1 if value.upper()<0 else 0)
            if sign and value.rel_accuracy_bits()>=80:
                logabs=(value if sign>0 else -value).log()
                return {"sign":sign,"value_interval":interval(value),
                        "abs_log_interval":interval(logabs),
                        "below_one":bool(logabs.upper()<0),
                        "above_one":bool(logabs.lower()>0),
                        "abs_log_value":float(logabs),
                        "arb_bits":bits,"relative_accuracy_bits":value.rel_accuracy_bits()}
        bits*=2
    raise ArithmeticError("Arb could not certify signed nonzero value")


def validate(p:int,n:int,m:int) -> tuple[int,int,int]:
    if p not in POLES or n<2 or n%2 or m<0:
        raise ValueError("Require p in {3,5,7,9}, positive even n, and m>=0")
    d=9-p
    b=d+1
    r=p*(n+1)-2*b*m-2
    if r<0:
        raise ValueError("Require 2bm<=p(n+1)-2")
    return d,b,r


def exact_vector(p:int,n:int,m:int,check_points:bool=False) -> dict:
    d,b,r=validate(p,n,m)
    H=harmonic_arrays(n+m,range(1,10))
    C=[]
    pole_coeffs={j:[] for j in range(1,p+1)}
    for k in range(n+1):
        top=((-1)**(m+k)*math.comb(n,k)**p
             *math.comb(k+m,m)**b*math.comb(n-k+m,m)**b)
        C.append(top)
        sums=[fmpq(0)]*(p)
        for v in range(1,p):
            sums[v]=(b*((-1)**v*(H[v][k+m]-H[v][k])
                        +(H[v][n-k+m]-H[v][n-k]))
                     -p*((-1)**v*H[v][k]+H[v][n-k]))
        series=[fmpq(1)]
        for t in range(1,p):
            coefficient=sum(((-1)**(v+1)*sums[v]*series[t-v]
                             for v in range(1,t+1)),fmpq(0))/t
            series.append(coefficient)
        for t,value in enumerate(series):
            pole_coeffs[p-t].append(fmpq(top)*value)

    for j,cs in pole_coeffs.items():
        if j==1 or j%2==0:
            if sum(cs,fmpq(0))!=0:
                raise AssertionError(f"Unwanted zeta order {d+j} did not cancel")
        for k in range(n+1):
            if cs[n-k]!=(-1)**(j+1)*cs[k]:
                raise AssertionError("Partial fractions violate reflection")
    orders=list(range(d+3,10,2))
    assert len(orders)==(p-1)//2
    coeffs=[fmpq(math.comb(order-1,d))*sum(pole_coeffs[order-d],fmpq(0))
            for order in orders]
    constant=-sum((fmpq(math.comb(d+j-1,d))*pole_coeffs[j][k]*H[d+j][k]
                   for j in range(1,p+1) for k in range(n+1)),fmpq(0))
    raw=[constant]+coeffs
    G=math.gcd(*C)
    D=math.lcm(*range(1,n+m+1))
    certificate=fmpq(D**9,G)
    pres=[certificate*x for x in raw]
    if any(x.denom()!=1 for x in pres):
        raise AssertionError("d_(n+m)^9/G did not integerize full vector")
    ints=[int(x.numer()) for x in pres]
    content=math.gcd(*ints)
    if content<1:
        raise AssertionError("Zero or invalid full coefficient vector")
    primitive=[x//content for x in ints]
    assert math.gcd(*primitive)==1
    primitive_multiplier=certificate/content

    if check_points:
        pref=fmpq(math.factorial(n)**p,math.factorial(m)**(2*b))
        for t in (1,m+1,n+2,2*n+3):
            numerator=(math.prod(t-a for a in range(1,m+1))
                       *math.prod(t+n+a for a in range(1,m+1)))**b
            direct=pref*numerator/math.prod(t+a for a in range(n+1))**p
            pf=sum((pole_coeffs[j][k]/(t+k)**j
                    for j in range(1,p+1) for k in range(n+1)),fmpq(0))
            if direct!=pf:
                raise AssertionError("Partial fraction value differs at direct check point")

    return {"p":p,"n":n,"m":m,"d":d,"b":b,"r":r,
            "zeta_orders":orders,"raw_vector":raw,
            "certificate_multiplier":certificate,
            "preprimitive_vector":ints,"content":content,
            "primitive_vector":primitive,
            "primitive_multiplier":primitive_multiplier,
            "C":C,"G":G,"D":D,"pole_coeffs":pole_coeffs}


def det_int(matrix:list[list[int]]) -> int:
    size=len(matrix)
    if size==0:
        return 1
    if any(len(row)!=size for row in matrix):
        raise ValueError("Determinant requires a square matrix")
    if size==1:
        return matrix[0][0]
    return sum(((-1)**j*matrix[0][j]
                *det_int([row[:j]+row[j+1:] for row in matrix[1:]])
                for j in range(size)))


def integer_kernel(matrix:list[list[int]],columns:int) -> tuple[int,list[list[int]]]:
    """Exact rank and a primitive integer basis for a rational nullspace."""
    rows=[[Fraction(v) for v in row] for row in matrix]
    pivots=[]
    lead=0
    for col in range(columns):
        pivot=next((i for i in range(lead,len(rows)) if rows[i][col]),None)
        if pivot is None:
            continue
        rows[lead],rows[pivot]=rows[pivot],rows[lead]
        divisor=rows[lead][col]
        rows[lead]=[v/divisor for v in rows[lead]]
        for i in range(len(rows)):
            if i!=lead and rows[i][col]:
                factor=rows[i][col]
                rows[i]=[a-factor*b for a,b in zip(rows[i],rows[lead])]
        pivots.append(col)
        lead+=1
        if lead==len(rows):
            break
    basis=[]
    for free in range(columns):
        if free in pivots:
            continue
        vector=[Fraction(0)]*columns
        vector[free]=Fraction(1)
        for i,pivot in enumerate(pivots):
            vector[pivot]=-rows[i][free]
        scale=math.lcm(*(v.denominator for v in vector))
        integral=[int(v*scale) for v in vector]
        common=math.gcd(*integral)
        integral=[v//common for v in integral]
        basis.append(integral)
    assert len(basis)==columns-len(pivots)
    assert all(sum(row[i]*v[i] for i in range(columns))==0
               for v in basis for row in matrix)
    return len(pivots),basis


def eliminate(forms:list[dict]) -> dict:
    if not forms:
        raise ValueError("Need at least one form")
    p=forms[0]["p"]
    q=(p-1)//2
    n=forms[0]["n"]
    if (len(forms)!=q or any(f["p"]!=p or f["n"]!=n for f in forms)
            or [f["m"] for f in forms]!=list(range(forms[0]["m"],forms[0]["m"]+q))):
        raise ValueError("Need q adjacent m forms with common p,n")
    rows=[f["primitive_vector"] for f in forms]
    lower=[[row[j] for row in rows] for j in range(1,q)]
    rank,kernel=integer_kernel(lower,q)
    raw_weights=[(-1)**i*det_int([line[:i]+line[i+1:] for line in lower])
                 for i in range(q)]
    divisor=math.gcd(*raw_weights)
    if divisor==0:
        usable=next((v for v in kernel
                     if sum(v[i]*rows[i][-1] for i in range(q))!=0),None)
        return {"status":"rank_deficient","lower_rank":rank,
                "nullspace_basis":kernel,"usable_target_kernel":usable,
                "raw_cofactor_weights":raw_weights}
    if rank!=q-1:
        raise AssertionError("Nonzero cofactor with deficient rank")
    weights=[v//divisor for v in raw_weights]
    combined=[sum(weights[i]*rows[i][j] for i in range(q))
              for j in range(q+1)]
    if any(combined[j]!=0 for j in range(1,q)):
        raise AssertionError("Cofactors failed to eliminate lower zeta values")
    target=combined[-1]
    if target==0:
        return {"status":"constant_only" if combined[0] else "zero_combination",
                "lower_rank":rank,"nullspace_basis":kernel,
                "raw_cofactor_weights":raw_weights,
                "weights":weights,"combined_vector":combined}
    constant=combined[0]
    content=math.gcd(constant,target)
    if content==0:
        return {"status":"zero_combination","lower_rank":rank,
                "nullspace_basis":kernel,"weights":weights}
    primitive=[target//content,constant//content]
    if math.gcd(*primitive)!=1:
        raise AssertionError("Combination is not primitive")
    return {"status":"ok","lower_rank":rank,
            "raw_cofactor_weights":raw_weights,
            "weights":weights,"weight_content":divisor,
            "combined_vector":combined,"combination_content":content,
            "primitive_coefficients_A9_B":primitive}


def digest(values:list[int]) -> str:
    return hashlib.sha256(",".join(str(v) for v in values).encode()).hexdigest()


def json_integer_tree(value):
    if value is None:
        return None
    if isinstance(value,list):
        return [json_integer_tree(v) for v in value]
    return str(value) if isinstance(value,int) else value


def write_artifact(path:Path,record:dict) -> str:
    path.parent.mkdir(parents=True,exist_ok=True)
    temp=path.with_suffix(".tmp")
    with gzip.open(temp,"wt",encoding="utf-8") as stream:
        json.dump(record,stream,ensure_ascii=False,separators=(",",":"))
    temp.replace(path)
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atom_main(args) -> None:
    start=time.monotonic()
    form=exact_vector(args.p,args.n,args.m,check_points=(args.n<=24))
    vector=form["primitive_vector"]
    eval_result=score_value(form["zeta_orders"],vector[1:],vector[0])
    eval_result["abs_log_per_n"]=eval_result["abs_log_value"]/args.n
    case=f"p{args.p}-n{args.n}-m{args.m}"
    record={"case_id":case,"construction":"multi_zeta_general_poles",
            "p":args.p,"n":args.n,"m":args.m,"d":form["d"],"b":form["b"],"r":form["r"],
            "zeta_orders":form["zeta_orders"],
            "vector_order":"[constant, zeta(order1), ..., zeta(9)]",
            "raw_rational_vector":[qpair(x) for x in form["raw_vector"]],
            "certificate_multiplier":qpair(form["certificate_multiplier"]),
            "preprimitive_integer_vector":[str(x) for x in form["preprimitive_vector"]],
            "preprimitive_content":str(form["content"]),
            "primitive_integer_vector":[str(x) for x in vector],
            "primitive_multiplier":qpair(form["primitive_multiplier"]),
            "D_lcm_n_plus_m":str(form["D"]),"G_residue_gcd":str(form["G"]),
            "primitive_vector_sha256":digest(vector),
            "zeta_cancelled":[form["d"]+1]+list(range(form["d"]+2,10,2)),
            "signed_evaluation":eval_result,
            "height_digits":max(len(str(abs(x))) for x in vector),
            "seconds":round(time.monotonic()-start,3),
            "runtime":{"python":sys.version.split()[0],
                       "general_poles_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       "runner_sha256":hashlib.sha256(Path(__file__).with_name("attack_elimination.py").read_bytes()).hexdigest()}}
    path=BASE/"elimination-atoms"/f"{case}.json.gz"
    artifact_hash=write_artifact(path,record)
    brief={k:record[k] for k in ("case_id","p","n","m","r","zeta_orders",
                                 "primitive_vector_sha256","height_digits","seconds")}
    brief.update({"status":"ok","sign":eval_result["sign"],
                  "below_one":eval_result["below_one"],
                  "abs_log_per_n":eval_result["abs_log_per_n"],
                  "artifact_path":str(path.relative_to(ROOT)).replace("\\","/"),
                  "artifact_sha256":artifact_hash,
                  "runtime":record["runtime"]})
    print(json.dumps(brief,separators=(",",":")),flush=True)


def combine_main(args) -> None:
    start=time.monotonic()
    q=(args.p-1)//2
    forms=[]
    paths=[]
    for m in range(args.start,args.start+q):
        case=f"p{args.p}-n{args.n}-m{m}"
        path=BASE/"elimination-atoms"/f"{case}.json.gz"
        with gzip.open(path,"rt",encoding="utf-8") as stream:
            row=json.load(stream)
        forms.append({"p":args.p,"n":args.n,"m":m,
                      "primitive_vector":[int(x) for x in row["primitive_integer_vector"]]})
        paths.append({"path":str(path.relative_to(ROOT)).replace("\\","/"),
                      "sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
                      "primitive_vector_sha256":row["primitive_vector_sha256"]})
    result=eliminate(forms)
    case=f"p{args.p}-n{args.n}-m{args.start}..{args.start+q-1}"
    record={"case_id":case,"construction":"exact_cofactor_elimination",
            "p":args.p,"n":args.n,"m_start":args.start,"m_values":list(range(args.start,args.start+q)),
            "q_forms":q,"profile_slot":args.slot,
            "zeta_orders":list(range(12-args.p,10,2)),
            "input_atom_artifacts":paths,
            "input_primitive_vectors":[[str(v) for v in f["primitive_vector"]] for f in forms],
            "status":result["status"],"seconds":None}
    for name,value in result.items():
        if name!="status":
            record[name]=json_integer_tree(value)
    if result["status"]=="ok":
        a,b=result["primitive_coefficients_A9_B"]
        evaluation=score_value([9],[a],b)
        evaluation["abs_log_per_n"]=evaluation["abs_log_value"]/args.n
        record["signed_evaluation"]=evaluation
        record["coefficients_sha256"]=digest([a,b])
        record["height_digits"]=max(len(str(abs(a))),len(str(abs(b))))
    record["seconds"]=round(time.monotonic()-start,3)
    record["runtime"]={"python":sys.version.split()[0],
                       "general_poles_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       "runner_sha256":hashlib.sha256(Path(__file__).with_name("attack_elimination.py").read_bytes()).hexdigest()}
    path=BASE/"elimination-combinations"/f"{case}.json.gz"
    artifact_hash=write_artifact(path,record)
    brief={"case_id":case,"p":args.p,"n":args.n,"m_start":args.start,
           "m_values":record["m_values"],"profile_slot":args.slot,
           "status":record["status"],
           "seconds":record["seconds"],
           "artifact_path":str(path.relative_to(ROOT)).replace("\\","/"),
           "artifact_sha256":artifact_hash,"runtime":record["runtime"]}
    if result["status"]=="ok":
        brief.update({"sign":evaluation["sign"],"below_one":evaluation["below_one"],
                      "abs_log_per_n":evaluation["abs_log_per_n"],
                      "height_digits":record["height_digits"],
                      "coefficients_sha256":record["coefficients_sha256"]})
    print(json.dumps(brief,separators=(",",":")),flush=True)


def self_test() -> None:
    for p,n,m in ((3,14,3),(5,12,1),(7,12,1),(9,12,1)):
        start=time.monotonic()
        form=exact_vector(p,n,m,check_points=True)
        assert form["r"]>=0 and math.gcd(*form["primitive_vector"])==1
        print(json.dumps({"p":p,"n":n,"m":m,"r":form["r"],
                          "orders":form["zeta_orders"],
                          "height_digits":max(len(str(abs(x))) for x in form["primitive_vector"]),
                          "seconds":round(time.monotonic()-start,3)}),flush=True)
    # The p=3 formula is exactly the first-round zeta(9) construction.
    sys.path.insert(0,str(ROOT/"missions/zeta9/scripts"))
    from odd_linear_form import exact_form
    old=exact_form(9,14,3)
    new=exact_vector(3,14,3)
    assert new["raw_vector"]==[old["B_constant"],old["A_zeta"]]
    assert new["primitive_vector"]==[old["primitive"][1],old["primitive"][0]]
    sample=[exact_vector(5,12,m) for m in (0,1)]
    elim=eliminate(sample)
    assert elim["status"]=="ok" and elim["combined_vector"][1]==0
    a,b=elim["primitive_coefficients_A9_B"]
    signed=score_value([9],[a],b)
    opposite=score_value([9],[-a],-b)
    assert signed["sign"]==-opposite["sign"]
    print(json.dumps({"p3_agrees_with_round1":True,
                      "p5_lower_zeta_cancelled":True,
                      "negative_arb_handled":True}),flush=True)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--self-test",action="store_true")
    group.add_argument("--atom",action="store_true")
    group.add_argument("--combine",action="store_true")
    parser.add_argument("--p",type=int)
    parser.add_argument("--n",type=int)
    parser.add_argument("--m",type=int)
    parser.add_argument("--start",type=int)
    parser.add_argument("--slot",type=int)
    args=parser.parse_args()
    if args.self_test:
        self_test()
    elif args.atom:
        if args.p is None or args.n is None or args.m is None:
            parser.error("--atom requires --p --n --m")
        atom_main(args)
    else:
        if args.p is None or args.n is None or args.start is None:
            parser.error("--combine requires --p --n --start")
        combine_main(args)


if __name__=="__main__":
    main()
