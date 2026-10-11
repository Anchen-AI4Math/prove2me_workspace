"""Exact odd-zeta linear form from a triple-pole rational function.

For odd s >= 5 and even n, put b=s-2 and
 R(t)=(n!)^3/(m!)^(2b) * [(t-m)_m(t+n+1)_m]^b/(t)_(n+1)^3.
The sum of R^(s-3)(t)/(s-3)! over positive integers is A*zeta(s)+B.
All algebra below is exact; Arb encloses the signed primitive integer form.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "tmp/zeta7/exact_packages"))

from flint import arb, ctx, fmpq, fmpz  # type: ignore


def harmonic_arrays(limit: int, orders: set[int]) -> dict[int, list[fmpq]]:
    ans = {q: [fmpq(0)] for q in orders}
    for j in range(1, limit + 1):
        for q, values in ans.items():
            values.append(values[-1] + fmpq(1, j**q))
    return ans


def rational_pair(value: fmpq) -> list[str]:
    return [str(value.numer()), str(value.denom())]


def interval(value: arb, digits: int = 36) -> dict[str, str | int]:
    mid, rad, exp = value.mid_rad_10exp(digits)
    return {"mid": str(mid), "rad": str(rad), "exp": int(exp)}


def exact_form(s: int, n: int, m: int, check_points: bool = False) -> dict:
    if s < 5 or s % 2 != 1 or n < 2 or n % 2 or m < 0:
        raise ValueError("Require odd s>=5, positive even n, and m>=0")
    power = s - 2
    derivative_order = s - 3
    r = 3*n + 1 - 2*power*m
    if r < 0:
        raise ValueError("Require 2(s-2)m <= 3n+1 for O(t^-2) decay")

    H = harmonic_arrays(n + m, {1, 2, s-2, s-1, s})
    c1: list[fmpq] = []
    c2: list[fmpq] = []
    C: list[int] = []
    for k in range(n + 1):
        c = ((-1)**(m+k) * math.comb(n,k)**3
             * math.comb(k+m,m)**power
             * math.comb(n-k+m,m)**power)
        C.append(c)
        u = (power*(-(H[1][k+m]-H[1][k])
                    +(H[1][n-k+m]-H[1][n-k]))
             -3*(H[1][n-k]-H[1][k]))
        v = (-power*((H[2][k+m]-H[2][k])
                     +(H[2][n-k+m]-H[2][n-k]))
             +3*(H[2][k]+H[2][n-k]))
        c2.append(fmpq(c)*u)
        c1.append(fmpq(c)*(u*u+v)/2)

    if sum(c1, fmpq(0)) != 0:
        raise AssertionError("The zeta(s-2) coefficient did not cancel")
    if sum(c2, fmpq(0)) != 0:
        raise AssertionError("The zeta(s-1) coefficient did not cancel")
    for k in range(n+1):
        if (C[k] != C[n-k] or c1[k] != c1[n-k]
                or c2[k] != -c2[n-k]):
            raise AssertionError("Reflection identity failed")

    top = math.comb(s-1, 2)
    A = fmpq(top*sum(C))
    B = -sum((c1[k]*H[s-2][k] + power*c2[k]*H[s-1][k]
              + top*fmpq(C[k])*H[s][k] for k in range(n+1)), fmpq(0))
    if A == 0:
        raise AssertionError("Zeta coefficient is zero")

    G = math.gcd(*C)
    d = math.lcm(*range(1, n+m+1))
    cert_multiplier = fmpq(2*d**s, G)
    za, zb = cert_multiplier*A, cert_multiplier*B
    if za.denom() != 1 or zb.denom() != 1:
        raise AssertionError("The 2 d_(n+m)^s/G integerization failed")
    pre_a, pre_b = int(za.numer()), int(zb.numer())
    content = math.gcd(pre_a, pre_b)
    if content == 0:
        raise AssertionError("The linear form vanished identically")
    primitive_a, primitive_b = pre_a//content, pre_b//content
    primitive_multiplier = cert_multiplier/content
    if (primitive_multiplier*A != primitive_a
            or primitive_multiplier*B != primitive_b
            or math.gcd(primitive_a, primitive_b) != 1):
        raise AssertionError("Primitive scaling identity failed")

    if check_points:
        prefactor = fmpq(math.factorial(n)**3, math.factorial(m)**(2*power))
        for t in (1, m+1, n+2, 2*n+3):
            numerator = math.prod(t-j for j in range(1,m+1))
            numerator *= math.prod(t+n+j for j in range(1,m+1))
            direct = prefactor*numerator**power / math.prod(t+j for j in range(n+1))**3
            residues = sum((c1[k]/(t+k) + c2[k]/(t+k)**2
                            + fmpq(C[k],(t+k)**3) for k in range(n+1)), fmpq(0))
            if direct != residues:
                raise AssertionError("Partial fractions failed at a direct test point")

    return {"s":s,"n":n,"m":m,"r":r,"power":power,
            "derivative_order":derivative_order,"pole_order":3,
            "A_zeta":A,"B_constant":B,"d_lcm":d,"G":G,
            "certificate_multiplier":cert_multiplier,
            "preprimitive":(pre_a,pre_b),"content":content,
            "primitive":(primitive_a,primitive_b),
            "primitive_multiplier":primitive_multiplier,
            "C":C,"c1":c1,"c2":c2}


def signed_evaluation(s: int, a: int, b: int, extra_digits: int = 40) -> dict:
    height = max(len(str(abs(a))),len(str(abs(b))))
    bits = max(256, math.ceil(3.5*(height+extra_digits)))
    for _ in range(8):
        with ctx.workprec(bits):
            value = arb(fmpz(a))*arb(s).zeta()+arb(fmpz(b))
            sign = 1 if value.lower()>0 else (-1 if value.upper()<0 else 0)
            if sign and value.rel_accuracy_bits() >= 80:
                absolute = value if sign > 0 else -value
                logabs = absolute.log()
                return {"sign":sign,"value_interval":interval(value),
                        "abs_log_interval":interval(logabs),
                        "abs_log_value":float(logabs),
                        "below_one":bool(logabs.upper()<0),
                        "above_one":bool(logabs.lower()>0),
                        "arb_bits":bits,
                        "relative_accuracy_bits":value.rel_accuracy_bits()}
        bits *= 2
    raise ArithmeticError("Arb did not exclude zero with >=80 relative accuracy")


def full_record(form: dict, evaluation: dict) -> dict:
    a,b = form["primitive"]
    coefficient_text = f"{a},{b}"
    return {"construction":"odd_linear_triple_pole",
            "s":form["s"],"n":form["n"],"m":form["m"],"r":form["r"],
            "power":form["power"],"derivative_order":form["derivative_order"],
            "pole_order":3,"linear_form_order":"A*zeta(s)+B",
            "A_zeta_rational":rational_pair(form["A_zeta"]),
            "B_constant_rational":rational_pair(form["B_constant"]),
            "d_lcm_n_plus_m":str(form["d_lcm"]),"G_residue_gcd":str(form["G"]),
            "certificate_multiplier":rational_pair(form["certificate_multiplier"]),
            "preprimitive_integer_coefficients":[str(v) for v in form["preprimitive"]],
            "preprimitive_content":str(form["content"]),
            "primitive_integer_coefficients":[str(a),str(b)],
            "primitive_multiplier":rational_pair(form["primitive_multiplier"]),
            "coefficients_sha256":hashlib.sha256(coefficient_text.encode()).hexdigest(),
            "primitive_gcd_one":True,"zeta_s_minus_2_cancelled":True,
            "zeta_s_minus_1_cancelled":True,
            "signed_evaluation":evaluation,
            "abs_log_per_n":evaluation["abs_log_value"]/form["n"],
            "height_digits":max(len(str(abs(a))),len(str(abs(b))))}


def self_test() -> None:
    for s,n,m in ((5,4,1),(9,6,1),(9,10,2),(9,14,3),(9,8,0)):
        form=exact_form(s,n,m,check_points=True)
        a,b=form["primitive"]
        result=signed_evaluation(s,a,b)
        opposite=signed_evaluation(s,-a,-b)
        assert opposite["sign"] == -result["sign"]
        assert result["abs_log_interval"] == opposite["abs_log_interval"]
        print(json.dumps({"s":s,"n":n,"m":m,"r":form["r"],
                          "G_digits":len(str(form["G"])),
                          "height_digits":max(len(str(abs(a))),len(str(abs(b)))),
                          "sign":result["sign"],"below_one":result["below_one"]}),flush=True)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test",action="store_true")
    parser.add_argument("--compute",action="store_true")
    parser.add_argument("--s",type=int,default=9)
    parser.add_argument("--n",type=int)
    parser.add_argument("--m",type=int)
    parser.add_argument("--case-type",default="grid")
    args=parser.parse_args()
    if args.self_test:
        self_test()
        return
    if not args.compute or args.n is None or args.m is None:
        parser.error("Use --compute --n N --m M or --self-test")
    start=time.monotonic()
    form=exact_form(args.s,args.n,args.m,check_points=(args.n<=28))
    a,b=form["primitive"]
    evaluation=signed_evaluation(args.s,a,b)
    record=full_record(form,evaluation)
    case_id=f"s{args.s}-n{args.n}-m{args.m}"
    record["case_id"]=case_id
    record["case_type"]=args.case_type
    record["seconds"]=round(time.monotonic()-start,3)
    record["runtime"]={"python":sys.version.split()[0],
                       "exact_script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       "runner_script_sha256":hashlib.sha256(Path(__file__).with_name("attack_linear.py").read_bytes()).hexdigest()}
    directory=ROOT/"missions/zeta9/verification/linear-coeff"
    directory.mkdir(parents=True,exist_ok=True)
    path=directory/f"{case_id}.json.gz"
    temp=directory/f"{case_id}.tmp"
    with gzip.open(temp,"wt",encoding="utf-8") as stream:
        json.dump(record,stream,ensure_ascii=False,separators=(",",":"))
    temp.replace(path)
    brief={k:record[k] for k in ("case_id","case_type","s","n","m","r",
                                 "coefficients_sha256","height_digits","abs_log_per_n","seconds")}
    brief.update({"status":"ok","sign":evaluation["sign"],
                  "below_one":evaluation["below_one"],
                  "above_one":evaluation["above_one"],
                  "value_interval":evaluation["value_interval"],
                  "abs_log_interval":evaluation["abs_log_interval"],
                  "artifact_path":str(path.relative_to(ROOT)).replace("\\","/"),
                  "artifact_sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
                  "runtime":record["runtime"]})
    print(json.dumps(brief,ensure_ascii=False,separators=(",",":")),flush=True)


if __name__=="__main__":
    main()
