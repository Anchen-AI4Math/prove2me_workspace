"""Independent exact-source Jet compile and rational-series arithmetic checks."""
from pathlib import Path
from fractions import Fraction
from math import factorial, prod
import hashlib
import json
import os
import re
import subprocess

OUT = Path(__file__).resolve().parent
PROJECT = OUT / "project"
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
PINS = {"CoefficientMap.lean": "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03",
        "CoefficientMapJet.lean": "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a"}
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"
PROJECT.mkdir(exist_ok=True)
for name,expected in PINS.items():
    data = (TASK / "formalization" / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == expected
    target = PROJECT / "missions/zeta9/formalization" / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
(PROJECT / "lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
assert next(row for row in lock["packages"] if row["name"] == "mathlib")["rev"] == PIN
lock["name"] = "zeta9CoefficientMapJetIndependentReview"
(PROJECT / "lake-manifest.json").write_text(json.dumps(lock, indent=2) + "\n")
(PROJECT / "lakefile.lean").write_text('''import Lake
open Lake DSL
package zeta9CoefficientMapJetIndependentReview
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib Native where
  roots := #[]
  globs := #[.submodules `missions.zeta9.formalization]
''')
(PROJECT / ".lake").mkdir(exist_ok=True)
link = PROJECT / ".lake/packages"
target = ROOT / ".lake/packages"
if not link.exists():
    subprocess.run(["cmd", "/c", "mklink", "/J", str(link), str(target)], capture_output=True, check=True)
assert link.resolve() == target.resolve()
environment = os.environ.copy()
environment.pop("LEAN_PATH", None)
steps, chunks = [], []
commands = [["lake", "--no-cache", "build", "missions.zeta9.formalization.CoefficientMap"],
            ["lake", "--no-cache", "build", "missions.zeta9.formalization.CoefficientMapJet"],
            ["lake", "env", "lean", "JetReviewAudit.lean"]]
for command in commands:
    result = subprocess.run(command, cwd=PROJECT, env=environment, capture_output=True)
    chunks.append(("\nCOMMAND: " + " ".join(command) + "\n").encode())
    chunks.append(result.stdout + result.stderr)
    steps.append({"command": command, "exit_code": result.returncode})
    print(json.dumps(steps[-1]), flush=True)
    if result.returncode:
        break
log = b"".join(chunks)
(OUT / "independent-compile.log").write_bytes(log)
reports = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log.decode("utf-8-sig")):
    reports.setdefault(name, []).append(sorted(x.strip() for x in axioms.split(",") if x.strip()))
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = {name:values for name,values in reports.items() if any(set(xs) - allowed for xs in values)}
jet_required = ["actual_local_rational_expression", "actual_weighted_local_rational_expression",
    "shiftedClearedDenominator_constant_ne_zero", "clearedSeries_denominator_identity", "clearedSeries_unique",
    "weightedClearedSeries_denominator_identity", "localCoefficient_nine", "weightedLocalCoefficient_nine",
    "coefficient_convolution_explicit", "integer_coefficient_convolution"]
review_required = ["exists_unique_actual_series", "weighted_series_is_actual_quotient", "exists_unique_weighted_actual_series",
    "actual_weighted_regular_bridge", "all_orders_actual_convolution", "all_orders_integer_W_convolution",
    "integer_multiplier_coefficients", "zero_boundary_series", "zero_boundary_lower_coefficients", "zero_boundary_top_coefficient"]
required = ["ZetaNine.CoefficientMapJet."+x for x in jet_required] + ["ZetaNine.CoefficientMapJetIndependentReview."+x for x in review_required]
missing = [name for name in required if name not in reports]

def add(a,b):
    return [(a[k] if k<len(a) else 0)+(b[k] if k<len(b) else 0) for k in range(max(len(a),len(b)))]
def mul(a,b):
    c=[Fraction(0) for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j]+=x*y
    return c
def power(a,k):
    out=[Fraction(1)]
    for _ in range(k):
        out=mul(out,a)
    return out
def eval_poly(a,t):
    return sum(x*t**i for i,x in enumerate(a))
def compose(a,u):
    out=[Fraction(0)]
    for i,x in enumerate(a):
        out=add(out,[x*y for y in power(u,i)])
    return out
def coeff(a,k):
    return a[k] if k<len(a) else Fraction(0)
def quotient_jet(a,b,m=8):
    assert b[0]!=0
    out=[]
    for r in range(m+1):
        out.append((coeff(a,r)-sum(coeff(b,k)*out[r-k] for k in range(1,r+1)))/b[0])
    return out

parameters=weighted_orders=integer_multipliers=regular_bridges=0
for n in range(9):
    for j in range(n+1):
        numerator=[Fraction(factorial(n)**7)]
        for i in range(n):
            numerator=mul(numerator,[Fraction(-j-i-1),Fraction(1)])
            numerator=mul(numerator,[Fraction(n-j+i+1),Fraction(1)])
        denominator=[Fraction(1)]
        for k in range(n+1):
            if k!=j:
                denominator=mul(denominator,[Fraction(k-j),Fraction(1)])
        denominator9=power(denominator,9)
        jet=quotient_jet(numerator,denominator9)
        assert denominator[0]!=0
        parameters+=1
        u=[Fraction(-j*(n-j)),Fraction(n-2*j),Fraction(1)]
        for W in [[Fraction(1)],[Fraction(0),Fraction(1)],[Fraction(1),Fraction(1)],
                  [Fraction(3),Fraction(-2),Fraction(5)],[Fraction(2,3),Fraction(-7,5),Fraction(1)]]:
            multiplier=compose(W,u)
            weighted_jet=quotient_jet(mul(numerator,multiplier),denominator9)
            if all(x.denominator==1 for x in W):
                assert all(x.denominator==1 for x in multiplier)
                integer_multipliers+=len(multiplier)
            for s in range(1,10):
                convolution=sum(jet[9-l]*coeff(multiplier,l-s) for l in range(s,10))
                assert weighted_jet[9-s]==convolution
                weighted_orders+=1
            for t in [Fraction(1,2),Fraction(n+1),Fraction(-n-1)]:
                z=t+j
                full_pole=prod(t+k for k in range(n+1))
                actual_num=factorial(n)**7*prod(t-i-1 for i in range(n))*prod(t+n+i+1 for i in range(n))
                actual_weighted=actual_num/full_pole**9*eval_poly(W,t*(t+n))
                shifted_weighted=eval_poly(mul(numerator,multiplier),z)/eval_poly(denominator,z)**9
                assert full_pole!=0 and eval_poly(denominator,z)!=0
                assert actual_weighted*z**9==shifted_weighted
                regular_bridges+=1
        if n==0:
            assert jet==[Fraction(1)]+[Fraction(0)]*8
arithmetic={"status":"PASS","parameter_range":"0 <= n <= 8; 0 <= j <= n; 1 <= s <= 9",
    "local_parameter_pairs":parameters,"all_order_weighted_coefficients":weighted_orders,
    "integer_multiplier_coefficients":integer_multipliers,"regular_weighted_bridges":regular_bridges,
    "method":"Independent exact rational polynomial products and formal quotient recurrence; no float or proof-source coefficient arrays",
    "finite_checks_are_not_the_universal_proof":True}
(OUT / "exact-arithmetic.json").write_text(json.dumps(arithmetic,indent=2)+"\n")
compiler=subprocess.run(["lean","--version"],cwd=PROJECT,capture_output=True,text=True,check=True).stdout.strip()
passed=len(steps)==3 and all(x["exit_code"]==0 for x in steps) and not missing and not bad and "version 4.33.1," in compiler
receipt={"status":"PASS" if passed else "FAIL","source_sha256":PINS,"compiler":compiler,"mathlib_revision":PIN,
    "steps":steps,"log_sha256":hashlib.sha256(log).hexdigest(),"required_axiom_reports":{x:reports.get(x,[]) for x in required},
    "missing_reports":missing,"unexpected_axioms":bad,"finite_arithmetic":arithmetic,
    "original_sources_unchanged":all(hashlib.sha256((TASK/'formalization'/name).read_bytes()).hexdigest()==pin for name,pin in PINS.items()),
    "dependency_reuse":"Exact pinned Mathlib packages only; both actual task sources were copied byte-for-byte and recompiled in this independent project",
    "PNT_or_external_task_binary_cache_reused":False,"source_root_scope_frozen_package_edits":[],"network_API_credential_operations":False}
(OUT/"independent-compile-receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps({"status":receipt['status'],"missing":missing,"unexpected_axioms":bad,"arithmetic":arithmetic}))
raise SystemExit(0 if passed else 1)
