"""Finite exact-rational design checks; no Lean and no universal proof claim."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib, json, sys
sys.stdout.reconfigure(encoding='utf-8')
OUT=Path(__file__).resolve().parent;TASK=OUT.parents[1]
INPUT=TASK/'verification/formalization-coefficient-map-connection-independent-2026-10-04/exact-instance-checks.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def trim(a):
    a=list(map(F,a))
    while a and not a[-1]:a.pop()
    return a
def add(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def scale(a,b):return trim([b*x for x in a])
def mul(a,b):
    if not a or not b:return []
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return trim(c)
def power(a,n):
    c=[F(1)]
    for _ in range(n):c=mul(c,a)
    return c
def comp(a,b):
    c=[]
    for x in reversed(a):c=add(mul(c,b),[x])
    return c
def evaluate(a,x):
    y=F(0)
    for c in reversed(a):y=y*x+c
    return y
def mon(r):return [F(0)]*r+[F(1)]
def numerator(n):
    a=[F(factorial(n)**7)]
    for k in range(1,n+1):a=mul(a,[-k,1])
    for k in range(1,n+1):a=mul(a,[n+k,1])
    return a
def weighted(n,w):return mul(numerator(n),comp(w,[0,n,1]))
def pole(m,x):
    y=F(1)
    for k in range(m+1):y*=x+k
    return y
def quotient9(a,b):
    assert b and b[0]
    c=[]
    for k in range(9):
        value=a[k] if k<len(a) else F(0)
        for i in range(1,k+1):
            if i<len(b):value-=b[i]*c[k-i]
        c.append(value/b[0])
    return c
def local_array(m,a):
    rows=[]
    for j in range(m+1):
        denominator=[F(1)]
        for k in range(m+1):
            if k!=j:denominator=mul(denominator,power([k-j,1],9))
        series=quotient9(comp(a,[-j,1]),denominator)
        rows.append([series[9-s] for s in range(1,10)])
    return rows
def harmonic(s,j):return sum((F(1,k**s) for k in range(1,j+1)),F(0))
def constant(a):return -sum((a[j][s-1]*harmonic(s,j) for j in range(len(a)) for s in range(1,10)),F(0))
def rho(a,s):return sum((r[s-1] for r in a),F(0))
def rational(n,w,t):return evaluate(weighted(n,w),t)/pole(n,t)**9
def qnum(n,q):
    a=[F(factorial(n)**7)]
    for k in range(2,n+2):a=mul(a,[-k,1])
    for k in range(1,n+1):a=mul(a,[n+k,1])
    return mul(a,comp(q,[0,n-1,1]))
def qvalue(n,q,t):return evaluate(qnum(n,q),t)/((t-1)*pole(n,t))**9
def pfsum(a,x):return sum((a[j][s-1]/(x+j)**s for j in range(len(a)) for s in range(1,10)),F(0))

old=json.loads(INPUT.read_text(encoding='utf-8'))
checks=[];instances=[]
def check(name,condition,detail=None):
    assert condition,name
    checks.append(dict(name=name,pass_=True,detail=detail))
    checks[-1]['pass']=checks[-1].pop('pass_')
for instance in old['instances']:
    n=instance['n']; assert n in [1,2,3]
    oldF=[]
    for ell in range(5):
        a=local_array(n,weighted(n,mon(ell)))
        oldF.append([constant(a)]+[rho(a,s) for s in [3,5,7,9]])
    gamma=[];newF=[];details=[]
    for r in range(5):
        row=next(x for x in instance['solutions'] if x['name']=='actual_target_r'+str(r))
        c=list(map(F,row['input15_P5_Q10']));p,q=trim(c[:5]),trim(c[5:])
        b=local_array(n,weighted(n,p));a=local_array(n+2,weighted(n+2,mon(r)))
        nq=qnum(n,q);qc=local_array(n+1,comp(nq,[1,1]))
        check(f'n{n}_r{r}_proper_remainder_actual_numerator_degree',len(nq)-1<=2*n+18 and 2*n+18<9*(n+2))
        check(f'n{n}_r{r}_all_nine_actual_local_shift_relations',all(
            a[j][s-1]==(b[j-1][s-1] if 1<=j<=n+1 else 0)
                +(qc[j][s-1] if j<=n+1 else 0)
                -(qc[j-1][s-1] if 1<=j<=n+2 else 0)
            for j in range(n+3) for s in range(1,10)))
        check(f'n{n}_r{r}_all_nine_rho_totals_transport',all(rho(a,s)==rho(b,s) for s in range(1,10)))
        check(f'n{n}_r{r}_pure_rational_B_correction',constant(a)==constant(b)-rational(n,p,F(1))+qvalue(n,q,F(2)))
        check(f'n{n}_r{r}_two_true_boundary_values_zero',rational(n,p,F(1))==qvalue(n,q,F(2))==0)
        check(f'n{n}_r{r}_actual_Q_partial_fractions_regular_points',all(qvalue(n,q,F(t))==pfsum(qc,F(t-1)) for t in [2,3,n+4]))
        check(f'n{n}_r{r}_real_PS_identity_exact_rational_points',all(
            rational(n+2,mon(r),F(t-1))==rational(n,p,F(t))+qvalue(n,q,F(t))-qvalue(n,q,F(t+1))
            for t in [2,3,n+4]))
        for T in [0,1,2,5]:
            lhs=sum((rational(n+2,mon(r),F(t)) for t in range(1,T+1)),F(0))
            rhs=sum((rational(n,p,F(t)) for t in range(1,T+2)),F(0))+qvalue(n,q,F(2))-qvalue(n,q,F(T+2))
            check(f'n{n}_r{r}_actual_finite_telescope_T{T}',lhs==rhs)
        gamma.append(c[:5]);newF.append([constant(a)]+[rho(a,s) for s in [3,5,7,9]])
        details.append(dict(r=r,old_B=str(constant(b)),new_B=str(constant(a)),Q2=str(qvalue(n,q,F(2))),
            local_coefficients=len(a)*9,all_rho_orders=list(range(1,10))))
    check(f'n{n}_actual_row_orientation_F_new_equals_Gamma_F_old',all(
        newF[r][i]==sum((gamma[r][ell]*oldF[ell][i] for ell in range(5)),F(0)) for r in range(5) for i in range(5)))
    instances.append(dict(n=n,checks_scope='finite exact instances only',rows=details,
        Gamma=[[str(x) for x in row] for row in gamma],oldF=[[str(x) for x in row] for row in oldF],newF=[[str(x) for x in row] for row in newF]))
report=dict(status='FINITE_EXACT_RATIONAL_DESIGN_CHECKS_NOT_UNIVERSAL_LEAN_PROOF',
    source_input=INPUT.relative_to(TASK).as_posix(),source_input_sha256=sha(INPUT),
    checks=checks,instances=instances,Lean_executed=False,
    pure_rational_B_identity='B_new = B_old - weightedR_old(P,1) + Q(2)',
    local_relation='A_j,s = b_(j-1),s + c_j,s - c_(j-1),s, with zero extension',
    limitations='This script checks only n=1,2,3 and all five targets. The generic PF construction, local uniqueness, finite reindexing and universal five-coordinate transport still require actual Lean proofs.')
target=OUT/'exact-design-checks.json';assert not target.exists()
target.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(checks=len(checks),all_pass=True,n=[1,2,3],Lean_executed=False,report_sha256=sha(target))))
