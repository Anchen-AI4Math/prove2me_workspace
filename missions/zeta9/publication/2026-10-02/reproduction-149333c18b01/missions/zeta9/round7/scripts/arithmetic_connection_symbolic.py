"""Fixed-size polynomial connection determinants; no parameter search.

Bareiss exact division over Z[n] uses python-flint. Each determinant task has
a 120-second deadline, checked before each elimination stage.
"""
from __future__ import annotations
import hashlib
import json
import math
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'tmp/zeta7/exact_packages'))
from flint import fmpz_poly, fmpq_poly, fmpq_mat
sys.set_int_max_str_digits(0)
P=fmpz_poly
n=P([0,1])
ZERO=P([0])
ONE=P([1])

def add(a,b):
    return [(a[i] if i<len(a) else ZERO)+(b[i] if i<len(b) else ZERO) for i in range(max(len(a),len(b)))]

def neg(a):return [-x for x in a]

def mul(a,b):
    c=[P([0]) for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def power(a,k):
    b=[ONE]
    for _ in range(k):b=mul(b,a)
    return b

def invariant(a):
    a=list(a)
    while a and not a[-1]:a.pop()
    ans=[P([0]) for _ in range((len(a)+1)//2)]
    while a:
        d=len(a)-1
        assert d%2==0
        r=d//2;c=a[d];ans[r]=c
        for j in range(r+1):a[r+j]-=c*math.comb(r,j)*n**(r-j)
        while a and not a[-1]:a.pop()
    return ans

def bareiss(M):
    started=time.monotonic();M=[list(row) for row in M];m=len(M)
    sign=1;last=ONE
    for k in range(m-1):
        if time.monotonic()-started>120:raise TimeoutError('120-second determinant limit')
        if not M[k][k]:
            r=next(i for i in range(k+1,m) if M[i][k])
            M[k],M[r]=M[r],M[k];sign=-sign
        pivot=M[k][k]
        for i in range(k+1,m):
            for j in range(k+1,m):
                num=pivot*M[i][j]-M[i][k]*M[k][j]
                q,rem=divmod(num,last)
                assert not rem
                M[i][j]=q
        for i in range(k+1,m):M[i][k]=ZERO
        last=pivot
        print(json.dumps({'stage':k,'seconds':time.monotonic()-started,'pivot_degree':pivot.degree()}),flush=True)
    return sign*M[-1][-1],time.monotonic()-started

def factor_data(p):
    unit,factors=p.factor()
    return {'content':str(unit),'factors':[{'coefficients':[str(x) for x in f],'exponent':e,'display':str(f)} for f,e in factors]}

def main():
    t=[ZERO,ONE];u=[ZERO,n,ONE];v=[ZERO,n-1,ONE];vp=[n,n+1,ONE]
    H=[]
    for a in range(10):
        left=mul(mul([-n-1,ONE],power([n+1,ONE],10)),power(v,a))
        right=mul(mul([2*n+1,ONE],power([-ONE,ONE],10)),power(vp,a))
        h=invariant(add(left,neg(right)))
        assert h[-1]==7*n+18-2*a
        H.append(h)
    D=power([-n-1,ONE],10)
    old=[[ZERO]*r+D for r in range(5)]
    Z=[ONE]
    for a in range(1,4):Z=mul(Z,[-(n+a)*(2*n+a),ONE])
    cn=((n+1)*(n+2))**7
    new=[[cn*x for x in mul(Z,power([-n-1,ONE],r))] for r in range(5)]
    def matrix(cols):return [[c[i] if i<len(c) else ZERO for c in cols] for i in range(15)]
    print('old determinant',flush=True)
    da,ta=bareiss(matrix(old+H))
    print('new determinant',flush=True)
    db,tb=bareiss(matrix(new+H))
    common=da.gcd(db);num,r=divmod(db,common);assert not r
    den,r=divmod(da,common);assert not r
    finite=json.loads((ROOT/'missions/zeta9/round7/verification/connection-audit.json').read_text())
    for case in finite['cases']:
        nn=case['n'];x,y=map(int,case['determinant'])
        assert int(num(nn))*y==int(den(nn))*x
    # Leading homogeneous reduction, y=u/n^2. All ten H_a tend to h(y)y^a.
    h=fmpq_poly([H[0][i][11-2*i] for i in range(6)])
    y=fmpq_poly([0,1])
    AL=fmpq_mat([[((y**(10+r))%h)[j] for j in range(5)] for r in range(5)])
    BL=fmpq_mat([[(((y-2)**3*y**r)%h)[j] for j in range(5)] for r in range(5)])
    ML=BL*AL.inv();TL=ML.inv()
    assert ML.det()==num.leading_coefficient()/den.leading_coefficient()
    def pairs(M):return [[[str(M[i,j].numer()),str(M[i,j].denom())] for j in range(5)] for i in range(5)]
    result={'status':'passed','method':'Z[n] exact Bareiss determinants of fixed 15 by 15 systems',
            'orientation':'F_(n+2) = C_n F_n; det C_n = numerator/denominator',
            'numerator':factor_data(num),'denominator':factor_data(den),
            'numerator_coefficients':[str(x) for x in num],
            'denominator_coefficients':[str(x) for x in den],
            'old_system_determinant':factor_data(da),'new_system_determinant':factor_data(db),
            'old_system_determinant_degree':da.degree(),'new_system_determinant_degree':db.degree(),
            'system_columns_old_then_H':[[[str(x) for x in p] for p in col] for col in old+H],
            'system_columns_new_then_H':[[[str(x) for x in p] for p in col] for col in new+H],
            'homogeneous_limit':{'h_coefficients':[str(x) for x in h],
                'C_limit':pairs(ML),'inverse_weighted_limit':pairs(TL),
                'C_limit_charpoly':[str(x) for x in ML.charpoly()],
                'inverse_weighted_limit_charpoly':[str(x) for x in TL.charpoly()],
                'det_C_limit':str(ML.det())},
            'determinant_seconds':[ta,tb],'independent_finite_comparisons':len(finite['cases']),
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out=ROOT/'missions/zeta9/round7/verification/arithmetic-connection-symbolic.json'
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:result[k] for k in ['status','numerator','denominator','determinant_seconds']},indent=2),flush=True)

if __name__=='__main__':main()
