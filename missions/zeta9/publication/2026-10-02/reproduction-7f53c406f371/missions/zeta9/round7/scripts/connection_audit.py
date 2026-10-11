"""Exact independent finite audit of the uniform n -> n+2 connection.

No zeta value, HNF, LLL or candidate search is used. The polynomial
identity is constructed in t and independently reduced to invariant u.
"""
from __future__ import annotations
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'tmp/zeta7/exact_packages'))
sys.path.insert(0,str(ROOT/'missions/zeta9/round6/scripts'))
sys.set_int_max_str_digits(0)
from flint import fmpq,fmpq_poly,fmpq_mat
from independent_audit import independent_columns

OUT=ROOT/'missions/zeta9/round7/verification'


def pair(x):return [str(x.numer()),str(x.denom())]
def matrix(M):return [[pair(M[i,j]) for j in range(M.ncols())] for i in range(M.nrows())]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def invariant_coefficients(polynomial,u):
    work=fmpq_poly(polynomial)
    result=[fmpq(0)]*max(1,(polynomial.degree()//2+1))
    while work:
        d=work.degree()
        assert d%2==0
        coefficient=work[d]
        result[d//2]=coefficient
        work-=coefficient*u**(d//2)
    return result


def connection(n,crosscheck=False):
    started=time.monotonic()
    t=fmpq_poly([0,1]);u=t*(t+n);v=t*(t+n-1);vp=(t+1)*(t+n)
    H=[(t-n-1)*(t+n+1)**10*v**a-(t+2*n+1)*(t-1)**10*vp**a for a in range(10)]
    HC=[invariant_coefficients(p,u) for p in H]
    for a,row in enumerate(HC):
        assert len(row)==6+a and row[-1]==7*n+18-2*a
    B=[(u-n-1)**10*u**r for r in range(5)]
    BC=[invariant_coefficients(p,u) for p in B]
    system=fmpq_mat([[row[k] if k<len(row) else 0 for row in BC+HC] for k in range(15)])
    C=((n+1)*(n+2))**7
    Z=fmpq_poly([1])
    for a in [1,2,3]: Z*=u-(n+a)*(2*n+a)
    RHS=[C*Z*(u-n-1)**r for r in range(5)]
    RC=[invariant_coefficients(p,u) for p in RHS]
    targets=fmpq_mat([[row[k] if k<len(row) else 0 for row in RC] for k in range(15)])
    solution=system.inv()*targets
    assert system*solution==targets
    polys=[]
    for r in range(5):
        P=sum((solution[j,r]*u**j for j in range(5)),fmpq_poly([0]))
        lhs=(u-n-1)**10*P+sum((solution[a+5,r]*H[a] for a in range(10)),fmpq_poly([0]))
        assert lhs==RHS[r]
        polys.append(P)
    # Rows map new monomial forms to old monomial forms.
    Cmat=fmpq_mat([[solution[j,r] for j in range(5)] for r in range(5)])
    assert Cmat.det()!=0
    if crosscheck:
        old=fmpq_mat(independent_columns(n));new=fmpq_mat(independent_columns(n+2))
        assert Cmat*old==new
    return dict(n=n,connection_rows_new_by_old=matrix(Cmat),determinant=pair(Cmat.det()),
                gosper_coefficients_columns=matrix(fmpq_mat([[solution[a+5,r] for r in range(5)] for a in range(10)])),
                fifteen_by_fifteen_system_det=pair(system.det()),
                t_polynomial_identity_cases=5,full_partial_fraction_crosscheck=crosscheck,
                seconds=time.monotonic()-started)


def main():
    cases=[]
    for n in [2,4,6,12,24,48,96,192]:
        row=connection(n,crosscheck=n in [2,4,6,12])
        assert row['seconds']<120
        cases.append(row)
        print(json.dumps(dict(n=n,status='passed',seconds=row['seconds'],crosscheck=row['full_partial_fraction_crosscheck'])),flush=True)
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'connection-audit.json').write_text(json.dumps(dict(status='passed',cases=cases,
        diagnostic_scope='Fixed low-order polynomial identities; n=2,4,6,12 neighbors used only as algebra regression, not candidate search.',
        script_sha256=sha(Path(__file__))),indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
