"""Fixed odd-anchor local-jet certificates and exact finite lattice checks."""
from __future__ import annotations
import hashlib,json,math,sys
from pathlib import Path
from math import comb
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from verify_local_connection import P,QP,fmpq,fmpq_mat,valuation,local_n_data,prime_list,minor_values
OUT=M/'verification/odd-anchor-2026-09-29'

def mul(a,b,limit=None):
    count=len(a)+len(b)-1
    if limit is not None:count=min(count,limit)
    c=[fmpq(0)]*count
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<count:c[i+j]+=x*y
    return c

def parts(m,degree):
    rows=[]
    for k in range(m+1):
        local=[fmpq(1)]
        for a in range(1,m+1):local=mul(local,[-k-a,1],9)
        for a in range(m+1,2*m+1):local=mul(local,[a-k,1],9)
        for j in range(m+1):
            if j!=k:
                distance=j-k
                inverse=[fmpq((-1)**h*comb(8+h,8),distance**(9+h)) for h in range(9)]
                local=mul(local,inverse,9)
        h=[comb(degree,j)*2**j*(m-2*k)**(degree-j) for j in range(degree+1)]
        local=mul(local,h,9)
        rows.append([local[9-s] for s in range(1,10)])
    # Full identity, all principal parts, no interpolation.
    x=QP([0,1]); denominator=QP([1]); numerator=QP([1])
    for k in range(m+1):denominator*=(x+k)**9
    for a in range(1,m+1):numerator*=x-a
    for a in range(m+1,2*m+1):numerator*=x+a
    numerator*=(2*x+m)**degree
    reconstructed=QP([])
    for k,row in enumerate(rows):
        for s,c in enumerate(row,1):
            quotient,remainder=divmod(denominator,(x+k)**s)
            assert not remainder
            reconstructed+=c*quotient
    assert reconstructed==numerator
    return rows

def matrix_for(m):
    columns=[];records=[]
    for degree in (1,3,5):
        pp=parts(m,degree)
        columns.append([2*sum((row[s-1] for row in pp),fmpq(0)) for s in (3,5,7)])
        records.append({'degree':degree,'principal_coefficients':[[str(c) for c in row] for row in pp]})
    A=fmpq_mat(columns).transpose();det=A.det();assert det
    inv=A.inv()
    for degree in (0,2,4,6,8):
        pp=parts(m,degree)
        assert all(pp[m-k][s-1]==(-1)**s*pp[k][s-1] for k in range(m+1) for s in range(1,10))
    upper_odd_seven=parts(m,7)
    assert all(upper_odd_seven[m-k][s-1]==(-1)**(s+1)*upper_odd_seven[k][s-1] for k in range(m+1) for s in range(1,10))
    denominator_lcm=math.lcm(*(int(inv[i,j].denom()) for i in range(3) for j in range(3)))
    return A,inv,{'m':m,'matrix':[[str(A[i,j]) for j in range(3)] for i in range(3)],
                 'determinant':str(det),'inverse':[[str(inv[i,j]) for j in range(3)] for i in range(3)],
                 'inverse_denominator_lcm':str(denominator_lcm),
                 'antisymmetric_principal_parts':records,'exact_partial_fraction_identities':9}

def main():
    OUT.mkdir(exist_ok=True)
    ms=list(range(1,20,2));matrices={};symbolic=[]
    for m in ms:
        A,inv,record=matrix_for(m);matrices[m]=(A,inv);symbolic.append(record)
        print('symbolic m',m,'det numerator bits',int(A.det().numer()).bit_length(),flush=True)
    source=M/'verification/local-connection-2026-09-28/symbolic.json'
    src=json.loads(source.read_text()); entries=[[(P(list(map(int,e['numerator']))),P(list(map(int,e['denominator'])))) for e in row] for row in src['connection']]
    def connection(n):return fmpq_mat([[fmpq(a(n),b(n)) for a,b in row] for row in entries])
    sys.path.insert(0,str(M/'round6/scripts'))
    from independent_audit import independent_columns
    targets={}
    for m in ms:
        for p in prime_list(61):
            if p>max(7,2*m+2) and m*p+1<=600:targets.setdefault(m*p+1,[]).append((m,p))
    f=fmpq_mat(independent_columns(2));finite=[];raw=[]
    maximum=max(targets)
    for n in range(2,maximum+1,2):
        if n in (34,66):
            assert f==fmpq_mat(independent_columns(n));raw.append(n)
        if n in targets:
            det,small,mixed=local_n_data(f)
            for m,p in targets[n]:
                inv=matrices[m][1]
                e=max(0,-min(valuation(inv[i,j],p) for i in range(3) for j in range(3)))
                lo=min(valuation(x,p) for x in small);mid=min(valuation(x,p) for x in mixed)
                plane=[mid-lo,valuation(det,p)-mid]
                assert plane[0]>=-2-e
                normalized=f*fmpq_mat([[p**([9,6,4,2,0][i]) if i==j else 0 for j in range(5)] for i in range(5)])
                minor4=min(valuation(x,p) for x in minor_values(normalized,4))
                assert minor4>=16
                upper_checked=p>7*m/2
                if upper_checked:
                    assert valuation(det,p)==4 and plane[1]<=9
                    assert plane[1]-plane[0]<=11+e
                finite.append({'n':n,'m':m,'p':p,'inverse_loss':e,'plane':plane,
                               'normalized_four_minor_min':minor4,'upper_bound_checked':upper_checked})
        if n<maximum:f=connection(n)*f
    result={'status':'passed','symbolic':symbolic,'finite':finite,'independent_raw_checks':raw,
            'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'All odd m with nonzero fixed jet determinant; nonzero explicitly certified for m=1,3,...,19. No claim for every odd m.'}
    (OUT/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASSED',len(symbolic),'fixed odd m;',len(finite),'finite anchors; raw',raw,flush=True)
if __name__=='__main__':main()
