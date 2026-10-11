"""Exact fixed local-plane certificate and finite audits, no zeta numerics.
The all-prime argument is in research/local-plane-2026-09-29.md.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import sys
from pathlib import Path
from math import comb
M = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(M/'scripts'))
from verify_local_connection import (P, fmpq, fmpq_mat, fmpz, valuation,
                                    prime_list, minor_values, local_n_data)
OUT=M/'verification/local-plane-2026-09-29'

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def principal(h):
    # g(z) h(z), g=(z-1)(z+2)/(z^9(z+1)^9).
    numerator=mul([-2,1,1],h)
    a=[sum(numerator[j]*(-1)**(9-s-j)*comb(17-s-j,8)
           for j in range(min(len(numerator),10-s))) for s in range(1,10)]
    # Reflect z -> -1-z by the binomial theorem, and repeat at z=0.
    reflected=[sum(h[k]*(-1)**k*comb(k,j) for k in range(j,len(h)))
               for j in range(len(h))]
    rn=mul([-2,1,1],reflected)
    b=[(-1)**s*sum(rn[j]*(-1)**(9-s-j)*comb(17-s-j,8)
           for j in range(min(len(rn),10-s))) for s in range(1,10)]
    # An exact polynomial identity certifies that these are all principal
    # parts. Degree h <= 6 makes the rational function proper.
    z=P([0,1]); one=P([1]); numerator=P(numerator)
    rebuilt=P([])
    for s in range(1,10):
        rebuilt += a[s-1]*z**(9-s)*(z+1)**9
        rebuilt += b[s-1]*z**9*(z+1)**(9-s)
    assert numerator == rebuilt
    return a,b

def symbolic():
    basis=[]; columns=[]; bvalues=[]
    for degree in (1,3,5):
        h=[comb(degree,j)*2**j for j in range(degree+1)]
        a,b=principal(h)
        columns.append([2*(a[s-1]+b[s-1]) for s in (3,5,7)])
        bvalues.append(-sum(y+(-1)**(s+1)*x
                           for s,x,y in zip(range(1,10),a,b)))
        basis.append({'degree':degree,'coefficients':h,'at_zero':a,'at_minus_one':b})
    matrix=fmpq_mat(columns).transpose()
    assert matrix.det()==-2**14*3*257
    inverse=matrix.inv()
    assert matrix*inverse==fmpq_mat([[int(i==j) for j in range(3)] for i in range(3)])
    for i in range(3):
        for j in range(3):
            assert 2**14*3*257*inverse[i,j] == int(2**14*3*257*inverse[i,j])
    # Every symmetric basis vector is killed by all odd-zeta sums and by
    # the singular B functional, not just by the selected three rows.
    symmetric=[]
    for degree in (0,2,4,6):
        a,b=principal([comb(degree,j)*2**j for j in range(degree+1)])
        assert all(a[s-1]+b[s-1]==0 for s in (1,3,5,7,9))
        assert all(b[s-1]+(-1)**(s+1)*a[s-1]==0 for s in range(1,10))
        symmetric.append(degree)
    return {'antisymmetric_basis':basis,'low_zeta_matrix':[[str(matrix[i,j]) for j in range(3)] for i in range(3)],
            'determinant':str(matrix.det()),'factorization':[['2',14],['3',1],['257',1]],
            'inverse':[[str(inverse[i,j]) for j in range(3)] for i in range(3)],
            'B_singular_functional':bvalues,
            'B_from_low_zeta':[str(x) for x in (fmpq_mat([bvalues])*inverse).entries()],
            'symmetric_degrees_annihilated':symmetric,'exact_partial_fraction_identities':7}

def local_info(f,p,profile=False):
    det,small,mixed=local_n_data(f)
    lo=min(valuation(x,p) for x in small)
    mid=min(valuation(x,p) for x in mixed)
    plane=[mid-lo,valuation(det,p)-mid]
    result={'n_exponent':plane[1]-plane[0],'plane':plane}
    if profile:
        sums=[min(valuation(x,p) for x in minor_values(f,k)) for k in range(1,6)]
        result['five_dimensional_profile']=[sums[0]]+[sums[k]-sums[k-1] for k in range(1,5)]
    return result

def finite(limit):
    source=M/'verification/local-connection-2026-09-28/symbolic.json'
    data=json.loads(source.read_text())
    entries=[[(P(list(map(int,e['numerator']))),P(list(map(int,e['denominator']))))
              for e in row] for row in data['connection']]
    def connection(n):
        return fmpq_mat([[fmpq(a(n),b(n)) for a,b in row] for row in entries])
    sys.path.insert(0,str(M/'round6/scripts'))
    from independent_audit import independent_columns
    primes=prime_list(limit)
    f=fmpq_mat(independent_columns(2)); boundaries=[]; checks=[]; raw=[]
    for n in range(2,limit+1,2):
        if n in (12,38,80):
            assert f==fmpq_mat(independent_columns(n)); raw.append(n)
        candidates=[p for p in primes if max(7,n//2)<p<n]
        if candidates:
            det,small,mixed=local_n_data(f)
            for p in candidates:
                lo=min(valuation(x,p) for x in small)
                mid=min(valuation(x,p) for x in mixed)
                plane=[mid-lo,valuation(det,p)-mid]
                D=3*n//(2*p)+7*n//(2*p)
                bound=7+D+int(p==257)
                assert plane[0]>=-2-int(p==257)
                assert plane[1]<=9+(D-4)
                assert plane[1]-plane[0]<=bound
                row={'n':n,'p':p,'plane':plane,'N_valuation':plane[1]-plane[0],'bound':bound}
                checks.append(row)
                if p==n-1:
                    info=local_info(f,p,True)
                    assert plane==info['plane']
                    boundaries.append({**row,**info})
        if n<limit: f=connection(n)*f
    anomaly=next(r for r in boundaries if r['p']==257) if limit>=258 else None
    if anomaly: assert anomaly['plane']==[-3,9]
    return {'limit':limit,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'independent_raw_checks':raw,'interval_case_count':len(checks),'interval_cases':checks,
            'boundary_cases':boundaries,'exception_257':anomaly}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--limit',type=int,default=520)
    args=parser.parse_args(); assert args.limit>=2 and args.limit%2==0
    OUT.mkdir(exist_ok=True)
    result={'status':'passed','symbolic':symbolic(),'finite':finite(args.limit),
            'budget':{'previous_envelope_integral':'C-8','new_envelope_integral':'C-11',
                      'exact_additional_gain':'3','strict_upper':'11.337',
                      'exceptional_prime_257':'finite; normalized contribution tends to zero'},
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (OUT/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'passed','interval_cases':result['finite']['interval_case_count'],
                      'boundary_cases':len(result['finite']['boundary_cases']),
                      'raw_checks':result['finite']['independent_raw_checks'],
                      'exception_257':result['finite']['exception_257']},indent=2))
if __name__=='__main__':main()

