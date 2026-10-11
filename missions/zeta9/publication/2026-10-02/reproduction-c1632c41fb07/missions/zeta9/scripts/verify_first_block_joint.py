"""Odd-block merged trace and joint Smith bounds: exact finite audits only.
The parameter-uniform proof is in research/first-block-joint-2026-09-29.md.
"""
from pathlib import Path
from math import comb
import hashlib,json,sys
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from verify_local_connection import P,fmpq,fmpq_mat,valuation,prime_list,local_n_data
from flint import nmod_poly
OUT=M/'verification/first-block-joint-2026-09-29'

def finite_field_traces():
    records=[]
    for m,p,rs in [(1,23,[3,5,9]),(3,43,[5,7,15]),(5,61,[7,9,21])]:
        x=nmod_poly([0,1],p);one=nmod_poly([1],p);h=x**p-x
        for r in rs:
            n=m*p+r;L=9*(m+1);K=7*m+2;assert p>L
            qr=one
            for j in range(r+1):qr*=x+j
            quotient,remainder=divmod(h,qr);assert not remainder
            nr=one
            for j in range(1,r+1):nr*=x-j
            for j in range(r+1,2*r+1):nr*=x+j
            base=quotient**9*h**(2*m)*nr
            for degree in range(5):
                pol=base*(x*(x+r))**degree
                expected= L*p-7*n-9+2*degree
                assert pol.degree()==expected
                # Sum of shifted monomials. For positive k divisible by p-1,
                # sum a^k=-1, all other power sums (including k=0) vanish.
                tr=[0]*(max(0,pol.degree()-(p-1))+1)
                for j,c in enumerate(pol):
                    if not c:continue
                    for k in range(p-1,j+1,p-1):
                        tr[j-k]=(tr[j-k]-int(c)*comb(j,k))%p
                trace=nmod_poly(tr,p)
                assert not trace or trace.degree()<= (L-1)*p-7*n
                # Direct sum of merged pole coefficients from local expansion
                # at all t=-a. h(-a+v)=-v+v^p and L<p.
                q=L-K
                merged=(-1)**(L+1)*sum(int(pol[j])*comb(j,q)
                    for j in range(q+p-1,len(pol),p-1))%p
                if 7*r>p:
                    assert merged==0
                    assert not trace or trace.degree()<(L-K)*p
                records.append({'m':m,'p':p,'r':r,'W_degree':degree,
                                'P_degree':pol.degree(),'trace_degree':trace.degree() if trace else -1,
                                'merged_K':K,'merged_coefficient_sum':merged,
                                'threshold_active':7*r>p})
    assert any(x['merged_coefficient_sum'] for x in records if not x['threshold_active'])
    return records

def real_matrices(limit=800):
    model_path=M/'verification/odd-anchor-2026-09-29/certificate.json'
    models=json.loads(model_path.read_text())['symbolic']
    inverses={r['m']:fmpq_mat([[fmpq(x) for x in row] for row in r['inverse']]) for r in models}
    source=M/'verification/local-connection-2026-09-28/symbolic.json'
    entries=[[(P(list(map(int,e['numerator']))),P(list(map(int,e['denominator'])))) for e in row]
             for row in json.loads(source.read_text())['connection']]
    sys.path.insert(0,str(M/'round6/scripts'))
    from independent_audit import independent_columns
    F=fmpq_mat(independent_columns(2));primes=prime_list(limit);cases=[];raw=[]
    for n in range(2,limit+1,2):
        if n in (28,32):assert F==fmpq_mat(independent_columns(n));raw.append(n)
        det,small,mixed=local_n_data(F)
        for p in primes:
            if p>=n:break
            m,r=divmod(n,p)
            if m not in inverses or not r or p<=9*(m+1):continue
            inverse=inverses[m]
            e=max(0,-min(valuation(inverse[i,j],p) for i in range(3) for j in range(3)))
            delta3=min(valuation(v,p) for v in small)
            delta4=min(valuation(v,p) for v in mixed)
            plane=[delta4-delta3,valuation(det,p)-delta4]
            D=3*n//(2*p)+7*n//(2*p)-10*(n//(2*p))
            assert valuation(det,p)==D and delta3>=-3
            exponent=plane[1]-plane[0]
            assert plane[1]<=10 and exponent<=11+e
            active=7*r>p;window=active and 3*r<p
            if active:assert plane[0]>=-1-e
            if window:assert exponent<=10+e
            cases.append({'n':n,'p':p,'m':m,'r':r,'loss':e,'D0':D,'plane':plane,
                          'trace_active':active,'discount_window':window,'N_valuation':exponent})
        if n<limit:F=fmpq_mat([[fmpq(a(n),b(n)) for a,b in row] for row in entries])*F
    return {'limit':limit,'cases':cases,'independent_raw_checks':raw,
            'model_sha256':hashlib.sha256(model_path.read_bytes()).hexdigest(),
            'connection_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}

def main():
    OUT.mkdir(exist_ok=True)
    traces=finite_field_traces();real=real_matrices()
    result={'status':'passed','merged_trace_audit':traces,'real_matrix_audit':real,
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'Trace identities are tested finitely here; the all-parameter proof is in the accompanying note. Fixed models are certified for odd m<=19.'}
    (OUT/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'passed','trace_cases':len(traces),'real_matrix_cases':len(real['cases']),
                      'trace_active_cases':sum(r['trace_active'] for r in real['cases']),
                      'discount_cases':sum(r['discount_window'] for r in real['cases']),
                      'blocks_seen':sorted({r['m'] for r in real['cases']})},indent=2))
if __name__=='__main__':main()
