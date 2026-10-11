"""Exact row-pole certificate and first-block inverse-lattice audit."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
import hashlib, json, sys
M = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(M/'scripts'))
from verify_local_connection import P, fmpq, fmpq_mat, valuation, prime_list

def run(limit=520):
    source = M/'verification/local-connection-2026-09-28/symbolic.json'
    rows = json.loads(source.read_text())['connection']
    entries = [[(P(list(map(int,e['numerator']))),P(list(map(int,e['denominator']))))
                for e in row] for row in rows]
    x = P([0,1]); d = (x+1)**8*(x+2)**10
    row_certificate = []
    for r,row in enumerate(entries):
        quotients = []
        for num,den in row:
            scale,rem = divmod(d,den); assert not rem
            pol = num*scale
            quotient,rem = divmod(pol,(x+2)**(2*r)); assert not rem
            quotients.append([str(c) for c in quotient])
        row_certificate.append({'row':r,'divisor_power':2*r,
                                'quotients':quotients,'all_remainders_zero':True})
    def C(n): return fmpq_mat([[fmpq(a(n),b(n)) for a,b in row] for row in entries])
    sys.path.insert(0,str(M/'round6/scripts'))
    from independent_audit import independent_columns
    F = fmpq_mat(independent_columns(2)); primes = [p for p in prime_list(limit) if p>7]
    anchor_cases = []; interval_cases = []; exception_cases = []; odd_block_cases = []
    for n in range(2,limit+1,2):
        inverse = F.inv()
        for p in primes:
            if n%p or (n//p)%2 or p<=7*(n//p)/2: continue
            m = n//p
            S = [9,6,4,2,0]
            U = fmpq_mat([[F[r,j]*p**S[j]/p**(2*r) for j in range(5)] for r in range(5)])
            assert all(valuation(U[r,j],p)>=0 for r in range(5) for j in range(5))
            assert valuation(U.det(),p)==0 and valuation(F.det(),p)==-1
            back = inverse*C(n-2)
            assert all(valuation(back[r,j],p)>=-10 for r in range(5) for j in range(5))
            anchor_cases.append({'n':n,'p':p,'block':m,'normalized_det_valuation':0,
                                 'previous_inverse_min':min(valuation(z,p) for z in back.entries())})
        for p in primes:
            m=n//p
            if m<1 or m%2==0 or n%p==0 or p<=7*(m+1)/2: continue
            full_upper=-min(valuation(z,p) for z in inverse.entries())
            assert full_upper<=10
            odd_block_cases.append({'n':n,'p':p,'block':m,'full_upper':full_upper})
        candidates = [p for p in primes if n//2<p<n]
        E = fmpq_mat([[inverse[i,j] for j in range(5)] for i in (0,4)])
        minors = [E[0,i]*E[1,j]-E[0,j]*E[1,i] for i,j in combinations(range(5),2)]
        for p in candidates:
            full_upper = -min(valuation(z,p) for z in inverse.entries())
            assert full_upper<=10
            mu1 = min(valuation(z,p) for z in E.entries())
            mu2 = min(valuation(z,p) for z in minors)
            plane = [mu1-mu2,-mu1]
            D = 3*n//(2*p)+7*n//(2*p)
            bound = min(7+D,12)+int(p==257)
            assert plane[1]<=min(5+D,10)
            assert plane[0]>=-2-int(p==257)
            assert plane[1]-plane[0]<=bound
            entry = {'n':n,'p':p,'plane':plane,'full_upper':full_upper,'bound':bound}
            interval_cases.append(entry)
            if plane[1]-plane[0]>11: exception_cases.append(entry)
        if n<limit: F=C(n)*F
    cuts = [Q(1),Q(8,7),Q(4,3),Q(10,7),Q(12,7),Q(2)]
    old = Q(0); new = Q(0)
    for a,b in zip(cuts,cuts[1:]):
        y=(a+b)/2; D=(3*y)//2+(7*y)//2
        old+=(D-4)*(1/a-1/b)
        new+=min(D-4,1)*(1/a-1/b)
    assert old==Q(109,120) and new==Q(3,8) and old-new==Q(8,15)
    result={'status':'passed','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'row_polynomial_certificate':row_certificate,
            'finite':{'limit':limit,'even_anchor_count':len(anchor_cases),'even_anchor_cases':anchor_cases,
                      'interval_count':len(interval_cases),'exception_cases':exception_cases,
                      'all_odd_block_inverse_count':len(odd_block_cases),
                      'all_odd_block_records_sha256':hashlib.sha256(json.dumps(odd_block_cases,sort_keys=True).encode()).hexdigest(),
                      'interval_records_sha256':hashlib.sha256(json.dumps(interval_cases,sort_keys=True).encode()).hexdigest()},
            'budget':{'previous_first_block':str(old),'new_first_block':str(new),'exact_gain':str(old-new)},
            'warning':'Polynomial identities and written proof establish the theorem; finite cases are implementation checks.'}
    out=M/'verification/first-block-refinement-2026-09-29';out.mkdir(exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'passed','even_anchors':len(anchor_cases),'intervals':len(interval_cases),
                      'all_odd_block_inverses':len(odd_block_cases),
                      'budget':result['budget']},indent=2))

if __name__=='__main__': run()
