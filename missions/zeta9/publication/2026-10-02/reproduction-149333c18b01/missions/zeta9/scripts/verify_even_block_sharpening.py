"""Exact checks for the uniform even-block trace/CRT sharpening theorem."""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
from math import comb
import hashlib,json,sys
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from verify_local_connection import P,fmpq,fmpq_mat,valuation,local_n_data
from verify_multiblock_budget import d0
sys.path.insert(0,str(M/'round6/scripts'))
from independent_audit import independent_columns,product_form,compose_w


def convolution(a,b,N=8):
    c=[0]*(N+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<=N:c[i+j]+=x*y
    return c


def laurent_models():
    records=[]
    for m in range(2,21,2):
        series=[1]+[0]*8
        for k in list(range(-m,0))+list(range(m+1,2*m+1)):
            series=convolution(series,[1,k])
        for k in range(m+1):
            series=convolution(series,[(-1)**j*comb(8+j,j)*k**j for j in range(9)])
        columns=[convolution(series,[comb(i,j)*m**j for j in range(i+1)]) for i in range(5)]
        matrix=[[columns[i][2*(i-j)] if i>=j else 0 for i in range(5)] for j in range(5)]
        assert all(matrix[j][j]==1 for j in range(5))
        assert all(matrix[j][i]==0 for j in range(5) for i in range(j))
        records.append({'m':m,'coefficients_after_dividing_factorial_m_power_7':matrix})
    return records


def ordinary_crt():
    n,p,m=74,31,2;r=n-m*p
    base=product_form(9,n,[(n,1)],[1])
    harmonic={s:[fmpq(0)] for s in range(1,10)}
    for s in harmonic:
        for j in range(1,n+1):harmonic[s].append(harmonic[s][-1]+fmpq(1,j**s))
    records=[]
    for degree in (0,4):
        coefficients={s:[] for s in range(1,10)}
        for j in range(n+1):
            local=compose_w([0]*degree+[1],-j,n,8)
            for s in range(1,10):
                coefficients[s].append(sum((local[h]*base['pole_coeffs'][s+h][j] for h in range(10-s)),fmpq(0)))
        B=-sum((coefficients[s][j]*harmonic[s][j] for s in range(1,10) for j in range(n+1)),fmpq(0))
        longsum={(q,s):sum((coefficients[s][a+q*p] for a in range(r+1)),fmpq(0))
                 for q in range(m+1) for s in range(1,10)}
        singular=-sum((longsum[q,s]*fmpq(1,p**s)*harmonic[s][q]
                      for q in range(m+1) for s in range(1,10)),fmpq(0))
        ordinary=-sum((longsum[q,s]*(harmonic[s][q*p]-fmpq(1,p**s)*harmonic[s][q])
                      for q in range(m+1) for s in range(1,10)),fmpq(0))
        units=fmpq(0);minimum=10**9;count=0
        for a in range(r+1):
            for b in range(1,a+1):
                value=sum((coefficients[s][a+q*p]/(b+q*p)**s
                           for q in range(m+1) for s in range(1,10)),fmpq(0))
                assert valuation(value,p)>=7*m
                minimum=min(minimum,valuation(value,p));count+=1;units+=value
        short=-sum((coefficients[s][j]*harmonic[s][j]
                   for s in range(1,10) for j in range(n+1) if j%p>r),fmpq(0))
        assert valuation(short,p)>=0
        assert all(valuation(coefficients[s][j],p)>=s
                   for s in range(1,10) for j in range(n+1) if j%p>r)
        assert B==singular+ordinary-units+short
        records.append({'n':n,'p':p,'W_degree':degree,'exact_identity':True,
                        'unit_evaluations':count,'minimum_unit_evaluation_valuation':minimum,
                        'short_B_valuation':valuation(short,p)})
    return records


def merged_trace():
    records=[]
    m,p=2,31
    for r in (4,10,18,22,28):
        n=m*p+r
        base=product_form(9,n,[(n,1)],[1])
        for degree in (0,4):
            coefficients={s:[] for s in range(1,10)}
            for jj in range(n+1):
                local=compose_w([0]*degree+[1],-jj,n,8)
                for ss in range(1,10):
                    coefficients[ss].append(sum((local[h]*base['pole_coeffs'][ss+h][jj]
                                                 for h in range(10-ss)),fmpq(0)))
            for jet in range(1,5):
                K=7*m+9-2*jet
                # Exactly p^(9-K) times the aggregate merged Laurent moment.
                value=sum((fmpq(p)**(9-ss)*coefficients[ss][jj]
                           *comb(K-1,ss-1)*(-(jj//p))**(K-ss)
                           for jj in range(n+1) for ss in range(1,10)),fmpq(0))
                vp=valuation(value,p)
                assert vp>=2*jet
                active=7*r>(8-2*jet)*p
                if active:assert vp>=2*jet+1
                records.append({'n':n,'p':p,'W_degree':degree,'jet':jet,'K':K,
                                'trace_active':active,'scaled_merged_moment_valuation':vp,
                                'required_if_active':2*jet+1})
    return records


def finite():
    source=M/'verification/local-connection-2026-09-28/symbolic.json'
    rows=json.loads(source.read_text())['connection']
    def connection(n):
        return fmpq_mat([[fmpq(P(list(map(int,e['numerator'])))(n),
                                     P(list(map(int,e['denominator'])))(n)) for e in row] for row in rows])
    targets=[];deltas={}
    for m,p in ((2,43),(2,101),(4,43),(6,59)):
        fm=fmpq_mat(independent_columns(m))
        deltas[m]=fmpq_mat([[fm[i,j] for j in (1,2,3)] for i in range(3)]).det()
        rs=set()
        for fraction in (Q(1,7),Q(2,7),Q(4,7),Q(2,3),Q(6,7),Q(13,14)):
            rr=int(fraction*p);rr-=rr%2
            rs.update((rr,rr+2))
        for rr in sorted(rs):
            if 0<rr<p:targets.append((m,p,m*p+rr))
    wanted={n for m,p,n in targets};saved={}
    f=fmpq_mat(independent_columns(2))
    for n in range(2,max(wanted)+1,2):
        if n in wanted:saved[n]=(f.inv(),local_n_data(f))
        if n<max(wanted):f=connection(n)*f
    records=[]
    for m,p,n in targets:
        inverse,(det,small,mixed)=saved[n]
        e=valuation(deltas[m],p);r=n-m*p;D=d0(Q(n,p))
        assert p>7*m+9
        min_inverse=min(valuation(inverse[i,j],p) for i in range(5) for j in range(5))
        assert min_inverse>=-9
        assert valuation(det,p)==D
        delta3=min(valuation(x,p) for x in small);delta4=min(valuation(x,p) for x in mixed)
        a1=delta4-delta3;a2=valuation(det,p)-delta4
        assert a2<=9
        improved=int(7*r>2*p)
        assert a1>=-3-e+improved
        assert a2-a1<=12+e-improved
        records.append({'m':m,'p':p,'n':n,'r':r,'D0':D,'exception_exponent':e,
                        'full_inverse_minimum_valuation':min_inverse,'plane':[a1,a2],
                        'N_valuation':a2-a1,'new_upper':12+e-improved})
    return {'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'largest_n':max(wanted),'cases':records}


def threshold_audit():
    cuts=sorted({Q(0),Q(1),Q(2,7),Q(4,7),Q(6,7),Q(2,3)})
    rows=[]
    for a,b in zip(cuts,cuts[1:]):
        t=(a+b)/2
        weights=[int(t>=Q(2,3)),2+int(t>Q(6,7)),4+int(t>Q(4,7)),6+int(t>Q(2,7))]
        assert sum(weights)==12+d0(t)
        assert max(weights)<9
        rows.append({'interval':[str(a),str(b)],'weights':weights,'D0':d0(t)})
    assert Q(1,2)-Q(7,16)==Q(1,16)
    return {'segments':rows,'second_block_excess_integral':'1/16',
            'warning':'This is the certified local envelope integral, not the actual budget.'}


def main():
    result={'status':'passed','laurent_models':laurent_models(),'ordinary_CRT':ordinary_crt(),'merged_trace':merged_trace(),
            'finite':finite(),'threshold_audit':threshold_audit(),
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'boundary':'No Lean proof or irrationality claim; uniform proof is in the research note.'}
    out=M/'verification/even-block-sharpening-2026-09-29';out.mkdir(parents=True,exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':result['status'],'model_count':len(result['laurent_models']),
                     'ordinary_CRT':result['ordinary_CRT'],'finite_cases':len(result['finite']['cases']),'merged_trace_cases':len(result['merged_trace']),
                     'largest_n':result['finite']['largest_n'],'threshold_audit':result['threshold_audit']},indent=2))
if __name__=='__main__':main()
