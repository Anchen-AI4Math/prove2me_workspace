"""Fixed even-block anchor theorem: exact model minors and arithmetic checks."""
from __future__ import annotations
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,sys
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from verify_local_connection import (P,fmpq,fmpq_mat,fmpz,valuation,
                                    local_n_data,minor_values)
from verify_multiblock_budget import sharp_first_budget,d0,old,saving
sys.path.insert(0,str(M/'round6/scripts'))
from independent_audit import independent_columns


def model_certificates():
    results=[]; deltas={}
    for m in range(2,21,2):
        matrix=fmpq_mat(independent_columns(m))
        low=fmpq_mat([[matrix[i,j] for j in (1,2,3)] for i in range(3)])
        # Independent explicit three-by-three determinant formula.
        a,b,c=[[low[i,j] for j in range(3)] for i in range(3)]
        det=(a[0]*(b[1]*c[2]-b[2]*c[1])
             -a[1]*(b[0]*c[2]-b[2]*c[0])
             +a[2]*(b[0]*c[1]-b[1]*c[0]))
        assert det==low.det() and det!=0
        deltas[m]=det
        results.append({'m':m,'low_matrix':[[str(low[i,j]) for j in range(3)] for i in range(3)],
                        'determinant':str(det),'nonzero':True})
    assert deltas[2]==fmpq(70533507825,2)
    return results,deltas


def finite(deltas):
    source=M/'verification/local-connection-2026-09-28/symbolic.json'
    rows=json.loads(source.read_text())['connection']
    def connection(n):
        return fmpq_mat([[fmpq(P(list(map(int,e['numerator'])))(n),
                                     P(list(map(int,e['denominator'])))(n)) for e in row] for row in rows])
    targets=[]
    for m,p in ((2,11),(2,13),(2,29),(2,31),(4,19),(4,23),(6,29)):
        for ratio in (Q(0),Q(1,3),Q(5,6)):
            n=m*p+int(ratio*p)
            n+=n%2
            assert p*p>Q(7*n,2)
            targets.append((m,p,n))
    wanted={n for m,p,n in targets};data={};anchors={}
    f=fmpq_mat(independent_columns(2))
    for n in range(2,max(wanted)+1,2):
        if n in wanted:
            data[n]=local_n_data(f)
            for m,p,nn in targets:
                if nn==n==m*p:
                    U=fmpq_mat([[f[i,j]*fmpq(p)**([9,6,4,2,0][j]-2*i)
                                 for j in range(5)] for i in range(5)])
                    assert all(valuation(U[i,j],p)>=0 for i in range(5) for j in range(5))
                    assert valuation(U.det(),p)==0
                    anchors[(m,p)]=True
        if n<max(wanted):f=connection(n)*f
    checks=[]
    for m,p,n in targets:
        det,small,mixed=data[n]
        delta3=min(valuation(v,p) for v in small)
        delta4=min(valuation(v,p) for v in mixed)
        a1=delta4-delta3;a2=valuation(det,p)-delta4
        e=valuation(deltas[m],p)
        assert e>=0
        assert a1>=-3-e
        if n==m*p:
            assert delta3>=-6
            assert valuation(det,p)==-1
            assert a2<=8+e and a2-a1<=11+2*e
            bound=11+2*e
        else:
            d=d0(Q(n,p))
            assert a2<=9+d+e and a2-a1<=12+d+2*e
            bound=12+d+2*e
        checks.append({'m':m,'p':p,'n':n,'exception_exponent':e,'plane':[a1,a2],
                       'N_valuation':a2-a1,'upper':bound})
    return {'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'unit_scaled_full_matrix_checks':len(anchors),'plane_cases':checks,
            'largest_n':max(wanted)}


def budget():
    gain=Q(0); blocks=[]
    cuts=sorted({Q(0),Q(1),Q(2,3)}|{Q(2*j,d) for d in (3,7) for j in range(d+1) if Q(2*j,d)<1})
    for m in range(2,21,2):
        g=Q(0)
        for aa,bb in zip(cuts,cuts[1:]):
            a=m+aa;b=m+bb;y=(a+b)/2;t=y-m
            before=old(t)-saving(t)
            after=1+d0(t)
            assert before>=after
            g+=(before-after)*(1/a-1/b)
        gain+=g
        blocks.append({'m':m,'exact_gain':str(g),'decimal_gain':float(g)})
    base=sharp_first_budget()
    lower=Q(base['nonnegative_integral_lower'])-gain
    upper=Q(base['nonnegative_integral_upper'])-gain
    return {'covered_even_blocks':list(range(2,21,2)),'block_gains':blocks,
            'exact_additional_gain':str(gain),'decimal_additional_gain':float(gain),
            'integral_lower':str(lower),'integral_upper':str(upper),
            'integral_lower_decimal':float(lower),'integral_upper_decimal':float(upper),
            'dependency':'Previous joint plane/odd/reverse envelope; fixed exceptional primes contribute o(n).'}


def main():
    models,deltas=model_certificates()
    result={'status':'passed','models':models,'finite':finite(deltas),'budget':budget(),
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'boundary':'Uniform argument is in the note; no Lean proof or irrationality claim.'}
    out=M/'verification/even-block-direction-2026-09-29';out.mkdir(parents=True,exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':result['status'],'model_count':len(models),
                     'case_count':len(result['finite']['plane_cases']),'budget':result['budget']},indent=2))
if __name__=='__main__':main()
