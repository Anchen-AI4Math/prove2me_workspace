"""Independent exact integration and real-matrix audit of the twenty-block bound."""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import math
import sys

MISSION = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(MISSION/'scripts'))
from verify_local_connection import (fmpq, fmpq_mat, P, prime_list,
                                     local_n_data, local_n_exponent)


def d0(y):
    return (3*y)//2+(7*y)//2-10*(y//2)


def old_envelope(y):
    if y<2:
        return d0(y)-4
    t=y-2*(y//2)
    if t>=1:
        return 14+d0(t)
    return 19+d0(t)-5*int(t>=Q(2,3))-int(t<Q(2,3))*max(0,2*d0(t)-1)


def envelope(y):
    m=y//1
    if m%2 and m<=19:
        return min(d0(y)-4,1)
    if m%2==0 and 2<=m<=20:
        return 1+d0(y)
    return old_envelope(y)


def cuts_on(a,b):
    cuts={Q(k) for k in range(a,b+1)}
    for den in (1,3,7):
        cuts.update(Q(2*j,den) for j in range(den*a//2,den*b//2+2)
                    if a<Q(2*j,den)<b)
    cuts.update(Q(k)+Q(2,3) for k in range(a,b) if a<Q(k)+Q(2,3)<b)
    return sorted(cuts)


def integrate(fn,a,b):
    cuts=cuts_on(a,b)
    return sum((fn((x+y)/2)*(1/x-1/y) for x,y in zip(cuts,cuts[1:])),Q(0))


def exact_budget():
    # Independent explicit step table for the unchanged periodic tail.
    tail_cuts=list(map(Q,['0','2/7','4/7','2/3','6/7','1','8/7','4/3','10/7','12/7','2']))
    heights=[19,19,18,17,18,18,19,20,21,22]
    mean=sum((b-a)*h for a,b,h in zip(tail_cuts,tail_cuts[1:],heights))/2
    assert mean==Q(407,21)
    primitive=Q(0)
    for a,b,h in zip(tail_cuts,tail_cuts[1:],heights):
        primitive+=(b-a)*(h-mean)
        assert -Q(80,63)<=primitive<=0
    assert primitive==0
    areas=[]; gain=Q(0)
    for m in range(1,21):
        cuts=cuts_on(m,m+1)
        for a,b in zip(cuts,cuts[1:]):
            y=(a+b)/2
            assert 0<=envelope(y)<=old_envelope(y)
        new=integrate(envelope,m,m+1)
        old=integrate(old_envelope,m,m+1)
        gain+=old-new
        areas.append({'block':m,'integral':str(new),'old_integral':str(old),'gain':str(old-new)})
    assert Q(areas[0]['integral'])==Q(3,8)
    assert Q(areas[1]['integral'])==Q(277,720)
    obstruction=Q(areas[0]['integral'])+Q(areas[1]['integral'])
    assert obstruction==Q(547,720)>Q(611,1000)
    main=integrate(envelope,1,100)
    upper=main+mean/100
    lower=upper-Q(80,630000)
    assert Q(2115,1000)<lower<=upper<Q(2116,1000)
    old=json.loads((MISSION/'verification/multiblock-budget-2026-09-29/audit.json').read_text())['final_budget']
    assert Q(old['nonnegative_integral_upper'])-gain==upper
    return {'block_integrals':areas,'exact_gain_from_previous_envelope':str(gain),
            'integral_lower':str(lower),'integral_upper':str(upper),
            'lower_decimal':float(lower),'upper_decimal':float(upper),'strict_upper':'2.116',
            'tail_periodic_mean':str(mean),'tail_primitive_lower':'-80/63',
            'first_two_block_obstruction':str(obstruction),
            'warning':'The obstruction is a limit of these upper envelopes, not a lower bound on the true budget.'}


def source_checks():
    records=[('odd-anchor-2026-09-29/certificate.json','verify_odd_anchor.py'),
             ('even-block-direction-2026-09-29/certificate.json','verify_even_block_direction.py'),
             ('first-block-refinement-2026-09-29/certificate.json','verify_first_block_refinement.py')]
    hashes={}; loaded={}
    for rel,script in records:
        path=MISSION/'verification'/rel
        data=json.loads(path.read_text())
        assert data['status']=='passed'
        digest=hashlib.sha256((MISSION/'scripts'/script).read_bytes()).hexdigest()
        assert data['script_sha256']==digest
        hashes[rel]={'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                     'script_sha256':digest}
        loaded[script]=data
    odd={int(x['m']):x for x in loaded['verify_odd_anchor.py']['symbolic']}
    even={int(x['m']):x for x in loaded['verify_even_block_direction.py']['models']}
    assert sorted(odd)==list(range(1,20,2)) and sorted(even)==list(range(2,21,2))
    for x in odd.values():
        mat=fmpq_mat([[fmpq(v) for v in row] for row in x['matrix']])
        inv=fmpq_mat([[fmpq(v) for v in row] for row in x['inverse']])
        assert mat.det()==fmpq(x['determinant'])!=0
        assert mat*inv==fmpq_mat([[int(i==j) for j in range(3)] for i in range(3)])
    for x in even.values():
        a=[[Q(v) for v in row] for row in x['low_matrix']]
        determinant=(a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
                     -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
                     +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))
        assert determinant==Q(x['determinant'])!=0
    return hashes,odd,even


def vp(q,p):
    q=Q(q)
    def v(a):
        a=abs(a); k=0
        while a%p==0:
            a//=p;k+=1
        return k
    return v(q.numerator)-v(q.denominator)


def finite_check(odd,even):
    source=MISSION/'verification/local-connection-2026-09-28/symbolic.json'
    rows=json.loads(source.read_text())['connection']
    parsed=[[(P(list(map(int,e['numerator']))),P(list(map(int,e['denominator'])))) for e in row] for row in rows]
    sys.path.insert(0,str(MISSION/'round6/scripts'))
    from independent_audit import independent_columns
    F=fmpq_mat(independent_columns(2));cases=[]
    for n in range(2,521,2):
        if n%10==0 or n in (12,24,48,96,192,234,258,384):
            data=local_n_data(F)
            for p in prime_list(n):
                m,r=divmod(n,p)
                if r==0 or not 1<=m<=20 or p<=max(7,Q(7*(m+1),2)):
                    continue
                if m%2:
                    loss=vp(int(odd[m]['inverse_denominator_lcm']),p)
                else:
                    loss=2*vp(even[m]['determinant'],p)
                assert loss>=0
                bound=11+envelope(Q(n,p))+loss
                actual=local_n_exponent(data,p)
                assert actual<=bound
                cases.append({'n':n,'p':p,'block':m,'exception_loss':loss,
                              'actual':actual,'bound':bound})
        if n<520:
            F=fmpq_mat([[fmpq(a(n),b(n)) for a,b in row] for row in parsed])*F
    assert any(x['n']==258 and x['p']==257 and x['exception_loss']==1 for x in cases)
    assert any(x['block']%2==0 and x['exception_loss']>0 for x in cases)
    return {'case_count':len(cases),'cases':cases,
            'connection_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}


def main():
    hashes,odd,even=source_checks()
    result={'status':'passed','budget':exact_budget(),'source_certificates':hashes,
            'finite':finite_check(odd,even),
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'Only fixed blocks 1 through 20 use the new models; the old proven envelope controls the tail.'}
    out=MISSION/'verification/block-budget-continuation-2026-09-29'
    out.mkdir(exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':'passed','real_matrix_cases':result['finite']['case_count'],
                      'strict_upper':result['budget']['strict_upper'],
                      'first_two_block_obstruction':result['budget']['first_two_block_obstruction']},indent=2))


if __name__=='__main__':
    main()
