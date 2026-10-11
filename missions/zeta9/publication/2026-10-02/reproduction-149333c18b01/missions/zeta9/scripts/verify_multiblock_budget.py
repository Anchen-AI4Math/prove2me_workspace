"""Exact reverse-connection multiblock bounds and rational budget audit."""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import sys

MISSION = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(MISSION / 'scripts'))
from verify_local_connection import (P, fmpq, fmpq_mat, prime_list,
    local_n_data, local_n_exponent)


def d0(y):
    return (3*y)//2+(7*y)//2-10*(y//2)


def old(y):
    return 19+d0(y)-5*int(y-y//1 >= Q(2,3))


def saving(y):
    t=y-2*(y//2)
    if t<Q(2,3):
        return max(0,2*d0(t)-1)
    if 1<=t<Q(5,3):
        return max(0,2*d0(t)-9)
    return 0


def new(y):
    return 2+d0(y) if y<2 else old(y)-saving(y)


def budget():
    cuts=sorted({Q(0),Q(1),Q(2),Q(2,3),Q(5,3)} |
                {Q(2*j,d) for d in (3,7) for j in range(d+1)})
    mu=sum((b-a)*(old((a+b)/2)-saving((a+b)/2))
           for a,b in zip(cuts,cuts[1:]))/2
    assert mu==Q(283,14)
    primitive=Q(0); endpoints=[]
    for a,b in zip(cuts,cuts[1:]):
        primitive+=(b-a)*(old((a+b)/2)-saving((a+b)/2)-mu)
        assert -Q(11,6)<=primitive<=0
        endpoints.append({'endpoint':str(b),'primitive':str(primitive)})
    assert primitive==0
    integral=Q(0); gain=Q(0)
    for k in range(1,100):
        cuts={Q(k),Q(k+1),Q(k)+Q(2,3)}
        for d in (3,7):
            cuts.update(Q(2*j,d) for j in range(d*k//2,d*(k+1)//2+2)
                        if k<Q(2*j,d)<k+1)
        cuts=sorted(cuts)
        for a,b in zip(cuts,cuts[1:]):
            y=(a+b)/2
            integral+=new(y)*(1/a-1/b)
            if y>=2:
                gain+=saving(y)*(1/a-1/b)
    upper=integral+mu/100
    lower=upper-Q(11,60000)
    assert Q(13846,1000)<lower<=upper<Q(13847,1000)
    return {'periodic_mean':str(mu),'primitive_endpoints':endpoints,
            'integral_lower':str(lower),'integral_upper':str(upper),
            'integral_lower_decimal':float(lower),'integral_upper_decimal':float(upper),
            'gain_on_2_to_100':str(gain),'strict_interval':'13.846 < I < 13.847'}


def joint_budget():
    """Uses the independently cross-reviewed odd-block valuation theorem."""
    def joint_period(t):
        if t>=1:
            return 14+d0(t)
        return old(t)-saving(t)
    cuts=sorted({Q(0),Q(1),Q(2),Q(2,3),Q(5,3)} |
                {Q(2*j,d) for d in (3,7) for j in range(d+1)})
    mu=sum((b-a)*joint_period((a+b)/2) for a,b in zip(cuts,cuts[1:]))/2
    assert mu==Q(407,21)
    primitive=Q(0); endpoints=[]
    for a,b in zip(cuts,cuts[1:]):
        primitive+=(b-a)*(joint_period((a+b)/2)-mu)
        assert -Q(80,63)<=primitive<=0
        endpoints.append({'endpoint':str(b),'primitive':str(primitive)})
    assert primitive==0
    integral=Q(0)
    for k in range(1,100):
        segment=sorted(Q(k-k%2)+t for t in cuts if k<=Q(k-k%2)+t<=k+1)
        for a,b in zip(segment,segment[1:]):
            y=(a+b)/2
            value=2+d0(y) if y<2 else joint_period(y-2*(y//2))
            integral+=value*(1/a-1/b)
    upper=integral+mu/100
    lower=upper-Q(80,630000)
    assert Q(13485,1000)<lower<=upper<Q(13486,1000)
    return {'dependency':'Independent odd-block theorem v_p(N_n) <= 25 + D_(n,p)',
            'periodic_mean':str(mu),'primitive_endpoints':endpoints,
            'integral_lower':str(lower),'integral_upper':str(upper),
            'integral_lower_decimal':float(lower),'integral_upper_decimal':float(upper),
            'strict_interval':'13.485 < I_joint < 13.486'}


def sharp_first_budget():
    """Adds the separately audited plane bound v_p(N_n) <= 7 + D on 1<y<2."""
    joint=joint_budget()
    lower=Q(joint['integral_lower'])-3
    upper=Q(joint['integral_upper'])-3
    assert Q(10485,1000)<lower<=upper<Q(10486,1000)
    # Both signed and nonnegative envelopes coincide because 7+D >= 11.
    for d in range(4,9):
        assert max(7+d-11,0)==max(7+d,2)-11==d-4
        assert (2+d)-(d-4)==6
    assert 6*(Q(1)-Q(1,2))==3
    return {'dependencies':['Odd-block theorem v_p(N_n) <= 25+D',
                            'Plane theorem v_p(N_n) <= 7+D on 1<y<2, fixed prime 257 excepted'],
            'first_block_exact_improvement':'3',
            'nonnegative_integral_lower':str(lower),'nonnegative_integral_upper':str(upper),
            'signed_integral_lower':str(lower),'signed_integral_upper':str(upper),
            'integral_lower_decimal':float(lower),'integral_upper_decimal':float(upper),
            'strict_interval':'10.485 < I_final < 10.486',
            'dependency_status':'Both dependency theorems proved in notes and independently cross-reviewed; no Lean claim.'}


def anchor(n,p):
    m=n//p
    target=max(n, m*p+(2*p+1)//3)
    if target%2:
        target+=1
    assert 3*(target-m*p)>=2*p-1
    return target


def combinatorial_audit():
    count=0
    for p in prime_list(199):
        if p<=43:
            continue
        for m in range(2,2*p//7):
            for n in range(m*p+1, m*p+(2*p+2)//3):
                if n%2 or 3*(n-m*p)>=2*p:
                    continue
                np=anchor(n,p)
                if p*p<=Q(7*np,2):
                    continue
                assert n<=np<(m+1)*p-1
                assert all((k+1)%p and (k+2)%p for k in range(n,np,2))
                dp=d0(Q(np,p)); d=d0(Q(n,p))
                cap=3 if m%2==0 else 7
                assert d<=dp<=cap
                old_cap=30+d-5*int(3*(n-m*p)>=2*p-1)
                exact_reverse_cap=25+2*dp-d
                envelope_cap=11+new(Q(n,p))
                assert min(old_cap,exact_reverse_cap)<=envelope_cap
                count+=1
    return count


def original_matrix_audit():
    source=MISSION/'verification/local-connection-2026-09-28/symbolic.json'
    rows=json.loads(source.read_text())['connection']
    def connection(n):
        return fmpq_mat([[fmpq(P([int(c) for c in e['numerator']])(n),
                                     P([int(c) for c in e['denominator']])(n))
                          for e in row] for row in rows])
    sys.path.insert(0,str(MISSION/'round6/scripts'))
    from independent_audit import independent_columns
    targets=[]
    for p in (47,53):
        for m in (2,3):
            for fraction in (Q(1,3),Q(3,5)):
                n=m*p+int(fraction*p)
                n+=n%2
                np=anchor(n,p)
                assert p*p>Q(7*np,2)
                targets.append((n,p,np))
    wanted={n for n,p,np in targets}|{np for n,p,np in targets}
    matrices={}
    f=fmpq_mat(independent_columns(2))
    for n in range(2,max(wanted)+1,2):
        if n in wanted:
            matrices[n]=local_n_data(f)
        if n<max(wanted):
            f=connection(n)*f
    checks=[]
    for n,p,np in targets:
        vn=local_n_exponent(matrices[n],p)
        vp=local_n_exponent(matrices[np],p)
        d=d0(Q(n,p)); dp=d0(Q(np,p)); r=dp-d
        assert abs(vp-vn)<=r
        assert vp<=25+dp
        assert vn<=25+2*dp-d
        assert vn<=11+new(Q(n,p))
        checks.append({'n':n,'p':p,'anchor':np,'v_n':vn,'v_anchor':vp,
                       'det_increment':r,'reverse_upper':25+2*dp-d,
                       'new_upper':11+new(Q(n,p)),
                       'old_upper':30+d-5*int(3*(n%p)>=2*p-1)})
    return {'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'cases':checks,'largest_matrix_n':max(wanted)}


def main():
    result={'status':'passed','budget':budget(),'joint_budget':joint_budget(),
            'final_budget':sharp_first_budget(),
            'finite_anchor_cases':combinatorial_audit(),
            'original_matrix_checks':original_matrix_audit(),
            'proof_boundary':'Uniform theorem is in the note; finite checks are implementation audits only.',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out=MISSION/'verification/multiblock-budget-2026-09-29'
    out.mkdir(exist_ok=True,parents=True)
    (out/'audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
