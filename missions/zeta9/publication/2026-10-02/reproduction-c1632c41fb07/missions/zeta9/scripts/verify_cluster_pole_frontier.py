"""Small exact checks of clustered-pole translation and primitive growth bounds."""
from __future__ import annotations
import hashlib
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT.parents[1]/"tmp/zeta7/exact_packages"))
from flint import fmpq as Q, fmpq_mat as Mat, fmpq_poly as Poly, arb, ctx

X = Poly([0,1])


def primes(n):
    return [p for p in range(2,n+1)
            if all(p%q for q in range(2,math.isqrt(p)+1))]


def vp_int(n,p):
    n=abs(n)
    if n==0:
        return 10**9
    count=0
    while n%p==0:
        n//=p
        count+=1
    return count


def vp(x,p):
    return vp_int(int(x.numerator),p)-vp_int(int(x.denominator),p)


def moment(e):
    return (-1)**e*Q.bernoulli(2*e+2)*Q(math.factorial(2*e+9),
                                      math.factorial(8)*math.factorial(2*e+2))


def interpolate(matrixR,matrixB,h):
    F=Poly([0])
    for j in range(h+1):
        value=(matrixR+j*matrixB).det()
        basis=Poly([1]); divisor=1
        for k in range(h+1):
            if j!=k:
                basis*=X-k
                divisor*=j-k
        F+=basis*Q(value,divisor)
    for z in [-2,-1,h+1]:
        assert F(z)==(matrixR+z*matrixB).det()
    return F


def construct(poles,h,coefficients,label):
    poles=tuple(poles)
    assert poles==tuple(sorted(set(poles))) and poles[0]>=1
    S=Poly(coefficients)
    m,u,b,a=len(poles),S.degree(),poles[-1],poles[0]
    W=b-a; H=max(abs(c) for c in coefficients)
    denominator=Poly([1])
    for c in poles:
        denominator*=X+c*c
    derivative=denominator.derivative()
    harmonics=[Q(0)]
    for j in range(1,b+1):
        harmonics.append(harmonics[-1]+Q(1,j**9))
    K0=u+2*h-2
    K=math.lcm(*(int(moment(e).denominator) for e in range(K0+1)))
    V=math.prod(poles[j]**2-poles[i]**2 for i in range(m) for j in range(i+1,m))
    ell=math.lcm(*range(a+1,b+1)) if W else 1
    L=8*K*V*math.prod(poles)*ell**9
    if W:
        assert math.comb(b,W)*math.lcm(*range(1,W+1))%ell==0
    M0=max([Q(1)]+[abs(moment(e)) for e in range(K0+1)])
    C0=(u+1)*((K0+1)*math.comb(m+K0,K0)*M0+2*m+1)
    exponent=2*K0+9
    Rmom=[]; Bmom=[]; originalmom=[]
    cancelled=[]
    for c in poles:
        if S(-c*c)==0:
            cancelled.append(c)
    for k in range(2*h-1):
        numerator=S*X**k
        quotient,remainder=divmod(numerator,denominator)
        rq=sum((quotient[e]*moment(e) for e in range(len(quotient))),Q(0))
        rr=rq; bb=Q(0); aa=rq
        for c in poles:
            residue=remainder(-c*c)/derivative(-c*c)
            assert residue==S(-c*c)*(-c*c)**k/derivative(-c*c)
            rr+=residue*(-c**8*(harmonics[c]-harmonics[a])-Q(1,8)+Q(1,2*c))
            aa+=residue*(-c**8*harmonics[c]-Q(1,8)+Q(1,2*c))
            bb+=residue*c**8
        Rmom.append(rr); Bmom.append(bb); originalmom.append(aa)
    R=Mat([[Rmom[i+j] for j in range(h)] for i in range(h)])
    B=Mat([[Bmom[i+j] for j in range(h)] for i in range(h)])
    C=Mat([[originalmom[i+j] for j in range(h)] for i in range(h)])
    assert R==C+harmonics[a]*B
    for i in range(h):
        for j in range(h):
            assert (L*R[i,j]).denominator==1
            assert B[i,j].denominator==1
            assert abs(R[i,j])<=C0*H*b**exponent
            assert abs(B[i,j])<=C0*H*b**exponent
    F=interpolate(R,B,h)
    assert F.degree()==B.rank()
    d=F.degree()
    Delta=sum((F[i]*(X-harmonics[a])**i for i in range(d+1)),Poly([0]))
    for z in [-1,0,1,2]:
        assert Delta(z)==(C+z*B).det()
    Ai=[int((L**h*F[i]).numerator) for i in range(d+1)]
    for j in range(d+1):
        assert (L**h*F[j]).denominator==1
        assert abs(Ai[j])<=math.factorial(h)*math.comb(h,j)*(C0*L*H*b**exponent)**h
    Ad=abs(Ai[-1]); assert Ad>0
    coefficient_clearer=math.lcm(*(int(c.denominator) for c in Delta))
    integer_coeff=[int((c*coefficient_clearer).numerator) for c in Delta]
    content=math.gcd(*integer_coeff)
    primitive=[c//content for c in integer_coeff]
    multiplier=Q(coefficient_clearer,content)
    assert Poly(primitive)==Delta*multiplier
    assert math.gcd(*primitive)==1
    assert Ad%int(multiplier.denominator)==0
    T=int(harmonics[a].denominator)
    ratio=Q(L**h*T**d)/multiplier
    assert ratio.denominator==1 and ratio>=1
    small=1; goodT=1; bad=1; good=[]
    for p in primes(a):
        e=vp_int(T,p)
        if not e:
            continue
        if p*p<=a:
            small*=p**e
        elif (L*Ad)%p==0:
            assert e<=9
            bad*=p**e
        else:
            assert 1<=e<=9
            goodT*=p**e
            assert vp(Delta[0],p)==-d*e
            assert vp(multiplier,p)==d*e
            for i in range(d+1):
                assert vp(Delta[i],p)>=-(d-i)*e
            good.append({"p":p,"v_p_T":e,"v_p_c":d*e})
    assert T==small*bad*goodT
    assert (L*Ad)**9%bad==0
    assert int(multiplier.numerator)%goodT**d==0
    lower=Q(T**d,Ad*small**d*(L*Ad)**(9*d))
    upper=Q(L**h*T**d)
    assert lower<=multiplier<=upper
    if d==0:
        assert primitive==[1] and Delta[0]>0
    precision=max(512,max(abs(c).bit_length() for c in primitive)+256)
    ctx.prec=precision
    zeta=arb(9).zeta()
    value=arb(0)
    for c in reversed(primitive):
        value=value*zeta+c
    assert value>0 and value.rel_accuracy_bits()>=80
    return {"label":label,"poles":list(poles),"h":h,"m":m,"S":coefficients,
            "height":str(H),"width":W,"degree":d,"cancelled_poles":cancelled,
            "L":str(L),"A_d":str(Ai[-1]),"harmonic_denominator_T":str(T),
            "primitive_coefficients":[str(c) for c in primitive],
            "minimal_positive_multiplier":str(multiplier),"good_prime_checks":good,
            "normalization_bound_lower":str(lower),"normalization_bound_upper":str(upper),
            "positive_value_ball":value.str(25),"precision_bits":precision,
            "all_exact_clearer_height_translation_checks":"PASS"}, C, B


def cases():
    answer=[]
    def add(amin,offsets,h,S,label):
        answer.append(([amin+x for x in offsets],h,S,label))
    for amin in [2,11,31]:
        add(amin,[0,3],1,[1],"two nonconsecutive poles")
    for amin in [2,17,41]:
        add(amin,[0,2,6],2,[1],"full rank h<m")
    for amin in [3,19]:
        add(amin,[0,1,3,4,7,8,12],2,[1],"rank one live low block")
    for amin in [2,23]:
        add(amin,[0,2,3,5,7,8,11,14],2,[1],"degree zero")
    for amin in [13,37]:
        add(amin,[0,4,7],2,[2,3,1],"nonnegative numerator")
    for amin in [7,29]:
        add(amin,[0,1,4,8,10],3,[1,-2,1],"positive-axis zero numerator")
    for C in [31,1009]:
        add(11,[0,1,4,9],2,[1,2*C,C*C],"varying numerator height")
    add(13,[0,4],3,[1],"m<h")
    add(23,[0],2,[1],"single pole m<h")
    add(7,[0,3,6],2,[49,1],"numerator cancels first pole")
    add(10,[0,3],2,[1],"cancelled-weight comparison")
    return answer


def main():
    sys.set_int_max_str_digits(0)
    records=[]; matrices=[]
    for args in cases():
        row,C,B=construct(*args)
        records.append(row); matrices.append((C,B))
    assert matrices[-1]==matrices[-2]
    assert records[-1]["primitive_coefficients"]==records[-2]["primitive_coefficients"]
    sources=[Path(__file__),ROOT/"research/cluster-pole-frontier-2026-10-01.md"]
    payload={"result":"PASS","date":"2026-10-01","cases":len(records),
             "arithmetic":"exact FLINT rationals; Arb finite positive evaluations",
             "boundary":"finite verification; written proof/PNT establish exact asymptotic rate; no Lean",
             "good_prime_valuation_checks":sum(len(r["good_prime_checks"]) for r in records),
             "degree_zero_cases":sum(r["degree"]==0 for r in records),
             "sources":{str(p.relative_to(ROOT)).replace("\\","/"):hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in sources},"records":records}
    destination=ROOT/"verification/cluster-pole-frontier-2026-10-01"
    destination.mkdir(parents=True,exist_ok=True)
    (destination/"certificate.json").write_text(json.dumps(payload,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:v for k,v in payload.items() if k not in {"records","sources"}},indent=2))


if __name__=="__main__":
    main()
