"""Exact coefficient certificate for an invariant cone of the actual exterior recurrence."""
from pathlib import Path
import sys,json,math,hashlib
from fractions import Fraction
from itertools import combinations
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from probe_exterior_cone import P,Q,Mat,ENT,V,VI,PAIRS,compound,connection
from verify_local_connection import determinant

def clear(A):
    d=math.lcm(*(int(x.denominator) for x in A.entries()))
    return [[int(A[i,j]*d) for j in range(A.ncols())] for i in range(A.nrows())],d

def shifted(p,N):return p(P([N,1]))

def main():
    x=P([0,1]); den=(x+1)**8*(x+2)**10
    A=[]
    for row in ENT:
        out=[]
        for a,b in row:
            v,r=divmod(a*den,b);assert not r;out.append(v)
        A.append(out)
    comps=[tuple(k for k in range(5) if k not in I) for I in PAIRS]
    nums=[]
    for I,Ic in zip(PAIRS,comps):
        row=[]
        for J,Jc in zip(PAIRS,comps):
            p=determinant([[A[j][i] for i in Ic] for j in Jc])
            p*=(-1)**(sum(I)+sum(J))
            p*=x**(14-2*sum(I))*(x+2)**(2*sum(J))
            row.append(p)
        nums.append(row)
    common=P([])
    for row in nums:
        for p in row:common=common.gcd(p)
    if common.leading_coefficient()<0:common=-common
    for i in range(10):
        for j in range(10):
            nums[i][j],r=divmod(nums[i][j],common);assert not r
    print('raw numerator degrees',sorted({p.degree() for row in nums for p in row}),flush=True)
    L,dl=clear(compound(VI));R,dr=clear(compound(V))
    left=[[sum((L[i][k]*nums[k][j] for k in range(10)),P([])) for j in range(10)] for i in range(10)]
    T=[[-sum((left[i][k]*R[k][j] for k in range(10)),P([])) for j in range(10)] for i in range(10)]
    content=math.gcd(*(int(c) for row in T for p in row for c in p))
    T=[[p//content for p in row] for row in T]
    # Common factors have positive value at every n>=20, checked by shifted coefficients.
    assert all(c>=0 for c in shifted(common,20)) and common(20)>0
    det_P=determinant(A)
    assert all(c>=0 for c in shifted(det_P,20)) and det_P(20)>0
    # Numeric equality up to the same strictly positive scalar checks Jacobi indices.
    for n in (20,22,100):
        inv=connection(n).inv()
        G=Mat([[inv[i,j]*Q((n+2)**(2*j),n**(2*i)) for j in range(5)] for i in range(5)])
        direct=-compound(VI*G*V);scale=Q(T[0][0](n))/direct[0,0]
        assert scale>0
        assert all(T[i][j](n)==scale*direct[i,j] for i in range(10) for j in range(10))
    # Coefficientwise absolute upper bounds after n=N+t, t>=0.
    N=20; shifted_T=[[shifted(p,N) for p in row] for row in T]
    deg=max(p.degree() for row in shifted_T for p in row)
    coeff=[[[int(p[k]) for k in range(deg+1)] for p in row] for row in shifted_T]
    lower=[1000*coeff[0][0][k]-sum(abs(coeff[i][0][k]) for i in range(1,10)) for k in range(deg+1)]
    residual=[]
    for j in range(1,10):
        residual.append([lower[k]-1000000*abs(coeff[0][j][k])-1000*sum(abs(coeff[i][j][k]) for i in range(1,10)) for k in range(deg+1)])
    bad=[(j,k) for j,row in enumerate(residual,1) for k,a in enumerate(row) if a<0]
    print(json.dumps({'degree':deg,'N':N,'lower_positive':all(a>0 for a in lower),'negative_cone_coefficients':bad[:15],'negative_count':len(bad)}),flush=True)
    assert all(a>0 for a in lower) and not bad
    contraction=[]
    for j in range(1,10):
        contraction.append([lower[k]-2000*sum(abs(coeff[i][j][k]) for i in range(1,10))
                            -2*sum(abs(coeff[i][0][k]) for i in range(1,10)) for k in range(deg+1)])
    assert all(a>=0 for row in contraction for a in row)
    # The exact weighted limiting connection, without numerical eigenvectors.
    lim=[]
    for i,row in enumerate(ENT):
        lr=[]
        for j,(a,b) in enumerate(row):
            degree=a.degree()-b.degree()+2*j-2*i
            assert degree<=0
            lr.append(Q(a.leading_coefficient(),b.leading_coefficient()) if degree==0 else Q(0))
        lim.append(lr)
    G=Mat(lim).inv();limit_T=-compound(VI*G*V)
    limit_lower=limit_T[0,0]-Q(1,1000)*sum(abs(limit_T[i,0]) for i in range(1,10))
    assert limit_lower>10**9
    char=P([-1,-10336452,-10120051241400,-82488337575256095,-33339376907507494,22235661])
    assert G.charpoly()*22235661 == char
    A_lo,A_hi=Q(1499365229),Q(1499365230)
    B_lo,B_hi=Q(247407884,10**8),Q(247407885,10**8)
    assert char(A_lo)<0<char(A_hi)
    assert char(-B_hi)<0<char(-B_lo)
    from verify_vc_budget import log_interval
    def log_positive(x):
        x=Fraction(str(x)); k=0
        while x>2:x/=2;k+=1
        while x<1:x*=2;k-=1
        a,b=log_interval(x);c,d=log_interval(Fraction(2))
        return (a+k*c,b+k*d) if k>=0 else (a+k*d,b+k*c)
    area_lo=log_positive(A_lo*B_lo)[0]/4
    area_hi=log_positive(A_hi*B_hi)[1]/4
    height_hi=log_positive(A_hi/B_lo)[1]/4
    assert height_hi<Fraction(505562,100000)
    budget_path=M/'verification/vc-budget-2026-09-29/certificate.json'
    budget=json.loads(budget_path.read_text(encoding='utf-8'))
    volume_hi=area_hi+Fraction(budget['arithmetic_rate_signed_upper'])
    assert volume_hi<Fraction(10394861,1000000)
    sys.path.insert(0,str(M/'round6/scripts'))
    from independent_audit import independent_columns
    F=Mat(independent_columns(20)); inv=F.inv()
    E=Mat([[inv[i,j]*20**(2*j) for j in range(5)] for i in (0,4)])*V
    z=[E[0,i]*E[1,j]-E[0,j]*E[1,i] for i,j in PAIRS]
    assert z[0] and all(1000*abs(a)<abs(z[0]) for a in z[1:])
    result={'status':'passed','N':N,'epsilon':'1/1000','degree':deg,
        'common_factor':[str(c) for c in common],
        'det_P_shifted_positive_coefficients':[str(c) for c in shifted(det_P,20)],
        'coordinate_matrix':[[str(V[i,j]) for j in range(5)] for i in range(5)],
        'transformed_numerators':[[[str(c) for c in p] for p in row] for row in T],
        'positive_lower_coefficients':[str(a) for a in lower],
        'cone_residual_coefficients':[[str(a) for a in row] for row in residual],
        'half_contraction_residual_coefficients':[[str(a) for a in row] for row in contraction],
        'limit_matrix':[[str(limit_T[i,j]) for j in range(10)] for i in range(10)],
        'limit_scalar_lower':str(limit_lower),
        'positive_scale_formula':'s(n)=n^14 det(P(n)) d_L d_R/(den(n)^2 common(n) content); P=den*C, den=(n+1)^8(n+2)^10',
        'coordinate_denominators':[str(dl),str(dr)],'content':str(content),
        'eigenvalue_intervals':{'A':[str(A_lo),str(A_hi)],'B':[str(B_lo),str(B_hi)]},
        'area_exponent_interval':[str(area_lo),str(area_hi)],'height_exponent_upper':str(height_hi),
        'updated_volume_upper':str(volume_hi),'budget_sha256':hashlib.sha256(budget_path.read_bytes()).hexdigest(),
        'display':{'area_lower':float(area_lo),'area_upper':float(area_hi),'height_upper':float(height_hi),'updated_volume_upper':float(volume_hi)},
        'initial_exterior_ratios':[str(a/z[0]) for a in z],
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'probe_sha256':hashlib.sha256((M/'scripts/probe_exterior_cone.py').read_bytes()).hexdigest(),
        'connection_sha256':hashlib.sha256((M/'verification/local-connection-2026-09-28/symbolic.json').read_bytes()).hexdigest()}
    out=M/'verification/exterior-cone-2026-09-29';out.mkdir(parents=True,exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS invariant cone for all real n>=20 and actual initial wedge',flush=True)

if __name__=='__main__':main()
