"""Odd-model connection: exact polynomial telescoper, solve and raw PF checks."""
from pathlib import Path
import sys,json,math,hashlib

MISSION=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(MISSION/'round7/scripts'))
from arithmetic_connection_symbolic import P,n,ZERO,ONE,mul,power,add,neg,invariant
sys.path.insert(0,str(MISSION/'round5/scripts'))
from independent_round5 import compose_w,power_linear,mul as tmul,fmpq as Q
from flint import fmpq_poly as QP,fmpq_mat as Mat
sys.path.insert(0,str(MISSION/'scripts'))
from verify_local_connection import determinant,exact,factor

def generators():
    H=[]
    for a in range(10):
        left=mul(mul([-n-1,ONE],power([n+1,ONE],10)),power([ZERO,n-1,ONE],a))
        right=mul(mul([2*n+1,ONE],power([-ONE,ONE],10)),power([n,n+1,ONE],a))
        z=add(mul(left,[n-1,P([2])]),neg(mul(right,[n+1,P([2])])))
        while z and not z[-1]:z.pop()
        quotient=[ZERO]*(len(z)-1)
        for i in reversed(range(1,len(z))):
            q,r=divmod(z[i],P([2]));assert not r
            quotient[i-1]=q;z[i]-=2*q;z[i-1]-=n*q
        assert not any(z)
        h=invariant(quotient)
        assert h[-1]==7*n+17-2*a
        H.append(h)
    D=power([-n-1,ONE],10)
    old=[[ZERO]*r+D for r in range(5)]
    Z=[ONE]
    for a in range(1,4):Z=mul(Z,[-(n+a)*(2*n+a),ONE])
    new=[[((n+1)*(n+2))**7*c for c in mul(Z,power([-n-1,ONE],r))] for r in range(5)]
    return old,new,H

def raw_matrix(nn):
    assert nn>0 and nn%2
    out=[]
    for r in range(5):
        poles={s:[] for s in range(1,10)}
        for j in range(nn+1):
            p=compose_w([0]*r+[1],-j,nn,8)
            p=tmul(p,[Q(nn-2*j),Q(2)],8)
            for shift in list(range(-nn,0))+list(range(nn+1,2*nn+1)):
                p=tmul(p,power_linear(shift-j,1,8),8)
            for i in range(nn+1):
                if i!=j:p=tmul(p,power_linear(i-j,-9,8),8)
            for s in poles:poles[s].append(math.factorial(nn)**7*p[9-s])
        sums={s:sum(c,Q(0)) for s,c in poles.items()}
        assert sums[1]==0 and all(sums[s]==0 for s in (2,4,6,8))
        assert all(poles[s][nn-j]==(-1)**(s+1)*poles[s][j] for s in poles for j in range(nn+1))
        B=Q(0)
        for s,cs in poles.items():
            harm=Q(0)
            for j,c in enumerate(cs):
                if j:harm+=Q(1,j**s)
                B-=c*harm
        out.append([B]+[sums[s] for s in (3,5,7,9)])
    return Mat(out)

def main():
    old,new,H=generators()
    matrix=[[col[i] if i<len(col) else ZERO for col in old+H] for i in range(15)]
    rhs=[[col[i] if i<len(col) else ZERO for col in new] for i in range(15)]
    augmented=[matrix[i]+rhs[i] for i in range(15)]
    previous=ONE;swaps=0
    for k in range(14):
        if not augmented[k][k]:
            j=next(j for j in range(k+1,15) if augmented[j][k])
            augmented[k],augmented[j]=augmented[j],augmented[k];swaps+=1
        pivot=augmented[k][k]
        for i in range(k+1,15):
            for j in range(k+1,20):
                augmented[i][j]=exact(pivot*augmented[i][j]-augmented[i][k]*augmented[k][j],previous)
            augmented[i][k]=ZERO
        previous=pivot
        print('odd polynomial elimination',k+1,flush=True)
    det=augmented[14][14]
    solution=[[ZERO for _ in range(5)] for _ in range(15)]
    for i in reversed(range(15)):
        for r in range(5):
            numerator=det*augmented[i][15+r]-sum((augmented[i][j]*solution[j][r] for j in range(i+1,15)),ZERO)
            solution[i][r]=exact(numerator,augmented[i][i])
    for i in range(15):
        for r in range(5):
            assert sum((matrix[i][j]*solution[j][r] for j in range(15)),ZERO)==det*rhs[i][r]
    old_det=(-1)**swaps*det
    new_det=determinant([[col[i] if i<len(col) else ZERO for col in new+H] for i in range(15)])
    gcd=old_det.gcd(new_det)
    numerator=exact(new_det,gcd);denominator=exact(old_det,gcd)
    if denominator.leading_coefficient()<0:numerator=-numerator;denominator=-denominator
    print('detC numerator',numerator.factor(),flush=True)
    print('detC denominator',denominator.factor(),flush=True)
    det_sign=1 if old_det(1)>0 else -1
    for p in (det_sign*old_det,det_sign*new_det):
        assert p(1)>0 and all(c>=0 for c in p(P([1,1])))
    rows=[];common=ONE
    for r in range(5):
        row=[]
        for j in range(5):
            g=solution[j][r].gcd(det)
            a=exact(solution[j][r],g);b=exact(det,g)
            if b.leading_coefficient()<0:a=-a;b=-b
            row.append({'numerator':[str(c) for c in a],'denominator':[str(c) for c in b]})
            common=exact(common*b,common.gcd(b))
        rows.append(row)
    finite=[]
    for nn in (1,3,5):
        C=Mat([[Q(P(list(map(int,e['numerator'])))(nn),P(list(map(int,e['denominator'])))(nn)) for e in row] for row in rows])
        F=raw_matrix(nn);nextF=raw_matrix(nn+2)
        h=(nn-1)//2
        assert F.det()==Q(16*math.factorial(3*h+2)*math.factorial(7*h+2),math.factorial(h)**10)
        if nn==1:assert F.det()==64
        assert C*F==nextF
        assert C.det()==Q(numerator(nn),denominator(nn))
        finite.append({'n':nn,'det_F':str(F.det()),'det_C':str(C.det()),'full_connection_equal':True})
    # Highest weighted homogeneous part is unchanged.
    h=QP([H[0][i][11-2*i] for i in range(6)])
    assert h==QP([-1,-9,-26,-23,5,7])
    y=QP([0,1])
    A=Mat([[((y**(10+r))%h)[j] for j in range(5)] for r in range(5)])
    B=Mat([[(((y-2)**3*y**r)%h)[j] for j in range(5)] for r in range(5)])
    G=A*B.inv()
    previous=json.loads((MISSION/'roadmap/verification/cp-stable-modes.json').read_text())
    assert G==Mat([[Q(c) for c in row] for row in previous['G']])
    # Weighted limit from the actual solved rational entries, independently.
    lim=[]
    for i,row in enumerate(rows):
        line=[]
        for j,e in enumerate(row):
            a=P(list(map(int,e['numerator'])));b=P(list(map(int,e['denominator'])))
            degree=a.degree()-b.degree()+2*j-2*i
            assert degree<=0
            line.append(Q(a.leading_coefficient(),b.leading_coefficient()) if degree==0 else Q(0))
        lim.append(line)
    assert Mat(lim).inv()==G
    result={'status':'passed','definition':'Ftilde_n rows are formal vectors of n!^7 G_n(t)(2t+n)[t(t+n)]^r',
        'orientation':'Ftilde_(n+2)=Ctilde(n) Ftilde_n, positive odd n',
        'H_leading_coefficient':'7n+17-2a','connection':rows,'common_denominator':factor(common),
        'determinant_numerator':factor(numerator),'determinant_denominator':factor(denominator),
        'determinant_numerator_coefficients':[str(c) for c in numerator],
        'determinant_denominator_coefficients':[str(c) for c in denominator],
        'old_system_determinant':factor(old_det),'new_system_determinant':factor(new_det),
        'both_system_determinants_positive_after_common_sign_for_real_n_ge_1':True,
        'old_system_determinant_coefficients':[str(c) for c in old_det],
        'new_system_determinant_coefficients':[str(c) for c in new_det],
        'H_coefficients':[[[str(c) for c in p] for p in row] for row in H],
        'inverse_weighted_limit':[[str(G[i,j]) for j in range(5)] for i in range(5)],
        'same_limit_as_even_connection':True,'finite_raw_partial_fraction_checks':finite,
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out=MISSION/'verification/odd-model-connection-2026-09-29';out.mkdir(parents=True,exist_ok=True)
    (out/'symbolic.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS odd symbolic connection, all-parameter nonsingular systems, same limit, n=1,3,5 raw PF comparisons.',flush=True)

if __name__=='__main__':main()
