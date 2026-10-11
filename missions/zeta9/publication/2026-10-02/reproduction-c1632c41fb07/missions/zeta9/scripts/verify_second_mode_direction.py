"""Exact first-order connection and second-mode sign certificates; no zeta floats."""
from pathlib import Path
from fractions import Fraction as F
import sys,json,hashlib

MISSION=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(MISSION/'scripts'))
from probe_exterior_cone import ENT,Q,Mat
from verify_local_connection import determinant,QP

def add(a,b): return (a[0]+b[0],a[1]+b[1])
def mul(a,b):
    q=[a[i]*b[j] for i in range(2) for j in range(2)]
    return (min(q),max(q))
def neg(a): return (-a[1],-a[0])
def point(a): return (F(a),F(a))
def polynomial(roots,shift=0):
    out=[point(1)]
    for root in roots:
        constant=add(point(shift),neg(root));new=[point(0)]*(len(out)+1)
        for i,c in enumerate(out):
            new[i]=add(new[i],mul(c,constant));new[i+1]=add(new[i+1],c)
        out=new
    return out
def sign(a):
    assert a[0]>0 or a[1]<0
    return 1 if a[0]>0 else -1
def pair(a): return [str(a[0]),str(a[1])]

def main():
    # M_n=W_(n+2)^(-1) C(n) W_n=M+M1/n+O(n^-2), G_n=M_n^-1.
    m=[];m1=[]
    for i,row in enumerate(ENT):
        line=[];first=[]
        for j,(a,b) in enumerate(row):
            delta=a.degree()-b.degree()+2*j-2*i
            assert delta<=0
            lead=Q(a.leading_coefficient(),b.leading_coefficient())
            line.append(lead if delta==0 else Q(0))
            if delta==0:
                correction=Q(a[a.degree()-1],a.leading_coefficient())-Q(b[b.degree()-1],b.leading_coefficient())-4*i
                first.append(lead*correction)
            else:first.append(lead if delta==-1 else Q(0))
        m.append(line);m1.append(first)
    G=Mat(m).inv();G1=-G*Mat(m1)*G
    old_path=MISSION/'roadmap/verification/cp-stable-modes.json'
    old=json.loads(old_path.read_text())
    old_G=Mat([[Q(a) for a in row] for row in old['G']])
    old_G1=Mat([[Q(a) for a in row] for row in old['G1']])
    X=Mat([[Q(a) for a in row] for row in old['X']])
    assert G==old_G and G1==old_G1
    assert G1-10*G==G*X-X*G
    base=[[QP([-G[i,j],1 if i==j else 0]) for j in range(5)] for i in range(5)]
    char=determinant(base);derivative=QP([])
    for r in range(5):
        mat=[row[:] for row in base]
        mat[r]=[QP([-G1[r,j]]) for j in range(5)]
        derivative+=determinant(mat)
    x=QP([0,1])
    assert derivative==50*char-10*x*char.derivative()
    # Each row of G is multiplication by phi=y^10/(y-2)^3 modulo h.
    h=QP([-1,-9,-26,-23,5,7]);den=(x-2)**3
    for i in range(5):
        assert not ((QP([G[i,j] for j in range(5)])*den-x**(10+i))%h)
    roots=[(F(2008,1000),F(2009,1000)),(F(-1610,1000),F(-1609,1000)),
           (F(-537,1000),F(-536,1000)),(F(-321,1000),F(-320,1000)),
           (F(-257,1000),F(-256,1000))]
    hc=[-1,-9,-26,-23,5,7]
    evaluate=lambda y:sum(c*y**i for i,c in enumerate(hc))
    assert all(evaluate(a)*evaluate(b)<0 for a,b in roots)
    # Disjoint intervals exhaust all roots of the degree-five h.
    primary=polynomial([r for i,r in enumerate(roots) if i!=0])
    secondary=polynomial([r for i,r in enumerate(roots) if i!=1])
    primary_taylor=polynomial([r for i,r in enumerate(roots) if i!=0],2)
    secondary_taylor=polynomial([r for i,r in enumerate(roots) if i!=1],2)
    assert list(map(sign,primary))==[1]*5
    assert list(map(sign,secondary))==[-1,-1,-1,-1,1]
    assert list(map(sign,primary_taylor))==[1]*5
    assert list(map(sign,secondary_taylor))==[-1,1,1,1,1]
    dot=point(0)
    for a,b in zip(primary,secondary):dot=add(dot,mul(a,b))
    assert F(-6)<dot[0]<dot[1]<F(-59,10)
    secondary_X=[]
    for j in range(5):
        c=point(0)
        for i in range(5):c=add(c,mul(secondary[i],point(F(str(X[i,j])))))
        secondary_X.append(c)
    at_positive=point(0)
    for c in reversed(secondary_X):at_positive=add(mul(at_positive,roots[0]),c)
    derivative_at_positive=point(1)
    for j in (2,3,4):
        derivative_at_positive=mul(derivative_at_positive,add(roots[0],neg(roots[j])))
    assert derivative_at_positive[0]>0
    positive_root_shift=neg(mul(at_positive,(1/derivative_at_positive[1],1/derivative_at_positive[0])))
    assert F(3)<positive_root_shift[0]<positive_root_shift[1]<F(31,10)
    # Identify which spectral root phi(y_i) is: positive dominant,
    # negative modulus >1, remaining negative modulus <1/1000.
    phi=[]
    for a,b in roots:
        power=point(1)
        for _ in range(10):power=mul(power,(a,b))
        denominator=point(1)
        for _ in range(3):denominator=mul(denominator,(a-2,b-2))
        assert denominator[0]*denominator[1]>0
        inv=(F(1,denominator[1]),F(1,denominator[0]))
        phi.append(mul(power,inv))
    assert phi[0][0]>10**9
    assert phi[1][1]<-1
    assert all(-F(1,1000)<a<b<0 for a,b in phi[2:])
    assert all(phi[i][1]<phi[i+1][0] for i in (1,2,3))
    result={'status':'passed','G':[[str(G[i,j]) for j in range(5)] for i in range(5)],
        'G_first_order':[[str(G1[i,j]) for j in range(5)] for i in range(5)],
        'characteristic':[str(c) for c in char],
        'characteristic_first_order':[str(c) for c in derivative],
        'first_order_identity':'q1(X)=50q(X)-10Xq_derivative(X)',
        'all_simple_modes_polynomial_exponent':'5',
        'existing_cp_stable_G_and_G1_match':True,
        'existing_commutator_identity_rechecked':True,
        'quotient_multiplication_identity':'G acts by y^10/(y-2)^3 modulo h',
        'h_coefficients':hc,'root_intervals':list(map(pair,roots)),
        'spectral_phi_intervals':list(map(pair,phi)),
        'primary_monic_coefficients':list(map(pair,primary)),
        'secondary_monic_coefficients':list(map(pair,secondary)),
        'primary_Taylor_at_2':list(map(pair,primary_taylor)),
        'secondary_Taylor_at_2':list(map(pair,secondary_taylor)),
        'monic_primary_secondary_dot_interval':pair(dot),
        'positive_root_first_order_shift_interval':pair(positive_root_shift),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'existing_cp_certificate_sha256':hashlib.sha256(old_path.read_bytes()).hexdigest(),
        'connection_sha256':hashlib.sha256((MISSION/'verification/local-connection-2026-09-28/symbolic.json').read_bytes()).hexdigest()}
    out=MISSION/'verification/second-mode-direction-2026-09-29';out.mkdir(parents=True,exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: first-order modal exponent 5; exact quotient action; five real roots; monomial/Taylor signs; nonzero Euclidean dot product.')
    print('primary-secondary monic dot interval:',pair(dot))

if __name__=='__main__':main()
