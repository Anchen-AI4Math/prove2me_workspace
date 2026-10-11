"""Exact first jet of the actual rational connection, not a fitted sequence.

Run with python-flint available; the prior round's local package folder is
also supported by its imported polynomial generator. This changes no frozen
round artifact. The output records a rational commutator certificate.
"""
import sys, importlib.util, json
from pathlib import Path
from fractions import Fraction
ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('conn',ROOT/'missions/zeta9/round7/scripts/arithmetic_connection_symbolic.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
from flint import fmpq_poly as P, fmpq_mat as M
n=c.n; ONE=c.ONE; ZERO=c.ZERO
H=[]
for a in range(10):
    left=c.mul(c.mul([-n-1,ONE],c.power([n+1,ONE],10)),c.power([ZERO,n-1,ONE],a))
    right=c.mul(c.mul([2*n+1,ONE],c.power([-ONE,ONE],10)),c.power([n,n+1,ONE],a))
    pol=c.invariant(c.add(left,c.neg(right)))
    assert all(p.degree() <= 11+2*a-2*j for j,p in enumerate(pol))
    H.append(tuple(P([p[11+2*a-2*j-k] if 11+2*a-2*j-k>=0 else 0 for j,p in enumerate(pol)]) for k in range(2)))
def red(p,q):
    for a in range(9,-1,-1):
        h,j=H[a];v=p[5+a]/7; w=(q[5+a]-v*j[5+a])/7
        p-=v*h;q-=w*h+v*j
    assert p.degree()<5 and q.degree()<5
    return p,q
y=P([0,1]); AA=[];BB=[]
for r in range(5):
    AA.append(red(y**(10+r),-10*y**(9+r)))
    p=(y-2)**3*y**r
    q=21*p-18*(y-2)**2*y**r-(r*(y-2)**3*y**(r-1) if r else P([]))
    BB.append(red(p,q))
A0,A1=[M([[a[k][j] for j in range(5)] for a in AA]) for k in range(2)]
B0,B1=[M([[b[k][j] for j in range(5)] for b in BB]) for k in range(2)]
G=A0*B0.inv();G1=A1*B0.inv()-G*B1*B0.inv()+G*M([[4*i if i==j else 0 for j in range(5)] for i in range(5)])
old_certificate=json.loads((ROOT/'missions/zeta9/round7/verification/arithmetic-connection-symbolic.json').read_text())
old_g=old_certificate['homogeneous_limit']['inverse_weighted_limit']
assert G==M([[f'{p}/{q}' for p,q in row] for row in old_g])
R=G1-10*G
def tr(m):return sum(m[i,i] for i in range(5))
power=M([[int(i==j) for j in range(5)] for i in range(5)])
for i in range(5):
    assert tr(power*R)==0
    print(i,tr(power*R),flush=True);power=power*G
print('det',G.det(),flush=True)
system=[]
for i in range(5):
    for j in range(5):
        system.append([(G[i,k] if l==j else 0)-(G[l,j] if i==k else 0) for k in range(5) for l in range(5)]+[R[i,j]])
rr,rank=M(system).rref();assert rank==20
xx=[0]*25
for i in range(rank):
    pivot=next(j for j in range(25) if rr[i,j]);xx[pivot]=rr[i,25]
X=M([xx[i*5:(i+1)*5] for i in range(5)])
assert G*X-X*G==R
print('commutator rank',rank,flush=True)
# Independent determinant first jet from the closed formula for det C(n).
c_det_first=Fraction(2,3)+Fraction(4,3)+sum(Fraction(2*k,7) for k in range(1,7))-18
g_det_first=40-c_det_first
assert c_det_first==-10 and g_det_first==50
assert Fraction(str(tr(G.inv()*G1)))==g_det_first
def pairs(m):return [[str(m[i,j]) for j in range(m.ncols())] for i in range(m.nrows())]
destination=Path(__file__).with_name('cp-stable-modes.json')
destination.write_text(json.dumps({'status':'passed','method':'exact polynomial coefficients at infinity; rational matrix arithmetic','G':pairs(G),'G1':pairs(G1),'R':pairs(R),'X':pairs(X),'commutator_rank':rank,'trace_G_power_R':[0]*5,'determinant_first_jet':{'C':str(c_det_first),'G':str(g_det_first)},'scope':'actual rational connection first jet; does not certify nonzero second-mode connection coefficient'},indent=2),encoding='utf-8')
print('passed: actual first jet, exact commutator, and independent determinant first jet')
