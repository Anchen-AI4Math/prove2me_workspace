"""Exact countercheck of Anand, Zenodo 22920911 v1, equations 59--73/Table 5.

This checks the manuscript's formulas, not the claimed local estimates themselves.
No network or third-party dependencies are required.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/zenodo-route-audit-2026-09-29'
A, L = F(3, 40), F(37, 40)
LO, HI = F(1, 3), 2*L

class PL:
    def __init__(self, pieces):
        self.pieces = pieces  # tuples (left, right, slope, intercept)
    def at(self, x):
        for lo, hi, a, b in self.pieces:
            if lo <= x <= hi:
                return a*x+b
        raise ValueError(x)
    def line(self, x):
        for lo, hi, a, b in self.pieces:
            if lo < x < hi:
                return a,b
        raise ValueError(x)
    def binary(self, other, mode):
        if not isinstance(other, PL): other = const(other)
        cuts = sorted({x for p in self.pieces+other.pieces for x in p[:2]})
        ans=[]
        for lo,hi in zip(cuts,cuts[1:]):
            a,b=self.line((lo+hi)/2); c,d=other.line((lo+hi)/2)
            if mode=='add': ans.append((lo,hi,a+c,b+d)); continue
            sub=[lo,hi]
            if a!=c and lo < (d-b)/(a-c) < hi: sub.insert(1,(d-b)/(a-c))
            for u,v in zip(sub,sub[1:]):
                first=(a*(u+v)/2+b <= c*(u+v)/2+d)
                if mode=='max': first=not first
                ans.append((u,v,a if first else c,b if first else d))
        return PL(ans)
    def __add__(self,o):return self.binary(o,'add')
    __radd__=__add__
    def __neg__(self):return self.scale(-1)
    def __sub__(self,o):return self+(-o if isinstance(o,PL) else -F(o))
    def __rsub__(self,o):return -self+o
    def scale(self,c):return PL([(l,h,a*c,b*c) for l,h,a,b in self.pieces])
    def minimum(self,o):return self.binary(o,'min')
    def maximum(self,o):return self.binary(o,'max')
    def integral(self):return sum(a*(h*h-l*l)/2+b*(h-l) for l,h,a,b in self.pieces)

def const(c):return PL([(LO,HI,F(0),F(c))])
Y=PL([(LO,HI,F(1),F(0))])
def splice(items):
    return PL([(max(lo,a),min(hi,b),s,c) for a,b,p in items
               for lo,hi,s,c in p.pieces if max(lo,a)<min(hi,b)])

def main():
    # Limit of -gamma_out/K directly from (54),(58),(59), with gamma=0 for p>K.
    rank=(1+6*A-Y.scale(3)).maximum(0).minimum(L)
    u2=(1+A-Y.scale(3)).maximum(0)
    t2=(1-Y.scale(2)).minimum(A)+u2
    r2=(1-Y).scale(9)-16*A-t2.scale(7)+rank.minimum(Y+u2)
    u1=(1+A-Y.scale(2)).maximum(0)
    t1=(1-Y).minimum(A)+u1
    r1=(1-Y).scale(9)-t1.scale(8)+rank.minimum(Y-A+u1)
    R=splice([(LO,F(1,2),r2),(F(1,2),F(1),r1),(F(1),HI,const(0))])
    floor=splice([(LO,F(1,2),const(2)),(F(1,2),F(1),const(1)),(F(1),HI,const(0))])
    scalar=floor.scale(-2*L)+sum(((2*L-Y.scale(j)).maximum(0) for j in range(1,8)),const(0))
    correct=R+scalar
    # Literal (71)--(73) subtract the rank correction a second time.
    d=(1+6*A-Y.scale(3)-(1+2*A-Y.scale(3)).maximum(0)).maximum(0)
    d=d+splice([(LO,F(1,2),const(1)),(F(1,2),HI,const(0))])
    literal=correct-d
    table=[('1/3','37/100','-75/8','8'),('37/100','37/80','-99/8','16'),
           ('37/80','29/60','-569/40','20'),('29/60','1/2','-569/40','20'),
           ('1/2','37/60','-107/10','9'),('37/60','37/40','-251/20','12'),
           ('37/40','77/80','-72/5','14'),('77/80','1','1','-2'),
           ('1','37/20','-239/20','-2')]
    tab=PL([(F(a),F(b),F(s),F(c)) for a,b,c,s in table])
    point=F(3,2)
    assert correct.at(point)==literal.at(point)==F(7,20)
    assert tab.at(point)==-F(299,20)
    assert correct.integral()==F(453803,288000)
    assert tab.integral()==-F(11002997,720000)
    assert literal.integral()>0
    # Even granting other quoted arithmetic contributions, restoring this outer
    # term destroys the advertised negative final upper-bound coefficient.
    tail=F(9928298118277006344769,7535670527041937280000)
    inner=F(120667538150827615739401,708353029541942104320000)
    restored=tail+inner+correct.integral()+F(44,25)
    result={'status':'PASS: exact counterexample to Table 5 / equation 122',
      'source':'https://zenodo.org/records/22920911',
      'source_sha256':hashlib.sha256((OUT/'anand-zeta7.pdf').read_bytes()).hexdigest(),
      'point':str(point),'formula_value':str(correct.at(point)),
      'table_value':str(tab.at(point)),
      'outer_from_local_normalizer':str(correct.integral()),
      'outer_literal_71_73':str(literal.integral()),
      'outer_table':str(tab.integral()),
      'restored_final_upper_bound_coefficient':str(restored),
      'restored_final_upper_bound_decimal':float(restored),
      'pieces_from_local_normalizer':[[str(x) for x in p] for p in correct.pieces],
      'limitations':['Does not prove the actual determinants grow.',
                     'Does not verify all other lemmas or a repaired proof.',
                     'Restored positive upper bound cannot imply claimed decay.']}
    (OUT/'certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='pieces_from_local_normalizer'},indent=2))

if __name__=='__main__':main()
