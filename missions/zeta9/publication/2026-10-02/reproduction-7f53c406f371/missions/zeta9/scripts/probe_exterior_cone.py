"""Exploratory exact rational coordinates for the actual exterior connection."""
from pathlib import Path
import sys,json
from itertools import combinations
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from verify_local_connection import P,fmpq as Q,fmpq_mat as Mat

PAIRS=list(combinations(range(5),2))
NODES=[Q(2008938256613084,10**15),Q(-1609005876644581,10**15),
       Q(-536785038277432,10**15),Q(-320710111055619,10**15),Q(-256722944921166,10**15)]
V=Mat([[x**i for x in NODES] for i in range(5)])
VI=V.inv()
data=json.loads((M/'verification/local-connection-2026-09-28/symbolic.json').read_text())
ENT=[[(P(list(map(int,e['numerator']))),P(list(map(int,e['denominator'])))) for e in row] for row in data['connection']]

def connection(n): return Mat([[Q(a(n),b(n)) for a,b in row] for row in ENT])
def compound(A):return Mat([[A[i,k]*A[j,l]-A[i,l]*A[j,k] for k,l in PAIRS] for i,j in PAIRS])
def exterior(n):
    A=connection(n).inv()
    G=Mat([[A[i,j]*Q((n+2)**(2*j),n**(2*i)) for j in range(5)] for i in range(5)])
    return -compound(VI*G*V)

def main():
    for n in (20,100,200,1000,10000,1000000):
        T=exterior(n); eps=Q(1,2)
        lower=T[0,0]-eps*sum(abs(T[i,0]) for i in range(1,10))
        upper=max(abs(T[0,j])+eps*sum(abs(T[i,j]) for i in range(1,10)) for j in range(1,10))
        print(json.dumps({'n':n,'lower':float(lower),'upper_over_lower':float(upper/lower),
                          'cone':lower>0 and upper<=eps*lower}),flush=True)
    sys.path.insert(0,str(M/'round6/scripts'))
    from independent_audit import independent_columns
    F=Mat(independent_columns(2))
    for n in range(2,202,2):
        if n in (20,100,200):
            inv=F.inv(); E=Mat([[inv[i,j]*n**(2*j) for j in range(5)] for i in (0,4)])*V
            z=[E[0,i]*E[1,j]-E[0,j]*E[1,i] for i,j in PAIRS]
            print(json.dumps({'actual_n':n,'ratios':[float(x/z[0]) for x in z],
                              'cone':all(abs(x)<=abs(z[0])/2 for x in z[1:])}),flush=True)
        if n<200:F=connection(n)*F

if __name__=='__main__':main()
