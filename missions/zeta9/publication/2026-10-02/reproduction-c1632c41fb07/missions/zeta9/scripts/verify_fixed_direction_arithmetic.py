"""Finite checks of the parameter-uniform fixed-output arithmetic theorem."""
from pathlib import Path
import hashlib,json,math,sys
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
from verify_local_connection import valuation,prime_list,fmpq
sys.set_int_max_str_digits(0)
OUT=M/'verification/fixed-direction-arithmetic-2026-09-29'


def main():
    source=M/'verification/shape-direction-2026-09-29/certificate.json'
    rows=json.loads(source.read_text())['cases']
    oddpath=M/'verification/odd-anchor-2026-09-29/certificate.json'
    evenpath=M/'verification/even-block-direction-2026-09-29/certificate.json'
    bad={r['m']:int(r['inverse_denominator_lcm']) for r in json.loads(oddpath.read_text())['symbolic']}
    bad.update({r['m']:abs(int(fmpq(r['determinant']).numer()))
                for r in json.loads(evenpath.read_text())['models']})
    primes=prime_list(7*max(r['n'] for r in rows)//2)
    local=[]; fixed=[]; tail=[]
    for row in rows:
        n=row['n'];mat=row['M_rows'];a,b=mat[0];c,d=mat[1]
        h=int(row['N'])//int(row['g'])
        for z in [(0,1),(1,1),(2,3),(1,0)]:
            x,y=z; defect=math.gcd(h,x*d-y*c,-x*b+y*a)
            fixed.append(dict(n=n,z=z,h_over_q=str(defect),q=str(h//defect)))
        for p in primes:
            k=valuation(h,p)
            if k<=0: continue
            depth=min(valuation(b,p),valuation(d,p))
            m,r=divmod(n,p)
            active=(1<=m<=20 and r and p>max(9*(m+1),7*m+9) and bad[m]%p)
            large=p>n
            if active or large:
                assert depth>=1
                assert min(valuation(a,p),valuation(c,p))==0
                # For odd blocks and the late even segment, H is fully diagonal.
                diagonal=large or (active and (m%2 or 7*r>2*p))
                if diagonal: assert depth>=k
                elif active: assert depth>=max(1,k-1)
                for x,y in [(0,1),(1,1),(2,3)]:
                    if y%p:
                        defect=math.gcd(h,x*d-y*c,-x*b+y*a)
                        assert valuation(defect,p)==0
                local.append(dict(n=n,p=p,m=m,r=r,h_v=k,A9_depth=depth,
                                  diagonal=bool(diagonal),large_prime=large))
            # Coarse tail statement, independent of fixed-model invertibility.
            if p<=n and r and p>max(9*(m+1),7*m+9):
                for x,y in [(0,1),(1,1),(2,3)]:
                    if y%p:
                        defect=math.gcd(h,x*d-y*c,-x*b+y*a)
                        v=valuation(defect,p); assert v<=7
                        tail.append(dict(n=n,p=p,z=[x,y],defect_v=v))
    OUT.mkdir(exist_ok=True)
    payload=dict(status='passed',scope='Finite exact checks; uniform proof is in the research note.',
                 sources={str(p.relative_to(M)):hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [source,oddpath,evenpath]},
                 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                 fixed_directions=fixed,local_direction_cases=local,tail_cases=tail)
    (OUT/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps(dict(status='passed',fixed_directions=len(fixed),local_cases=len(local),
                         tail_cases=len(tail),full_diagonal_cases=sum(r['diagonal'] for r in local))))


if __name__=='__main__':main()
