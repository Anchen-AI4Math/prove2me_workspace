"""Independent finite audit: determinant expansion and all saved ball evaluations."""
from pathlib import Path
import sys,json,hashlib,math,itertools
M=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(M/'scripts'))
import probe_positive_hankel as source
from flint import fmpq as Q,fmpq_poly as P,arb,ctx
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def permutation_det(matrix):
    h=len(matrix);ans=P([0])
    for perm in itertools.permutations(range(h)):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(h) for j in range(i+1,h))
        term=P([sign])
        for i,j in enumerate(perm):term*=matrix[i][j]
        ans+=term
    return ans
def direct(s,k,n,r):
    x=P([0,1]);dn=source.D(n);tail=source.D(k)//dn
    entries=[]
    for e in range(2*(k-n)-1):
        num=dn**(r-1)*x**e;q,rem=divmod(num,tail)
        value=P([sum((q[i]*source.moment(s,i) for i in range(len(q))),Q(0))])
        for j in range(n+1,k+1):
            residue=num(-j*j)/tail.derivative()(-j*j)
            harmonic=sum((Q(1,v**s) for v in range(1,j+1)),Q(0))
            value+=residue*P([-j**(s-1)*harmonic-Q(1,s-1)+Q(1,2*j),Q(j**(s-1))])
        entries.append(value)
    return permutation_det([[entries[i+j] for j in range(k-n)] for i in range(k-n)])
def main():
    independent=[]
    for args in [(3,2,0,1),(5,4,0,6),(9,4,1,1),(9,4,1,2),(9,5,2,6)]:
        record=source.construct(*args,False);delta=direct(*args)
        assert P([int(v) for v in record['primitive_integer_coefficients']])==delta*Q(record['positive_multiplier'])
        independent.append(list(args))
    assert source.moment(5,0)==Q(5,12)
    assert source.moment(9,0)==Q(3,4)
    assert source.moment(9,1)==Q(11,8)
    evidence={};gridballs={}
    for name,count in [('certificate.json',24),('grid.json',110)]:
        path=M/'verification/positive-hankel-2026-09-29'/name
        d=json.loads(path.read_text());assert d['script_sha256']==sha(M/'scripts/probe_positive_hankel.py')
        assert len(d['cases'])==count
        keys=[]
        for c in d['cases']:
            keys.append((c['s'],c['K'],c['N'],c['power']))
            coeff=[int(a) for a in c['primitive_integer_coefficients']]
            assert len(coeff)==c['h']+1 and math.gcd(*coeff)==1 and Q(c['positive_multiplier'])>0
            ctx.prec=c['precision_bits']+128
            value=arb(0);z=arb(c['s']).zeta()
            for a in reversed(coeff):value=value*z+a
            assert value>0 and value.rel_accuracy_bits()>80
            assert value.overlaps(arb(c['value_ball']))
            scale=value.log()/(c['K']**2)
            assert scale.overlaps(arb(c['log_value_over_K_squared_ball']))
            if name=='grid.json':
                assert value>1
                gridballs[keys[-1]]=scale
        assert len(set(keys))==count
        if name=='grid.json':
            expected={(9,k,n,r) for k in (16,24) for n in range(0,k,2) for r in ((1,) if n==0 else (1,2,4,6,8,10))}
        else:
            expected={(s,k,3*k//40,r) for s in (5,9) for k in (4,8,12,16,20,24,32,40) for r in ((6,) if s==5 else (6,10))}
        assert set(keys)==expected
        evidence[name]={'sha256':sha(path),'cases':count,'all_values_reevaluated':True}
    for k in (16,24):
        winner=(9,k,k-2,1)
        assert all(gridballs[winner]<ball for key,ball in gridballs.items() if key[1]==k and key!=winner)
    out=M/'verification/positive-hankel-review-2026-09-30';out.mkdir(exist_ok=True)
    data={'status':'passed','independent_permutation_determinants':independent,
        'saved_certificates':evidence,'all_grid_values_greater_than_one':True,
        'grid_minima_strictly_certified_by_balls':True,'script_sha256':sha(Path(__file__)),
        'note_sha256':sha(M/'research/positive-hankel-zeta9-2026-09-29.md'),
        'scope':'Finite polynomial and Arb checks only; positivity proof and asymptotic limits reviewed separately.'}
    (out/'certificate.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))
if __name__=='__main__':main()
