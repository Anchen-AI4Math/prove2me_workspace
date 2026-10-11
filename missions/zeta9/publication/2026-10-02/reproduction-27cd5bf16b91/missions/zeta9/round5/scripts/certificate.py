"""Independent finite arithmetic and telescoper audit for zeta(9), round 5.

Standard library only. Reads frozen exact archives but never modifies them.
Theorems, including all small primes, are proved in ../research/arithmetic.md.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
BASE = Path(__file__).resolve().parents[1]
OUT = BASE / 'verification'


def primes_upto(n):
    sieve = bytearray(b'\x01') * (n + 1)
    if n >= 0:
        sieve[0] = 0
    if n >= 1:
        sieve[1] = 0
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p::p] = b'\x00' * ((n - p*p)//p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def vp_factorial(n, ell):
    result = 0
    while n:
        n //= ell
        result += n
    return result


def vp_binomial(n, k, ell):
    return vp_factorial(n, ell)-vp_factorial(k, ell)-vp_factorial(n-k, ell)


def lcm_exponent(n, ell):
    a = 0
    while n >= ell:
        n //= ell
        a += 1
    return a


def integer_lcm(n):
    return math.prod(ell**lcm_exponent(n, ell) for ell in primes_upto(n))


def top_residues(p, n, layers):
    return [(-1)**(p*j + sum(m*b for m,b in layers)) * math.comb(n,j)**p
            * math.prod((math.comb(j+m,m)*math.comb(n-j+m,m))**b for m,b in layers)
            for j in range(n+1)]


def finite_certificate(p, n, layers):
    """Return exact prime exponents and strongest proved combined multiplier.

    layers=[(m,q),...]. A certificate holds for every integer W for which
    2*sum(m*q)+2*deg(W) <= p*(n+1)-2.
    """
    layers = [(int(m),int(b)) for m,b in layers]
    if p not in (3,5,7,9) or n < 2 or n % 2 or any(m<0 or b<1 for m,b in layers):
        raise ValueError('Invalid odd-pole/even-n/layer parameters')
    M = max((m for m,b in layers), default=0)
    short = 4*M <= n
    simple = len(layers)==1 and layers[0][0]<=n and p>=2*layers[0][1]
    local, G, multiplier = [], 1, Q(1)
    for ell in primes_upto(n+M):
        g = min(p*vp_binomial(n,j,ell) + sum(b*(vp_binomial(j+m,m,ell)
                    +vp_binomial(n-j+m,m,ell)) for m,b in layers)
                for j in range(n+1))
        en, em = lcm_exponent(n,ell), lcm_exponent(n+M,ell)
        choices = {'split': (p-1)*em+(10-p)*en-g}
        if short:
            choices['short'] = 9*en-g
        if simple:
            choices['simple'] = 9*en
        best = min(choices.values())
        multiplier *= Q(ell**best) if best>=0 else Q(1,ell**(-best))
        G *= ell**g
        local.append({'prime':ell,'v_G':g,'v_lcm_n':en,
                      'v_lcm_n_plus_M':em,'certificates':choices,'combined':best})
    assert G == math.gcd(*top_residues(p,n,layers))
    return {'p':p,'n':n,'layers':layers,'short_applicable':short,
            'simple_applicable':simple,'G':G,'prime_factors':local,
            'multiplier':multiplier,'max_W_degree':(p*(n+1)-2-2*sum(m*b for m,b in layers))//2}


def trim(p):
    p = list(p)
    while len(p)>1 and not p[-1]:
        p.pop()
    return p


def add(a,b,scale=1):
    z = list(a)+[0]*max(0,len(b)-len(a))
    for i,x in enumerate(b):
        z[i] += scale*x
    return trim(z)


def mul(a,b):
    z = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            z[i+j] += x*y
    return trim(z)


def power(a,k):
    z = [1]
    for _ in range(k):
        z = mul(z,a)
    return z


def telescoper(n,a):
    """Integer coefficients in u of A(t)v(t)^a-B(t)v(t+1)^a."""
    A = mul([-n-1,1],power([n,1],10))
    B = [0]*10+[2*n+1,1]
    raw = add(mul(A,power([0,n-1,1],a)),mul(B,power([n,n+1,1],a)),-1)
    original = list(raw)
    coeff = [0]*(len(raw)//2+1)
    while any(raw):
        deg = len(raw)-1
        assert deg%2==0
        k = deg//2
        coeff[k] = raw[-1]
        raw = add(raw,power([0,n,1],k),-raw[-1])
    coeff = trim(coeff)
    assert len(coeff)-1==5+a and coeff[-1]==7*n-2-2*a
    restored = [0]
    for k,c in enumerate(coeff):
        restored = add(restored,power([0,n,1],k),c)
    assert restored==original
    return coeff


def reduce_degree_four(n, W):
    """Integral reduction, retaining the product of all prescribed leading factors."""
    W = list(W)
    R = len(W)-1
    factor = 1
    for a in reversed(range(max(0,R-4))):
        T = telescoper(n,a)
        c = 7*n-2-2*a
        assert c>0
        W = add([c*x for x in W],T,-(W[5+a] if len(W)>5+a else 0))
        factor *= c
    assert len(trim(W))<=5
    return factor, trim(W)


def determinant(rows):
    n = len(rows)
    if not n:
        return 1
    a = [list(map(int,row)) for row in rows]
    sign, last = 1, 1
    for k in range(n-1):
        pivot = next((i for i in range(k,n) if a[i][k]),None)
        if pivot is None:
            return 0
        if pivot!=k:
            a[k],a[pivot] = a[pivot],a[k]
            sign = -sign
        q = a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator = a[i][j]*q-a[i][k]*a[k][j]
                assert numerator%last==0
                a[i][j] = numerator//last
            a[i][k] = 0
        last = q
    return sign*a[-1][-1]


def rank(rows):
    a = [[Q(x) for x in row] for row in rows]
    if not a:
        return 0
    r = 0
    for c in range(len(a[0])):
        i = next((i for i in range(r,len(a)) if a[i][c]),None)
        if i is None:
            continue
        a[r],a[i] = a[i],a[r]
        pivot = a[r][c]
        a[r] = [x/pivot for x in a[r]]
        for j in range(r+1,len(a)):
            factor = a[j][c]
            a[j] = [x-factor*y for x,y in zip(a[j],a[r])]
        r += 1
        if r==len(a):
            break
    return r


def product(a,b):
    if not a:
        return []
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]


def saturation_index(rows, columns):
    k = len(rows)
    if not k:
        return 1
    result = 0
    for cols in itertools.combinations(range(columns),k):
        result = math.gcd(result,determinant([[row[j] for j in cols] for row in rows]))
    return result


def fq(pair):
    return Q(int(pair[0]),int(pair[1]))


def primitive_multiplier(vector):
    denominator = math.lcm(*(x.denominator for x in vector))
    content = math.gcd(*(int(denominator*x) for x in vector))
    if not content:
        return None
    return Q(denominator,content)


def logq(q):
    return math.log(q.numerator)-math.log(q.denominator)


def audit_archive(path):
    with gzip.open(path,'rt',encoding='utf-8') as handle:
        data = json.load(handle)
    p,n,m,R = (int(data[key]) for key in ('p','n','m','R'))
    cert = finite_certificate(p,n,[(m,10-p)])
    assert R<=cert['max_W_degree']
    vectors = [[fq(x) for x in row] for row in data['raw_monomial_vectors']]
    poles = [[[fq(x) for x in row] for row in block]
             for block in data['monomial_pole_coefficients_r_by_j_by_s1_to_p']]
    T,G,E,D = cert['multiplier'],cert['G'],integer_lcm(n),integer_lcm(n+m)
    local_checks = 0
    for block in poles:
        for row in block:
            for s,c in enumerate(row,1):
                assert (Q(D**(p-s),G)*c).denominator==1
                if cert['short_applicable']:
                    assert (Q(E**(p-s),G)*c).denominator==1
                if cert['simple_applicable']:
                    assert (E**(p-s)*c).denominator==1
                local_checks += 1
    assert all((T*x).denominator==1 for row in vectors for x in row)
    ranks = {}
    for which,key in [('low','lower_integer_matrix'),('full','full_integer_matrix')]:
        original = [list(map(int,row)) for row in data[key]]
        info = data[which+'_hnf']
        trans = [list(map(int,row)) for row in info['T']]
        hnf = [list(map(int,row)) for row in info['H']]
        basis = [list(map(int,row)) for row in info['basis']]
        assert abs(determinant(trans))==1
        assert product(trans,list(map(list,zip(*original))))==hnf
        zero = [i for i,row in enumerate(hnf) if not any(row)]
        assert basis==[trans[i] for i in zero]
        assert rank(original)==int(info['rank'])==rank(hnf)
        assert rank(basis)==len(basis)==R+1-rank(original)
        assert all(not sum(x*y for x,y in zip(row,w)) for row in original for w in basis)
        assert saturation_index(basis,R+1)==1
        ranks[which] = rank(original)
    image = data['image_lattice']
    igr = [list(map(int,row)) for row in image['image_generator_rows']]
    iu = [list(map(int,row)) for row in image['image_U']]
    ih = [list(map(int,row)) for row in image['image_H']]
    assert abs(determinant(iu))==1 and product(iu,igr)==ih
    common = int(image['image_common_denominator'])
    for row,w in zip(ih,image['image_preimages']):
        w = list(map(int,w))
        mapped = [sum(w[j]*vectors[j][k] for j in range(R+1)) for k in (0,len(vectors[0])-1)]
        assert [common*x for x in mapped]==row
    telescope = None
    if p==9 and m==n:
        ts = [telescoper(n,a)+[0]*(R-5-a) for a in range(max(0,R-4))]
        assert all(sum(w[j]*vectors[j][k] for j in range(R+1))==0
                   for w in ts for k in range(len(vectors[0])))
        assert rank(ts)==R+1-ranks['full']
        if R>=4:
            assert ranks=={'low':3,'full':5}
        telescope = {'explicit_basis':ts,'saturation_index':saturation_index(ts,R+1),
                     'full_kernel_dimension':len(ts)}
    gaps = []
    for entry in data['candidate_search']['selected']:
        w = list(map(int,entry['w']))
        raw = [sum(w[j]*vectors[j][k] for j in range(R+1)) for k in range(len(vectors[0]))]
        assert raw==[fq(x) for x in entry['raw_vector']]
        assert not any(raw[1:-1]) and raw[-1]
        M = primitive_multiplier([raw[-1],raw[0]])
        assert M==fq(entry['normalized']['multiplier'])
        ratio = T/M
        assert ratio.denominator==1
        if p==9 and m==n:
            factor,V = reduce_degree_four(n,w)
            imageV = [sum(V[j]*vectors[j][k] for j in range(len(V))) for k in range(len(vectors[0]))]
            assert imageV==[factor*x for x in raw]
        gaps.append({'primitive_multiplier':M,'combined_certificate_gap':ratio.numerator,
                     'log_primitive_per_n':logq(M)/n,
                     'log_combined_gap_per_n':logq(ratio)/n,
                     'log_dn9_gap_per_n':logq(Q(E**9)/M)/n if cert['simple_applicable'] else None})
    return {'case_id':data['case_id'],'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'status':'passed','local_pole_checks':local_checks,'certificate':cert,
            'ranks':ranks,'image_rank':rank(igr),'telescopers':telescope,
            'candidate_gaps':gaps}


def audit_height_barrier(path):
    """Read-only independent verification: no Gauss-reduction algorithm is rerun."""
    data = json.loads(path.read_text(encoding='utf-8'))
    checks = []
    for row in data['checks']:
        b0 = [list(map(int,r)) for r in row['saturated_kernel_basis']]
        b = [list(map(int,r)) for r in row['gauss_basis']]
        trans = [list(map(int,r)) for r in row['unimodular_transform']]
        assert abs(determinant(trans))==1 and product(trans,b0)==b
        assert saturation_index(b0,len(b0[0]))==1
        aa = sum(x*x for x in b[0])
        bb = sum(x*y for x,y in zip(*b))
        cc = sum(x*x for x in b[1])
        det = aa*cc-bb*bb
        assert [aa,bb,cc]==list(map(int,row['gram'])) and det>0
        height = int(row['initial_L1'])
        bounds = [math.isqrt((height*height*v)//det) for v in (cc,aa)]
        assert bounds==row['exhaustive_rectangle']
        best = min(sum(abs(x*a+y*c) for a,c in zip(*b))
                   for x in range(-bounds[0],bounds[0]+1)
                   for y in range(-bounds[1],bounds[1]+1) if x or y)
        assert best==int(row['exact_minimum_nonzero_W_L1'])<=height
        checks.append({'n':row['n'],'minimum_L1':best,'rectangle':bounds,'status':'passed',
                       'scope':'finite minimum only; no asymptotic inference'})
    return {'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'checks':checks}


def short_zero_self_test():
    """Small exact product checks, including numerator exponent 1 and Taylor order 8.

    This checks a local lemma; it does not search for small linear forms.
    """
    cases = [(9,4,[(1,1)]),(9,8,[(2,1)]),(7,8,[(2,1)]),
             (3,4,[(0,7),(0,4)])]
    cases += [(3,12,[(2,7),(1,e)]) for e in (1,2,4)]
    checks = []
    for p,n,layers in cases:
        cert = finite_certificate(p,n,layers)
        assert cert['short_applicable'] and cert['max_W_degree']>=0
        E,G = integer_lcm(n),cert['G']
        tops = top_residues(p,n,layers)
        poles = []
        for j,C in enumerate(tops):
            series = [Q(1)]+[Q(0)]*(p-1)
            factors = []
            for m,b in layers:
                factors += [(-j-k,b) for k in range(1,m+1)]
                factors += [(n-j+k,b) for k in range(1,m+1)]
            factors += [(i-j,-p) for i in range(n+1) if i!=j]
            for distance, exponent in factors:
                factor = [Q((math.comb(exponent,h) if h<=exponent else 0),distance**h)
                          if exponent>=0 else Q((-1)**h*math.comb(-exponent+h-1,h),distance**h)
                          for h in range(p)]
                series = [sum(series[k]*factor[h-k] for k in range(h+1)) for h in range(p)]
            row = [C*series[p-s] for s in range(1,p+1)]
            assert all((Q(E**(p-s),G)*c).denominator==1 for s,c in enumerate(row,1))
            poles.append(row)
        d = 9-p
        rho = [sum(row[s-1] for row in poles) for s in range(1,p+1)]
        assert rho[0]==0 and all(rho[s-1]==0 for s in range(2,p+1,2))
        constant = -sum(math.comb(d+s-1,d)*poles[j][s-1]
                        *sum((Q(1,k**(d+s)) for k in range(1,j+1)),Q(0))
                        for j in range(n+1) for s in range(1,p+1))
        full = [constant]+[math.comb(d+s-1,d)*rho[s-1] for s in range(3,p+1,2)]
        assert all((Q(E**9,G)*v).denominator==1 for v in full)
        checks.append({'p':p,'n':n,'layers':layers,'status':'passed',
                       'local_coefficients':p*(n+1),'G':G})
    return checks


def encode(x):
    if isinstance(x,Q):
        return [str(x.numerator),str(x.denominator)]
    if isinstance(x,dict):
        return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):
        return [encode(v) for v in x]
    if isinstance(x,int) and not isinstance(x,bool) and abs(x)>2**53:
        return str(x)
    return x


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit',action='store_true')
    parser.add_argument('--n',type=int)
    parser.add_argument('--p',type=int,default=3)
    parser.add_argument('--layers',help='JSON list [[m,q],...]')
    args = parser.parse_args()
    if args.audit:
        rows = [audit_archive(path) for path in sorted(OUT.glob('weighted-*.json.gz'))]
        report = {'status':'passed','scope':'finite exact certificates and identities; not irrationality',
                  'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  'archives':rows,'height_barrier':audit_height_barrier(OUT/'independent-height-barrier.json'),
                  'short_zero_self_tests':short_zero_self_test()}
        (OUT/'arithmetic-audit.json').write_text(json.dumps(encode(report),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
        print(json.dumps({'status':'passed','archives':len(rows),
                          'local_pole_checks':sum(r['local_pole_checks'] for r in rows),
                          'telescoper_indices':{r['case_id']:r['telescopers']['saturation_index'] for r in rows if r['telescopers']},
                          'height_barrier':report['height_barrier']['checks']},default=str))
    else:
        if args.n is None or args.layers is None:
            parser.error('Use --audit or provide --n, --p, --layers')
        print(json.dumps(encode(finite_certificate(args.p,args.n,json.loads(args.layers))),ensure_ascii=False))


if __name__=='__main__':
    main()
