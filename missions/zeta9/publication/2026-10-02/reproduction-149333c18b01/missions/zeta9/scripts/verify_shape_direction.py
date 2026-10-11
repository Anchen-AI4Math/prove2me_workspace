"""Exact genuine-kernel and intrinsic-slope diagnostics; finite evidence only."""
from pathlib import Path
import argparse, hashlib, json, math, sys

M = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(M / 'scripts'))
from verify_local_connection import P, fmpq, fmpq_mat, prime_list
from flint import arb, ctx, fmpz, fmpz_mat
sys.path.insert(0, str(M / 'round7/scripts'))
from modulus_scan import gauss, gram, matmul_2
sys.path.insert(0, str(M / 'round6/scripts'))
from independent_audit import independent_columns
sys.set_int_max_str_digits(0)
OUT = M / 'verification/shape-direction-2026-09-29'


def rows(A):
    return [[int(A[i,j]) for j in range(A.ncols())] for i in range(A.nrows())]


def integerize(A):
    d = math.lcm(*(int(A[i,j].denom()) for i in range(A.nrows()) for j in range(A.ncols())))
    return fmpz_mat([[int(d*A[i,j]) for j in range(A.ncols())] for i in range(A.nrows())])


def normalize_content(A):
    vals = rows(A)
    d = math.gcd(*(v for r in vals for v in r))
    return [[v//d for v in r] for r in vals]


def ball(n, terms):
    with ctx.workprec(256):
        value = sum((arb(fmpz(v)).log()*a/b for v,a,b in terms), arb(0))/n
        mid, rad, exp = value.mid_rad_10exp(35)
        return dict(mid=str(mid), rad=str(rad), exp=int(exp), approx=float(value),
                    below_0169=bool(value.upper() < (arb(169)/1000).lower()))


def analyze(n, F, primes):
    low = integerize(fmpq_mat([[F[i,j] for j in (1,2,3)] for i in range(5)]))
    H,T = low.hnf(transform=True)
    assert H == T*low and abs(int(T.det())) == 1
    assert all(H[i,j]==0 for i in (3,4) for j in range(3))
    K = [rows(T)[i] for i in (3,4)]
    weights = [n**(2*r) for r in range(5)]
    H0, G0, _ = gauss(gram(K,weights))
    K = matmul_2(H0,K)
    delta2 = G0[0]*G0[2]-G0[1]**2
    image = fmpq_mat(K)*fmpq_mat([[F[i,j] for j in (0,4)] for i in range(5)])
    intrinsic = normalize_content(integerize(image))
    a,b = intrinsic[0]; c,d = intrinsic[1]
    N = abs(a*d-b*c)
    modulus = math.gcd(N,math.lcm(*range(1,n+1))**2)
    generators = fmpz_mat([[modulus,0],[0,modulus],[d,-b],[-c,a]])
    hermite = rows(generators.hnf())[:2]
    assert abs(int(fmpz_mat(hermite).det())) == modulus
    assert all(v % modulus == 0 for r in matmul_2(hermite,intrinsic) for v in r)
    basis = matmul_2(hermite,K)
    output_basis = [[v//modulus for v in row] for row in matmul_2(hermite,intrinsic)]
    Hg, Gg, _ = gauss(gram(basis,weights))
    coefficients = matmul_2(Hg,hermite)
    x,y = coefficients[0]
    content = math.gcd(x,y)
    primitive = [x//content,y//content]
    output = [sum(primitive[i]*intrinsic[i][j] for i in range(2)) for j in range(2)]
    cost = modulus//math.gcd(modulus,math.gcd(*output))
    assert cost == content
    assert Gg[0]*Gg[2]-Gg[1]**2 == modulus**2*delta2
    local = []
    for p in primes:
        if p>n: break
        if modulus%p: continue
        pe=1; e=0
        while modulus%(pe*p)==0: pe*=p; e+=1
        j = next(j for j in range(2) if any(intrinsic[i][j]%p for i in range(2)))
        column = [intrinsic[i][j]%pe for i in range(2)]
        i = next(i for i in range(2) if column[i]%p)
        column = [(v*pow(column[i],-1,pe))%pe for v in column]
        z = sum(primitive[i]*column[i] for i in range(2)) % pe
        v=0
        while v<e and z%p==0: v+=1; z//=p
        local.append(dict(p=p,e=e,normalized_column=column,primitive_v=v,cost_v=e-v))
    assert math.prod(r['p']**r['cost_v'] for r in local)==cost
    # A, B, delta2 certify the exact interval criterion in the note.
    sigma = ball(n,[(modulus,1,2),(delta2,1,4),(Gg[0],-1,2)])
    return dict(n=n,N=str(N),g=str(modulus),K_rows=K,M_rows=intrinsic,
                base_gram=G0,delta_squared=str(delta2),congruence_basis=hermite,
                output_basis=output_basis,
                reduced_coefficients=coefficients,reduced_gram=Gg,
                primitive_short_direction=primitive,shortest_multiplier=str(cost),
                sigma=sigma,base_sigma=ball(n,[(delta2,1,4),(G0[0],-1,2)]),
                multiplier_rate=ball(n,[(cost,1,1)]),
                direction_height_rate=ball(n,[(max(map(abs,primitive)),1,1)]),
                local_slopes=local)


def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--limit',type=int,default=200)
    parser.add_argument('--reuse',action='store_true')
    args=parser.parse_args(); OUT.mkdir(exist_ok=True)
    source=M/'verification/local-connection-2026-09-28/symbolic.json'
    data=json.loads(source.read_text())
    entries=[[(P(list(map(int,e['numerator']))),P(list(map(int,e['denominator']))))
              for e in row] for row in data['connection']]
    F=fmpq_mat(independent_columns(2)); records=[]; primes=prime_list(args.limit)
    if args.reuse: records=json.loads((OUT/'certificate.json').read_text())['cases']
    for n in ([] if args.reuse else range(2,args.limit+1,2)):
        if n in (12,28): assert F==fmpq_mat(independent_columns(n))
        records.append(analyze(n,F,primes))
        if n%20==0: print(json.dumps({'n':n,'sigma':records[-1]['sigma']['approx']}),flush=True)
        if n<args.limit: F=fmpq_mat([[fmpq(a(n),b(n)) for a,b in row] for row in entries])*F
    transitions=[]
    for left,right in zip(records,records[1:]):
        n=left['n']; assert right['n']==n+2
        C=fmpq_mat([[fmpq(a(n),b(n)) for a,b in row] for row in entries])
        Ci=C.inv()
        a=math.lcm(*(int(C[i,j].denom()) for i in range(5) for j in range(5)))
        b=math.lcm(*(int(Ci[i,j].denom()) for i in range(5) for j in range(5)))
        Q=a*b
        ell=math.lcm(*range(1,n+3))//math.lcm(*range(1,n+1))
        R=Q**2*ell**2; T=Q*R
        L,Lp=(fmpq_mat(r['M_rows']) for r in (left,right))
        for X in (Q*L*Lp.inv(),Q*Lp*L.inv()):
            assert all(X[i,j].denom()==1 for i in range(2) for j in range(2))
        for r in (left,right):
            g=int(r['g'])
            products=matmul_2(r['congruence_basis'],r['M_rows'])
            assert all(v%g==0 for row in products for v in row)
            r['output_basis']=[[v//g for v in row] for row in products]
            assert abs(int(fmpz_mat(r['output_basis']).det()))==int(r['N'])//g
        U,Up=(fmpq_mat(r['output_basis']) for r in (left,right))
        for X in (T*U*Up.inv(),T*Up*U.inv()):
            assert all(X[i,j].denom()==1 for i in range(2) for j in range(2))
        transitions.append(dict(n=n,a=str(a),b=str(b),ell=ell,Q=str(Q),T=str(T)))
    archive=json.loads((M/'round7/verification/modulus-scan.json').read_text())
    for r in records:
        x,y=r['reduced_coefficients'][0]; m=r['M_rows']; g=int(r['g'])
        z=[(x*m[0][j]+y*m[1][j])//g for j in range(2)]
        d=math.gcd(*z); z=[v//d for v in z]
        if z[1]<0 or (z[1]==0 and z[0]<0): z=[-v for v in z]
        r['primitive_short_output']=z
    changes=[a['n'] for a,b in zip(records,records[1:])
             if a['primitive_short_output']!=b['primitive_short_output']]
    by_n={r['n']:r for r in records}; crosschecks=[]
    for old in archive['cases']:
        n=int(old['n'])
        if n not in by_n: continue
        current=by_n[n]; weighted=next(m for m in old['modes'] if m['mode']=='n2r')
        tier=next(t for t in weighted['tiers'] if 'gcd_N_d_n_pow_2' in t['labels'])
        assert int(current['N'])==int(old['N'])
        assert int(current['delta_squared'])==int(weighted['deltaK_squared'])
        assert current['reduced_gram'][0]==int(tier['mu1_squared'])
        crosschecks.append(n)
    payload=dict(status='passed',scope='Finite genuine matrices only; no infinite shape assertion.',
                 connection_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                 dependency_sha256={str(p.relative_to(M)):hashlib.sha256(p.read_bytes()).hexdigest()
                                    for p in [M/'scripts/verify_local_connection.py',
                                              M/'round7/scripts/modulus_scan.py',
                                              M/'round6/scripts/independent_audit.py',
                                              M/'round7/verification/modulus-scan.json']},
                 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                 adjacent_containments=transitions,archived_crosschecks=crosschecks,
                 primitive_output_change_indices=changes,cases=records)
    (OUT/'certificate.json').write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({'cases':len(records),'max_sigma':max(r['sigma']['approx'] for r in records),
                      'not_below_0169':[r['n'] for r in records if not r['sigma']['below_0169']],
                      'nontrivial_multipliers':[r['n'] for r in records if r['shortest_multiplier']!='1']}))


if __name__=='__main__': main()
