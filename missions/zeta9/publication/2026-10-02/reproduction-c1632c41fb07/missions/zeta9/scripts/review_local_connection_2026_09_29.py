"""Independent permutation-minor and dual-plane checks for local connection."""
from pathlib import Path
import sys, json, itertools, math, hashlib
M = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(M.parents[1] / 'tmp/zeta7/exact_packages'))
from flint import fmpz_poly as P, fmpq, fmpq_mat

def det(a):
    n = len(a); total = P([])
    for s in itertools.permutations(range(n)):
        v = P([(-1)**sum(s[i] > s[j] for i in range(n) for j in range(i+1,n))])
        for i in range(n): v *= a[i][s[i]]
        total += v
    return total

def vp(a,p):
    a = fmpq(a)
    if not a: return 10**9
    def vi(x):
        x = abs(int(x)); r = 0
        while x % p == 0: x //= p; r += 1
        return r
    return vi(a.numer()) - vi(a.denom())

def run():
    src = M/'verification/local-connection-2026-09-28/symbolic.json'
    d = json.loads(src.read_text()); x = P([0,1]); den = (x+1)**8*(x+2)**10
    nums = []; dens = []; mat = []
    for row in d['connection']:
        ns = [P(list(map(int,e['numerator']))) for e in row]
        ds = [P(list(map(int,e['denominator']))) for e in row]
        vals = []
        for a,b in zip(ns,ds):
            quotient,rem = divmod(den,b); assert not rem; vals.append(a*quotient)
        nums.append(ns); dens.append(ds); mat.append(vals)
    J = 21*x*(3*x+2)*(3*x+4)
    for j in range(1,7): J *= 7*x+2*j
    gcds = [P([1]),(x+1)**4*(x+2)**4,(x+1)**12*(x+2)**12,
            (x+1)**24*(x+2)**24,J*(x+1)**40*(x+2)**41]
    specials = []; count = 0
    for k,g in enumerate(gcds,1):
        spec = {-1:0,-2:0}; gc = P([])
        for I in itertools.combinations(range(5),k):
            for K in itertools.combinations(range(5),k):
                z = det([[mat[i][j] for j in K] for i in I]); q,r = divmod(z,g)
                assert not r; gc = gc.gcd(z); count += 1
                for root in spec: spec[root] = math.gcd(spec[root],int(q(root)))
        assert gc == g
        for root in spec:
            assert str(spec[root]) == d['determinantal_certificates'][k-1]['specialization_gcd'][str(root)]['gcd']
        specials.append(spec)
    assert det(mat) == gcds[-1]
    sys.path.insert(0,str(M/'round6/scripts'))
    from independent_audit import independent_columns
    F = fmpq_mat(independent_columns(2)); checks = 0; boundary = []
    for n in range(2,61,2):
        inverse = F.inv(); E = fmpq_mat([[inverse[i,j] for j in range(5)] for i in (0,4)])
        small = [fmpq_mat([[F[i,j] for j in (1,2,3)] for i in I]).det()
                 for I in itertools.combinations(range(5),3)]
        mixed = [fmpq_mat([[F[i,j] for j in K] for i in I]).det()
                 for I in itertools.combinations(range(5),4) for K in ((0,1,2,3),(1,2,3,4))]
        minors = [E[0,i]*E[1,j]-E[0,j]*E[1,i] for i,j in itertools.combinations(range(5),2)]
        for p in range(2,98):
            if any(p % j == 0 for j in range(2,math.isqrt(p)+1)): continue
            two = min(vp(v,p) for v in minors)-2*min(vp(E[i,j],p) for i in range(2) for j in range(5))
            old = vp(F.det(),p)+min(vp(v,p) for v in small)-2*min(vp(v,p) for v in mixed)
            assert two == old; checks += 1
            if p == n+1 and p > 7: assert two == 1; boundary.append([n,p,two])
        C = fmpq_mat([[fmpq(nums[i][j](n),dens[i][j](n)) for j in range(5)] for i in range(5)])
        F = C*F
    result = {'status':'passed','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
              'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'independent_permutation_minors':count,'specialization_gcd':specials,
              'dual_plane_formula_checks':checks,'boundary_exact_exponent':boundary}
    out = M/'verification/local-connection-review-2026-09-29'; out.mkdir(exist_ok=True)
    (out/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__': run()
