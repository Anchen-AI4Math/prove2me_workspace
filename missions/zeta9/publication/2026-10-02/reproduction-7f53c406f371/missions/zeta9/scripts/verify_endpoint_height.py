"""Exact rho-series bounds, cone rates and five archived primitive adjugate checks."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
import gzip, hashlib, json, math, sys

M = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(M / 'scripts'))
from verify_local_connection import fmpq, fmpq_mat
from verify_vc_budget import log_interval
sys.set_int_max_str_digits(0)


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def log_positive(x):
    x = Q(x); k = 0
    while x > 2:
        x /= 2; k += 1
    while x < 1:
        x *= 2; k -= 1
    a, b = log_interval(x)
    c, d = log_interval(Q(2))
    return (a+k*c, b+k*d) if k >= 0 else (a+k*d, b+k*c)


def pairs_to_matrix(rows):
    return fmpq_mat([[fmpq(int(a), int(b)) for a, b in row] for row in rows])


def gram_area_squared(rows, n):
    gram = [[sum(rows[i,j]*rows[k,j]*n**(4*j) for j in range(5))
             for k in range(2)] for i in range(2)]
    return gram[0][0]*gram[1][1]-gram[0][1]**2


def main():
    count = 1000
    partial = sum((1/(2*Q(j)+Q(4,3))-1/(2*Q(j)+2)
                   for j in range(count)), Q())
    # f decreases: integral_M^infty f <= sum_{j>=M} f(j)
    #                                      <= f(M)+integral_M^infty f.
    l, u = log_interval((2*Q(count)+2)/(2*Q(count)+Q(4,3)))
    first = 1/(2*Q(count)+Q(4,3))-1/(2*Q(count)+2)
    rho_interval = (Q(19,2)+partial+l/2,
                    Q(19,2)+partial+u/2+first)
    assert rho_interval[1] < Q(9871,1000)

    cone_path = M/'verification/exterior-cone-2026-09-29/certificate.json'
    cone = json.loads(cone_path.read_text())
    assert cone['status'] == 'passed'
    assert cone['script_sha256'] == digest(M/'scripts/verify_exterior_cone.py')
    A0,A1 = map(Q, cone['eigenvalue_intervals']['A'])
    B0,B1 = map(Q, cone['eigenvalue_intervals']['B'])
    alpha = (log_positive(A0)[0]/2, log_positive(A1)[1]/2)
    beta = (log_positive(B0)[0]/2, log_positive(B1)[1]/2)
    gamma = (log_positive(A0*B0)[0]/4, log_positive(A1*B1)[1]/4)
    delta = (log_positive(A0/B1)[0]/4, log_positive(A1/B0)[1]/4)
    assert list(map(Q, cone['area_exponent_interval'])) == list(gamma)
    assert Q(cone['height_exponent_upper']) == delta[1]
    assert delta[1] < Q(505562,100000)
    bounds = {
        'rho': rho_interval,
        'alpha': alpha, 'beta': beta, 'gamma': gamma, 'delta': delta,
        'kappa': tuple(2*x for x in delta),
        'unreduced_endpoint_rate': tuple(rho_interval[i]+alpha[i] for i in (0,1)),
        'sufficient_gcd_rate_rational': tuple(rho_interval[i]+beta[i] for i in (0,1)),
        'sufficient_gcd_rate_FD': tuple(rho_interval[i]+gamma[i] for i in (0,1)),
        'unreduced_ellipse_center_rate': tuple(2*(rho_interval[i]+alpha[i]) for i in (0,1)),
    }
    assert bounds['sufficient_gcd_rate_rational'][1] < Q(10323444,10**6)
    assert bounds['sufficient_gcd_rate_FD'][1] < Q(15379054,10**6)

    archived = []
    for n in (12,24,48,96,192):
        path = M/f'round6/verification/search-input-n{n}.json.gz'
        with gzip.open(path,'rt',encoding='utf-8') as f:
            data = json.load(f)
        F = pairs_to_matrix(data['raw_monomial_vectors'])
        inv = F.inv()
        E = fmpq_mat([[inv[i,j] for j in range(5)] for i in (0,4)])
        K = fmpq_mat([[int(x) for x in row] for row in data['integer_W_basis_K_rows']])
        D,s1,s2 = (int(data[k]) for k in ('common_denominator_Q','SNF_s1','SNF_s2'))
        c,rho,N = fmpq(s1,D),fmpq(s2,D),s2//s1
        assert s2%s1 == 0
        C = rho*E
        assert all(x.denominator == 1 for x in C.entries())
        assert math.gcd(*(int(x) for x in C.entries())) == 1
        assert math.gcd(*(abs(int(K[0,i]*K[1,j]-K[0,j]*K[1,i]))
                          for i,j in combinations(range(5),2))) == 1
        image = K*fmpq_mat([[F[i,j] for j in (0,4)] for i in range(5)])
        J = fmpq_mat([[int(x) for x in row] for row in data['J_rows_B_A']])
        assert D*image == J
        assert math.gcd(*(int(x) for x in J.entries())) == s1
        assert abs(J.det()) == s1*s2
        Xi2,Delta2 = gram_area_squared(E,n),gram_area_squared(K,n)
        assert Delta2 == c**4*N**2*Xi2
        assert rho**4*Xi2 == N**2*Delta2
        archived.append({'n':n,'input_sha256':digest(path),'rho':str(rho),
                         'content':str(c),'N':str(N),'primitive_rho_E':True,
                         'saturated_K':True,'area_identity':True})
    result = {
        'status':'passed','series_count':count,'partial_sum':str(partial),
        'tail_integral_interval':[str(l/2),str(u/2)],'tail_first_term':str(first),
        'rate_intervals':{k:[str(v[0]),str(v[1])] for k,v in bounds.items()},
        'display':{k:[float(v[0]),float(v[1])] for k,v in bounds.items()},
        'archived_cases':archived,'cone_sha256':digest(cone_path),
        'script_sha256':digest(Path(__file__)),
        'dependencies':{str(p.relative_to(M)):digest(p) for p in
                        (M/'scripts/verify_vc_budget.py', M/'scripts/verify_local_connection.py')},
        'boundary':'Finite rational certificate and five archived matrices; all-n rho proof is in the note. No endpoint gcd lower bound or irrationality claim.',
    }
    out = M/'verification/endpoint-height-after-cone-2026-09-29'
    out.mkdir(exist_ok=True)
    (out/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'passed','rho_upper':float(rho_interval[1]),
                      'archived_cases':len(archived),'rates':result['display']}))


if __name__ == '__main__':
    main()
