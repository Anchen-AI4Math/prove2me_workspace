"""Bounded exact verification of the unshifted Mellin Hankel frontier.

The all-parameter arguments are in the accompanying note. The exact
runtime is reused from the workspace; this script installs nothing.
"""
from __future__ import annotations
import sys
from pathlib import Path
from math import gcd, lcm
from hashlib import sha256
import json

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT.parents[1] / "tmp/zeta7/exact_packages"))
from flint import fmpq, fmpq_mat


def primes(n):
    return [p for p in range(2, n + 1) if all(p % q for q in range(2, int(p**0.5)+1))]


def largepart(n, cutoff):
    for p in primes(cutoff):
        while n % p == 0:
            n //= p
    return n


def vp(n, p):
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def rank_mod(matrix, p):
    a = [[int(x.numerator) * pow(int(x.denominator), -1, p) % p
          for x in row] for row in matrix]
    rows, cols = len(a), len(a[0])
    rank = 0
    for j in range(cols):
        pivot = next((i for i in range(rank, rows) if a[i][j]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][j], -1, p)
        a[rank] = [x * inv % p for x in a[rank]]
        for i in range(rank + 1, rows):
            c = a[i][j]
            if c:
                a[i] = [(x - c*y) % p for x, y in zip(a[i], a[rank])]
        rank += 1
    return rank


def monic_beta_norm(k, b):
    numerator = fmpq(1)
    denominator = 2*k + b + 10
    for j in range(1, 10):
        numerator *= k+j
        denominator *= k+b+j
    leading = fmpq(1)
    for j in range(1, k+1):
        leading *= (k+b+9+j) / j
    return numerator / denominator / leading**2


def beta_gram(D, b):
    def moment(k):
        answer = fmpq(362880)
        for j in range(10):
            answer /= b+k+1+j
        return answer
    G = fmpq_mat([[moment(i+j) for j in range(D)] for i in range(D)])
    product = fmpq(1)
    for k in range(D):
        product *= monic_beta_norm(k, b)
    assert G.det() == product
    return G, product


def positive_leading_minors(matrix):
    for n in range(1, matrix.nrows()+1):
        assert fmpq_mat([[matrix[i,j] for j in range(n)]
                         for i in range(n)]).det() > 0


def analyze(D, M=0):
    N, cutoff = 2*M, 2*M+2*D
    a = [fmpq(1, (N+n)**9) for n in range(1, 2*D+1)]
    C = fmpq_mat([[a[i+j] - a[i+j+1] for j in range(D)] for i in range(D)])
    b = fmpq_mat([[-a[i]] for i in range(D)])
    dc = C.det()
    cinv = C.inv()
    r = (b.transpose() * cinv * b)[0, 0]
    h = sum((fmpq(1, j**9) for j in range(1, N+1)), fmpq(0))
    q = h+r
    H = [fmpq(0)]
    for n in range(1, cutoff+1):
        H.append(H[-1]+fmpq(1, n**9))
    oldC = fmpq_mat([[H[N+i]+H[N+j]-H[N+i+j]-H[N]
                     for j in range(1,D+1)] for i in range(1,D+1)])
    oldb = fmpq_mat([[H[N]-H[N+i]] for i in range(1,D+1)])
    assert oldC.det() == dc
    assert (oldb.transpose()*oldC.solve(oldb))[0,0] == r

    # The rational square-increment and orthogonality identities.
    n = D-1
    if n:
        previous = fmpq_mat([[C[i,j] for j in range(n)] for i in range(n)])
        u = fmpq_mat([[C[i,n]] for i in range(n)])
        bp = fmpq_mat([[b[i,0]] for i in range(n)])
        coefficients = previous.solve(u)
        dp = previous.det()
        rp = (bp.transpose()*previous.solve(bp))[0,0]
        sigma = C[n,n]-(u.transpose()*coefficients)[0,0]
        t = b[n,0]-(u.transpose()*previous.solve(bp))[0,0]
        polynomial = [-coefficients[i,0] for i in range(n)]+[fmpq(1)]
    else:
        dp, rp, sigma, t = fmpq(1), fmpq(0), C[0,0], b[0,0]
        polynomial = [fmpq(1)]
    xi = -t
    mixed = fmpq_mat([[C[i,j] for j in range(D)] for i in range(n)]
                    +[[a[j] for j in range(D)]]).det()
    norm_tau = sum((polynomial[i]*polynomial[j]*a[i+j]
                    for i in range(D) for j in range(D)), fmpq(0))
    assert norm_tau == sum(polynomial, fmpq(0))*xi > 0
    assert dc == dp*sigma and mixed == dp*xi
    assert r-rp == t*t/sigma == mixed*mixed/(dc*dp) > 0

    # Rectangular minors and the bordered Jacobi identity.
    Ktop = fmpq_mat([[a[i+j] for j in range(D)] for i in range(D)])
    tail = fmpq_mat([[a[D+j]] for j in range(D)])
    dtop = Ktop.det()
    w = Ktop.solve(tail)
    minors = [dtop * w[i, 0] for i in range(D)] + [dtop]
    if D <= 5:
        Krows = [[a[i+j] for j in range(D)] for i in range(D+1)]
        for i in range(D+1):
            direct = fmpq_mat(Krows[:i]+Krows[i+1:]).det()
            assert abs(direct) == abs(minors[i])
    y = cinv*b*dc
    z = r*dc
    border = fmpq_mat([[fmpq(0)]+[b[j,0] for j in range(D)]]
                     +[[b[i,0]]+[C[i,j] for j in range(D)] for i in range(D)])
    assert border.det() == -z
    adjborder = border.inv()*border.det()
    adjC = cinv*dc
    for i in range(D):
        for j in range(D):
            assert y[i,0]*y[j,0]-z*adjC[i,j] == dc*adjborder[i+1,j+1]
            assert largepart(int(adjborder[i+1,j+1].denominator), cutoff) == 1
    common = gcd(*(abs(int(x.numerator)) for x in minors))
    exceptional = largepart(common, cutoff)
    freshdet = largepart(int(dc.numerator), cutoff)
    freshP = largepart(int(q.denominator), cutoff)
    assert freshdet % freshP == 0
    cancelled = freshdet//freshP
    assert exceptional**2 % cancelled == 0
    assert freshdet % exceptional == 0
    assert (freshP*exceptional**2) % freshdet == 0
    assert freshP*exceptional**2 >= freshdet
    if exceptional == 1:
        assert freshdet == freshP
    forced = []
    Krows = [[a[i+j] for j in range(D)] for i in range(D+1)]
    for p in [11,13,17]:
        if p > cutoff and D > p-9:
            rk = rank_mod(Krows,p)
            assert rk <= p-9
            forced_power = D-(p-9)
            assert exceptional % p**forced_power == 0
            forced.append({"p":p,"rank":rk,"valuation_lower":forced_power})

    # Rational beta determinant formulas and strict positive comparisons.
    G0, beta0 = beta_gram(D,fmpq(N))
    Gh, betah = beta_gram(D,fmpq(2*N-1,2))
    lower = G0/fmpq(40320)
    upper = Gh*fmpq(16**8,40320)
    positive_leading_minors(C-lower)
    positive_leading_minors(upper-C)
    assert beta0/40320**D < dc < betah*fmpq(16**8,40320)**D
    primitive_lower = fmpq(int(q.denominator)*5040)
    for j in range(1,9):
        primitive_lower /= (D+j)*(D+N+j)
    return {
        "D":D,"M":M,"cutoff":cutoff,"P":str(q.denominator),
        "P_digits":len(str(q.denominator)),"q_sha256":sha256(str(q).encode()).hexdigest(),
        "det_C_numerator":str(dc.numerator),"det_C_denominator":str(dc.denominator),
        "F_large_determinant_part":str(freshdet),"F_digits":len(str(freshdet)),
        "J_large_maximal_minor_gcd":str(exceptional),
        "P_large_part":str(freshP),"cancelled_large_part":str(cancelled),
        "exact_large_part_equality":freshdet==freshP,"forced_rank_exceptions":forced,
        "primitive_value_lower_numerator":str(primitive_lower.numerator),
        "primitive_value_lower_denominator":str(primitive_lower.denominator),
        "primitive_value_lower_at_least_one":primitive_lower>=1,
        "square_increment_and_nonvanishing":"PASS",
        "adjugate_and_square_cancellation_bound":"PASS",
        "beta_norm_products_and_positive_comparison":"PASS",
    }


if __name__ == "__main__":
    sys.set_int_max_str_digits(100000)
    unshifted = [analyze(D) for D in range(1,25)]
    shifted = [analyze(D,M) for D in range(1,13) for M in sorted({1,D})]
    counter = next(item for item in shifted if item["D"] == item["M"] == 3)
    K19 = [[fmpq(1,(6+i+j+1)**9) for j in range(3)] for i in range(4)]
    alternating = [pow(n,9,19) for n in range(7,13)]
    assert alternating == [1,18,1,18,1,18]
    assert rank_mod(K19,19) == 1
    assert vp(int(counter["J_large_maximal_minor_gcd"]),19) == 2
    assert vp(int(counter["det_C_numerator"]),19) == 2
    assert vp(int(counter["P"]),19) == 0
    assert int(counter["cancelled_large_part"]) == 19**2
    sources = [Path(__file__),ROOT/"research/mellin-unshifted-frontier-2026-10-01.md"]
    certificate = {
        "result":"PASS","date":"2026-10-01","arithmetic":"exact FLINT fmpq",
        "unshifted_degrees":24,"fixed_or_linear_shifted_cases":len(shifted),
        "scope":"bounded checks; all-parameter proof in note; no denominator asymptotic or Lean",
        "extra_shifted_rank_counterexample":{"M":3,"D":3,"p":19,"rank":1,
                                              "delta":2,"v_p_det_C":2,"v_p_P":0},
        "sources":{str(p.relative_to(ROOT)).replace("\\","/"):sha256(p.read_bytes()).hexdigest()
                   for p in sources},
        "unshifted":unshifted,"shifted":shifted,
    }
    dest = ROOT/"verification/mellin-unshifted-frontier-2026-10-01"
    dest.mkdir(parents=True,exist_ok=True)
    (dest/"certificate.json").write_text(json.dumps(certificate,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:v for k,v in certificate.items()
                      if k not in {"sources","unshifted","shifted"}},indent=2))
    print("D | P digits | large determinant digits | J | equality")
    for row in unshifted:
        print(row["D"],row["P_digits"],row["F_digits"],
              row["J_large_maximal_minor_gcd"],row["exact_large_part_equality"])
