"""Exact finite checks of the universal theorem in short-zero-coefficient-nonvanishing.md.

Standard library only. These checks are not a proof for all parameters.
Run from any working directory; outputs stay within this mission.
"""
from fractions import Fraction
import gzip
import hashlib
import json
from math import comb, factorial, gcd
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
MISSION = Path(__file__).resolve().parents[1]
OUT = MISSION / "verification/continuation-2026-09-28"


def coefficients(n, m, r=3, b=7):
    return [comb(n, j)**r * (comb(j+m, m)*comb(n-j+m, m))**b
            for j in range(n+1)]


def operator_coefficients(n, m, r=3, b=7):
    # Start with the Legendre-transformed polynomial, then apply T_n.
    result = [comb(n, j)**2 for j in range(n+1)]
    for _ in range(r-2):
        result = [v*comb(n, j) for j, v in enumerate(result)]
    for _ in range(b):
        for k in range(1, m+1):
            result = [v*(j+k)*(n+k-j) for j, v in enumerate(result)]
        divisor = factorial(m)**2
        assert all(v % divisor == 0 for v in result)
        result = [v//divisor for v in result]
    return result


def alternating(values):
    return sum((-1)**j*v for j, v in enumerate(values))


def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def positive_normalize(p):
    # Remove rational denominators and positive content: signs are unchanged.
    from math import lcm
    d = lcm(*(v.denominator for v in p))
    a = [int(v*d) for v in p]
    g = gcd(*a)
    return [Fraction(v, g) for v in a] if g else [Fraction(0)]


def remainder(p, q):
    p = list(p)
    while len(p) >= len(q) and any(p):
        shift = len(p)-len(q)
        scale = p[-1]/q[-1]
        for j, v in enumerate(q):
            p[shift+j] -= scale*v
        trim(p)
    return p


def variations(signs):
    signs = [s for s in signs if s]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def sign(v):
    return (v > 0)-(v < 0)


def scale_interval(c, box):
    a, b = c*box[0], c*box[1]
    return min(a, b), max(a, b)


def log_interval(q, terms=40):
    """Rational enclosure from log(y)=2*atanh((y-1)/(y+1))."""
    q = Fraction(q)
    assert q > 0
    k = 0
    while q < 1:
        q *= 2
        k -= 1
    while q >= 2:
        q /= 2
        k += 1

    def reduced(y):
        u = (y-1)/(y+1)
        lo = 2*sum((u**(2*j+1)/ (2*j+1) for j in range(terms)), Fraction(0))
        remainder_bound = 2*u**(2*terms+1)/((2*terms+1)*(1-u*u))
        return lo, lo+remainder_bound

    x, y = reduced(q), scale_interval(k, reduced(Fraction(2)))
    return x[0]+y[0], x[1]+y[1]


def sturm_negative_simple(values):
    seq = [positive_normalize(list(map(Fraction, values))),
           positive_normalize([Fraction(j*values[j]) for j in range(1, len(values))])]
    while len(seq[-1]) > 1:
        rem = remainder(seq[-2], seq[-1])
        assert any(rem), "Repeated root: polynomial and derivative have nonconstant gcd"
        seq.append(positive_normalize([-v for v in rem]))
    at_minus_inf = [sign(p[-1])*(-1)**(len(p)-1) for p in seq]
    at_zero = [sign(p[0]) for p in seq]
    count = variations(at_minus_inf)-variations(at_zero)
    assert count == len(values)-1
    return count


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    rows = []
    cases = {(n, m) for n in range(2, 130, 2) for m in range((3*n+1)//14+1)}
    # All six original rational slopes, at larger scales; no zeta evaluation.
    for n in (224, 448, 896):
        cases.update((n, n*a//28) for a in range(7))
    # The combinatorial theorem is valid outside the analytic convergence domain.
    cases.update((n, m) for n in (2, 4, 8, 16) for m in (n, 2*n))
    for n, m in sorted(cases):
        h = coefficients(n, m)
        assert h == h[::-1]
        total = alternating(h)
        assert sign(total) == (-1)**(n//2)
        a = 28*(-1)**m*total
        assert sign(a) == (-1)**(m+n//2)
        lower = 28*factorial(3*n//2)//factorial(n//2)**3 * comb(n//2+m, m)**14
        assert abs(a) >= lower
        assert (abs(a) == lower) == (m == 0)
        if m == 0:
            dixon = (-1)**(n//2)*factorial(3*n//2)//factorial(n//2)**3
            assert total == dixon
        rows.append({"n": n, "m": m, "analytic_domain": 14*m <= 3*n+1,
                     "A": str(a), "expected_sign": (-1)**(m+n//2),
                     "explicit_absolute_lower_bound": str(lower)})

    operator_count = 0
    odd_count = 0
    for n in range(1, 17):
        for m in range(4):
            for r in (2, 3, 9):
                for b in (0, 1, 7):
                    direct = coefficients(n, m, r, b)
                    assert direct == operator_coefficients(n, m, r, b)
                    assert direct == direct[::-1]
                    v = alternating(direct)
                    if n % 2:
                        assert v == 0
                        assert sum((-1)**(j-1)*j*direct[j] for j in range(1,n+1)) != 0
                        odd_count += 1
                    else:
                        assert sign(v) == (-1)**(n//2)
                    operator_count += 1

    sturm_rows = []
    for n in range(2, 13):
        for m in (0, 1, 3):
            count = sturm_negative_simple(coefficients(n, m))
            sturm_rows.append({"n": n, "m": m, "simple_negative_roots": count})

    archives = []
    results = MISSION / "verification/linear-results.jsonl"
    for line in results.read_text(encoding="utf-8").splitlines():
        record = json.loads(line)
        artifact = MISSION.parents[1] / record["artifact_path"]
        assert hashlib.sha256(artifact.read_bytes()).hexdigest() == record["artifact_sha256"]
        with gzip.open(artifact, "rt", encoding="utf-8") as f:
            data = json.load(f)
        n, m = data["n"], data["m"]
        assert data["s"] == 9
        a = 28*(-1)**m*alternating(coefficients(n, m))
        num, den = map(int, data["A_zeta_rational"])
        assert Fraction(num, den) == a
        archives.append({"case_id": record["case_id"], "A_matches": True,
                         "artifact_sha256": record["artifact_sha256"]})

    assert log_interval(1) == (0, 0)
    log2 = log_interval(2)
    assert Fraction("0.693147") < log2[0] < log2[1] < Fraction("0.693148")
    analytic_path = MISSION / "verification/analytic-vertical-bound.json"
    analytic = json.loads(analytic_path.read_text(encoding="utf-8"))
    rates = []
    for row in analytic["rows"]:
        alpha = Fraction(row["alpha"])
        half = Fraction(1, 2)
        pieces = [scale_interval(Fraction(3, 2), log_interval(3)),
                  scale_interval(14*(half+alpha), log_interval(half+alpha)),
                  scale_interval(-14*half, log_interval(half)),
                  scale_interval(-14*alpha, log_interval(alpha))]
        beta_lo = sum(p[0] for p in pieces)
        beta_hi = sum(p[1] for p in pieces)
        margin = beta_lo-Fraction(row["H_global_strict_upper"])
        safe_rate = Fraction((margin*10**6).__floor__(), 10**6)
        assert 0 < safe_rate < margin
        rates.append({"alpha": row["alpha"], "beta_lower": str(beta_lo),
                      "beta_upper": str(beta_hi), "H_upper": row["H_global_strict_upper"],
                      "eventual_error_decay_rate": str(safe_rate),
                      "display_rate": f"{float(safe_rate):.6f}"})

    evidence = {"date": "2026-09-28", "universal_proof": "research/short-zero-coefficient-nonvanishing.md",
                "scope": "finite exact checks only; universal result is a written proof, not Lean checked",
                "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "even_coefficient_cases": rows, "operator_checks": operator_count,
                "odd_zero_and_simple_derivative_controls": odd_count,
                "sturm_checks": sturm_rows, "archived_coefficients": archives,
                "rational_approximation_rates": rates,
                "inherited_analytic_certificate_sha256": hashlib.sha256(analytic_path.read_bytes()).hexdigest(),
                "rate_boundary": "Combines new coefficient lower bound with inherited analytic upper bound; does not certify nonzero error or small integer forms.",
                "irrationality_proved": False}
    path = OUT / "coefficient-nonvanishing.json"
    path.write_text(json.dumps(evidence, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"even_cases": len(rows), "operator_checks": operator_count,
                      "odd_controls": odd_count, "exact_sturm_checks": len(sturm_rows),
                      "archive_matches": len(archives), "all_passed": True,
                      "rational_approximation_rates": [{"alpha": r["alpha"], "c": r["display_rate"]} for r in rates],
                      "output": str(path)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
