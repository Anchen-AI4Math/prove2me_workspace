"""Exact finite diagnostics for modified square-pole positive Hankel forms."""
from pathlib import Path
import hashlib
import json
import math
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "scripts"))
import verify_local_connection  # noqa: F401: adds the local python-flint path
from flint import arb, ctx, fmpq as Q, fmpq_mat as Mat, fmpq_poly as Poly

sys.set_int_max_str_digits(0)
X = Poly([0, 1])


def moment(s, e):
    return (-1) ** e * Q.bernoulli(2 * e + 2) * Q(
        math.prod(range(2 * e + 3, 2 * e + s + 1)), math.factorial(s - 1)
    )


def construct(case):
    s, poles, h = case["s"], tuple(case["poles"]), case["h"]
    zero_at_origin, shifted_zeros = case["origin_zero"], case["shifted_zeros"]
    assert s >= 3 and s % 2 and h >= 1
    assert poles == tuple(sorted(set(poles))) and poles[0] > 0
    assert zero_at_origin >= 0 and all(b > 0 and r > 0 for b, r in shifted_zeros)
    assert not set(poles).intersection(b for b, _ in shifted_zeros)

    denominator = Poly([1])
    for a in poles:
        denominator *= X + a * a
    derivative = denominator.derivative()
    numerator = X ** zero_at_origin
    for b, r in shifted_zeros:
        numerator *= (X + b * b) ** r
    harmonic = {
        a: sum((Q(1, v**s) for v in range(1, a + 1)), Q(0))
        for a in poles
    }
    entries = []
    residues = {a: numerator(-a * a) / derivative(-a * a) for a in poles}
    assert all(residues.values())
    for k in range(2 * h - 1):
        quotient, remainder = divmod(numerator * X**k, denominator)
        aa = sum((quotient[e] * moment(s, e) for e in range(len(quotient))), Q(0))
        bb = Q(0)
        for a in poles:
            residue = remainder(-a * a) / derivative(-a * a)
            aa += residue * (-a ** (s - 1) * harmonic[a] - Q(1, s - 1) + Q(1, 2 * a))
            bb += residue * a ** (s - 1)
        entries.append((aa, bb))
    A = Mat([[entries[i + j][0] for j in range(h)] for i in range(h)])
    B = Mat([[entries[i + j][1] for j in range(h)] for i in range(h)])
    # Rank is computed exactly. For h >= pole count the Vandermonde factor
    # ensures it equals the pole count. The positive Gram theorem then gives
    # degree = rank(B), even if B is indefinite.
    rank = B.rank()
    if h >= len(poles):
        assert rank == len(poles)
    degree_bound = min(h, len(poles))
    assert rank <= degree_bound
    values = [(A + j * B).det() for j in range(degree_bound + 1)]
    delta = Poly([0])
    for j, value in enumerate(values):
        basis = Poly([1])
        div = 1
        for k in range(degree_bound + 1):
            if j != k:
                basis *= X - k
                div *= j - k
        delta += basis * Q(value, div)
    for t in (-2, -1, degree_bound + 1):
        assert delta(t) == (A + t * B).det()
    assert delta.degree() == rank

    den = math.lcm(*(int(c.denom()) for c in delta))
    coeffs = [int((c * den).numer()) for c in delta]
    content = math.gcd(*coeffs)
    assert content > 0
    coeffs = [c // content for c in coeffs]
    assert math.gcd(*coeffs) == 1
    multiplier = Q(den, content)
    assert Poly(coeffs) == delta * multiplier

    precision = max(512, max(abs(c).bit_length() for c in coeffs) + 256)
    for _ in range(7):
        ctx.prec = precision
        zeta = arb(s).zeta()
        value = arb(0)
        for c in reversed(coeffs):
            value = value * zeta + c
        if value > 0 and value.rel_accuracy_bits() >= 80:
            break
        precision *= 2
    else:
        raise AssertionError("Arb could not certify positive evaluation")
    log_value = value.log()
    return {
        **case,
        "pole_count": len(poles),
        "A_matrix": [[str(A[i, j]) for j in range(h)] for i in range(h)],
        "B_matrix": [[str(B[i, j]) for j in range(h)] for i in range(h)],
        "rank_B": rank,
        "degree": delta.degree(),
        "determinants_at_0_through_degree_bound": [str(v) for v in values],
        "extra_determinant_checks": [-2, -1, degree_bound + 1],
        "rational_determinant_coefficients": [str(c) for c in delta],
        "primitive_integer_coefficients": [str(c) for c in coeffs],
        "minimal_positive_rational_multiplier": str(multiplier),
        "pole_residues": {str(a): str(residues[a]) for a in poles},
        "precision_bits": precision,
        "positive_value_ball": value.str(40),
        "log_positive_value_ball": log_value.str(30),
        "log_positive_value_mid": float(log_value.mid()),
        "normalization_claim": "Every positive rational scalar making the determinant integral is a positive integer multiple of this multiplier.",
    }


def cases():
    def one(s, poles, h, origin=0, shifted=()):
        return {"s": s, "poles": list(poles), "h": h,
                "origin_zero": origin, "shifted_zeros": [list(pair) for pair in shifted]}

    ans = []
    for s in (5, 9):
        # Isolate the rank/degree effect at fixed poles and numerator.
        for h in (2, 3, 4, 5):
            ans.append(one(s, (1, 2, 3), h))
        # Same pole count, different arithmetic scale and spacing.
        for poles in ((2, 3, 4), (1, 3, 5), (4, 5, 6)):
            ans.append(one(s, poles, 4))
        # Contrast zeros at the endpoint with positive shifted zeros.
        for origin, shifted in ((2, ()), (4, ()), (0, ((1, 2),)),
                                (0, ((5, 2),)), (0, ((1, 1), (5, 1)))):
            ans.append(one(s, (2, 3, 4), 4, origin, shifted))
        # The single-pole linear form shows rank stays one as h increases.
        for h in (3, 5):
            ans.append(one(s, (2,), h, shifted=((1, 2),)))
    # Small-pole boundary cases target the near-unit s=9 value in the
    # three-pole, three-dimensional control, without enlarging a K,N grid.
    for poles, h, origin, shifted in (
        ((1, 2), 2, 0, ()), ((1, 2), 3, 0, ()),
        ((1, 3), 2, 0, ()), ((2, 3), 2, 0, ()),
        ((1, 2, 3), 3, 1, ()),
        ((1, 2, 3), 3, 0, ((4, 1),)),
    ):
        ans.append(one(9, poles, h, origin, shifted))
    return ans


def main():
    records = []
    for case in cases():
        record = construct(case)
        records.append(record)
        print(json.dumps({key: record[key] for key in
                          ("s", "poles", "h", "origin_zero", "shifted_zeros",
                           "degree", "log_positive_value_mid")}), flush=True)
    output = HERE / "verification" / "modified-poles-2026-09-30"
    output.mkdir(parents=True, exist_ok=True)
    payload = {
        "status": "passed", "case_count": len(records), "cases": records,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "boundary": "Exact finite coefficients and primitive normalization; no asymptotic decay or irrationality conclusion.",
    }
    (output / "certificate.json").write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
