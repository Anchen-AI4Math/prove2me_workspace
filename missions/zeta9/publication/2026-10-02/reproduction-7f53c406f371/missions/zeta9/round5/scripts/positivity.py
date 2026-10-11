"""Exact Sturm half-ray audit for archived p=9 invariant-polynomial W.

If W has no zero in (u0,+infinity), W has one strict sign at every
effective lattice point except possibly the first one.  Since R_n(k)>0
for k>n, this proves the archived raw L_n(W) is nonzero.  This is a
finite-case certificate, never a uniform statement over all even n.
"""

from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tmp/zeta7/exact_packages"))
from flint import fmpq_poly  # type: ignore

VERIFY = ROOT / "missions/zeta9/round5/verification"


def sign(x) -> int:
    return (x > 0) - (x < 0)


def right_sign(poly: fmpq_poly, a: int) -> int:
    """Exact sign at a+epsilon for sufficiently small epsilon>0."""
    f = poly
    while not f.is_zero():
        value = f(a)
        if value:
            return sign(value)
        f = f.derivative()
    return 0


def variations(signs: list[int]) -> int:
    signs = [s for s in signs if s]
    return sum(signs[i] != signs[i + 1] for i in range(len(signs) - 1))


def sturm_open_ray(coefficients: list[int], a: int) -> dict:
    f = fmpq_poly(coefficients)
    if f.is_zero():
        raise ValueError("W is the zero polynomial")
    seq = [f]
    if f.degree() > 0:
        seq.append(f.derivative())
        while not seq[-1].is_zero():
            remainder = seq[-2] % seq[-1]
            if remainder.is_zero():
                break
            seq.append(-remainder)
    sr = [right_sign(g, a) for g in seq]
    si = [sign(g.leading_coefficient()) for g in seq]
    vr, vi = variations(sr), variations(si)
    count = vr - vi
    if count < 0 or count > f.degree():
        raise AssertionError(f"invalid Sturm root count: {count}")
    return {
        "degree": f.degree(),
        "u0": a,
        "endpoint_sign": sign(f(a)),
        "right_sign": right_sign(f, a),
        "infinity_sign": sign(f.leading_coefficient()),
        "sturm_length": len(seq),
        "variations_right": vr,
        "variations_infinity": vi,
        "distinct_roots_open_ray": count,
        "raw_L_sign_if_certified": (
            sign(f.leading_coefficient()) if count == 0 else None
        ),
    }


def audit_file(path: Path) -> list[dict]:
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        archive = json.load(stream)
    if int(archive["p"]) != 9 or int(archive["m"]) != int(archive["n"]):
        raise AssertionError("wrong archive")
    n = int(archive["n"])
    exponents = [int(x) for x in archive["W_basis_exponents"]]
    u0 = (n + 1) * (2 * n + 1)
    rows = []
    for ix, item in enumerate(archive["candidate_search"]["selected"]):
        weights = [int(x) for x in item["w"]]
        if len(weights) != len(exponents):
            raise AssertionError("coefficient dimension")
        hash_value = hashlib.sha256(
            ",".join(map(str, weights)).encode()
        ).hexdigest()
        if hash_value != item["W_sha256"]:
            raise AssertionError("W hash mismatch")
        coeffs = [0] * (max(exponents) + 1)
        for exponent, weight in zip(exponents, weights):
            coeffs[exponent] = weight
        certificate = sturm_open_ray(coeffs, u0)
        certified_sign = certificate["raw_L_sign_if_certified"]
        if certified_sign is not None and certified_sign != int(item["arb"]["sign"]):
            raise AssertionError("independent Sturm and Arb signs disagree")
        rows.append({
            "archive": path.name,
            "case_id": archive["case_id"],
            "selected_index": ix,
            "combo": item["combo"],
            "W_sha256": hash_value,
            "arb_sign": item["arb"]["sign"],
            **certificate,
        })
    return rows


def main() -> None:
    rows = []
    for path in sorted(VERIFY.glob("weighted-p9-*.json.gz")):
        rows.extend(audit_file(path))
    result = {
        "status": "exact_sturm_finite_cases",
        "scope": "Archived p9 selected W only; no all-n claim.",
        "cases": len(rows),
        "strict_half_ray_sign_certificates": sum(
            row["raw_L_sign_if_certified"] is not None for row in rows
        ),
        "rows": rows,
    }
    path = VERIFY / "analytic-positivity.json"
    path.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")
    print(
        f"cases={result['cases']} strict_half_ray_sign_certificates="
        f"{result['strict_half_ray_sign_certificates']} artifact={path}"
    )
    for row in rows:
        print(
            f"{row['case_id']} #{row['selected_index']} combo={row['combo']}"
            f" roots={row['distinct_roots_open_ray']}"
            f" sign={row['raw_L_sign_if_certified']}"
        )


if __name__ == "__main__":
    main()
