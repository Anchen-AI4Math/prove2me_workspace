"""Validate the local zeta(9) theorem DAG and replay five frozen finite checks.

This script makes no Prove2me requests and contains no theorem search. Use
--write-audit only when intentionally regenerating verification/finite-audit.json.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import re
import sys

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]
sys.path.insert(0, str(ROOT / "tmp/zeta7/exact_packages"))
sys.set_int_max_str_digits(0)
from flint import arb, ctx, fmpq, fmpz  # type: ignore  # noqa: E402


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_gram(rows: list[list[int]], weights: list[int]) -> tuple[int, int, int]:
    x = [a * w for a, w in zip(rows[0], weights, strict=True)]
    y = [a * w for a, w in zip(rows[1], weights, strict=True)]
    return sum(a*a for a in x), sum(a*b for a, b in zip(x, y)), sum(b*b for b in y)


def taylor_coefficients(row: list[int], n: int) -> list[int]:
    u0 = (n + 1) * (2*n + 1)
    return [sum(math.comb(r, j)*row[r]*u0**(r-j) for r in range(j, 5))
            for j in range(5)]


def one_sign(values: list[int]) -> bool:
    return (all(value >= 0 for value in values) or
            all(value <= 0 for value in values)) and any(values)


def matmul(left: list[list[int]], right: list[list[int]]) -> list[list[int]]:
    return [[sum(left[i][k] * right[k][j] for k in range(len(right)))
             for j in range(len(right[0]))] for i in range(len(left))]


def det3(M: list[list[int | Fraction]]) -> int | Fraction:
    return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
            -M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
            +M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))


def kernel_area_check(n: int, delta2: int, weights: list[int]) -> dict:
    source = ROOT / f"missions/zeta9/round6/verification/search-input-n{n}.json.gz"
    with gzip.open(source, "rt", encoding="utf-8") as stream:
        raw = json.load(stream)
    assert raw["vector_order"] == ["B", "zeta3", "zeta5", "zeta7", "zeta9"]
    assert raw["W_order"] == [f"u^{r}" for r in range(5)]
    q = math.lcm(*range(1, n+1)) ** 9
    L = []
    for row in raw["raw_monomial_vectors"]:
        scaled = [Fraction(int(pair[0])*q, int(pair[1])) for pair in row[1:4]]
        assert all(value.denominator == 1 for value in scaled)
        L.append([int(value) for value in scaled])
    assert len(L) == 5 and all(len(row) == 3 for row in L)
    minors = {I: int(det3([L[i] for i in I]))
              for I in itertools.combinations(range(5), 3)}
    delta3 = math.gcd(*minors.values())
    assert delta3 > 0
    predicted2 = sum((minor//delta3 * math.prod(weights[i] for i in range(5) if i not in I))**2
                     for I, minor in minors.items())
    assert predicted2 == delta2
    gram = [[sum(Fraction(L[i][j]*L[i][k], weights[i]**2) for i in range(5))
             for k in range(3)] for j in range(3)]
    predicted_gram2 = Fraction(math.prod(weights)**2, delta3**2)*det3(gram)
    assert predicted_gram2 == delta2
    return {"round6_input_sha256": digest(source), "delta3_digits": len(str(delta3)),
            "complementary_minors_identity": True, "weighted_gram_identity": True}


def interval(value: arb) -> dict[str, str | int]:
    mid, rad, exp = value.mid_rad_10exp(36)
    return {"mid": str(mid), "rad": str(rad), "exp": int(exp)}


def check_graph(data: dict) -> dict:
    assert data["schema"] == "zeta9-local-theorem-dag-v1"
    assert data["threshold"] == {"numerator": 2641, "denominator": 250, "decimal": "10.564"}
    nodes = data["nodes"]
    ids = [node["id"] for node in nodes]
    assert len(ids) == len(set(ids)) and data["root_id"] in ids
    by_id = {node["id"]: node for node in nodes}
    assert by_id[data["root_id"]]["status"] == "open"
    assert all(node["type"] == "theorem" for node in nodes)
    assert set(node["status"] for node in nodes) == {"open", "proved-in-notes"}

    for node in nodes:
        assert node["title"] and node["statement"]
        if node["status"] == "proved-in-notes":
            assert node.get("evidence"), node["id"]
            for citation in node["evidence"]:
                path = (BASE / citation["path"]).resolve()
                assert path.is_relative_to(ROOT) and path.is_file(), path
                assert citation["section"]
        else:
            assert node.get("obstacle"), node["id"]
        assert "theorem_id" not in node and "platform_status" not in node

    adjacency: dict[str, list[str]] = {name: [] for name in ids}
    reductions = data["reductions"]
    assert len({r["id"] for r in reductions}) == len(reductions)
    assert {r["id"]: (r["parent"], tuple(r["children"])) for r in reductions} == {
        "Z9.RED.R": ("Z9.R", ("Z9.J", "Z9.F", "Z9.A", "Z9.G", "Z9.P")),
        "Z9.RED.R.CRITICAL": ("Z9.R", ("Z9.CP", "Z9.CM")),
        "Z9.RED.R.POS": ("Z9.R", ("Z9.T", "Z9.TP", "Z9.X", "Z9.A", "Z9.F")),
        "Z9.RED.R.SADDLE": ("Z9.R", ("Z9.TS", "Z9.SP", "Z9.X", "Z9.A", "Z9.F")),
        "Z9.RED.R.FIVE": ("Z9.R", ("Z9.T5", "Z9.FQ", "Z9.X", "Z9.A", "Z9.F")),
        "Z9.RED.R.GPOS": ("Z9.R", ("Z9.TG", "Z9.TP", "Z9.V", "Z9.A", "Z9.F")),
        "Z9.RED.J": ("Z9.J", ("Z9.V", "Z9.S")),
        "Z9.RED.T5": ("Z9.T5", ("Z9.TS",)),
        "Z9.RED.T5.DENOM": ("Z9.T5", ("Z9.FD", "Z9.FC")),
        "Z9.RED.V": ("Z9.V", ("Z9.VA", "Z9.Q", "Z9.X")),
        "Z9.RED.VA": ("Z9.VA", ("Z9.VB", "Z9.Y")),
        "Z9.RED.VA.DISCOUNT": ("Z9.VA", ("Z9.VD", "Z9.YD", "Z9.H", "Z9.Z", "Z9.Y")),
        "Z9.RED.VB": ("Z9.VB", ("Z9.VC", "Z9.H", "Z9.Z")),
    }
    for reduction in reductions:
        parent = reduction["parent"]
        children = reduction["children"]
        assert parent in by_id and children and len(children) == len(set(children))
        assert all(child in by_id and child != parent for child in children)
        assert reduction["status"] in {"mathematical-bridge-checked", "sufficient-strengthening-checked"}
        proof_file, anchor = reduction["proof"].split("#", 1)
        proof_path = BASE / proof_file
        headings = re.findall(r"^#+\s+(.+)$", proof_path.read_text(encoding="utf-8"), re.M)
        assert anchor in {re.sub(r"\s+", "-", heading.lower()) for heading in headings}
        adjacency[parent].extend(children)

    assert {(edge["parent"], edge["input"]) for edge in data["research_inputs"]} == {
        ("Z9.V", "Z9.M"), ("Z9.V", "Z9.C"), ("Z9.S", "Z9.L"),
        ("Z9.S", "Z9.LC"), ("Z9.VC", "Z9.I"),
        ("Z9.VD", "Z9.I"), ("Z9.TG", "Z9.LC"),
        ("Z9.T", "Z9.TA"), ("Z9.TG", "Z9.TA"), ("Z9.TS", "Z9.TA"),
        ("Z9.T5", "Z9.TA"), ("Z9.T5", "Z9.GO"), ("Z9.T5", "Z9.FI"),
        ("Z9.T5", "Z9.FO"), ("Z9.T5", "Z9.FM"), ("Z9.T5", "Z9.XL"),
        ("Z9.V", "Z9.XL")
    }
    for edge in data["research_inputs"]:
        assert edge["parent"] in by_id and edge["input"] in by_id
        # Research inputs remain as historical provenance after a parent is
        # proved by a separate, documented argument; they are not proof edges.
        assert by_id[edge["parent"]]["status"] in {"open", "proved-in-notes"}
        assert by_id[edge["input"]]["status"] == "proved-in-notes"
        assert "not a complete reduction" in edge["role"] or "not a lower bound" in edge["role"]
        adjacency[edge["parent"]].append(edge["input"])

    assert {(edge["parent"], edge["dependency"]) for edge in data["proof_dependencies"]} == {
        ("Z9.H", "Z9.M"), ("Z9.Z", "Z9.M"), ("Z9.LC", "Z9.L"),
        ("Z9.I", "Z9.M"), ("Z9.FQ", "Z9.GC"),
        ("Z9.FI", "Z9.FQ"), ("Z9.FI", "Z9.TA"),
        ("Z9.FO", "Z9.TA"), ("Z9.FO", "Z9.X"),
        ("Z9.FC", "Z9.FI"), ("Z9.FC", "Z9.M"),
        ("Z9.XL", "Z9.TA"), ("Z9.XL", "Z9.FC"),
        ("Z9.CM", "Z9.F"), ("Z9.CM", "Z9.TA"),
        ("Z9.CM", "Z9.GC"), ("Z9.CM", "Z9.X")
    }
    for edge in data["proof_dependencies"]:
        assert edge["parent"] in by_id and edge["dependency"] in by_id
        assert by_id[edge["parent"]]["status"] == "proved-in-notes"
        assert by_id[edge["dependency"]]["status"] == "proved-in-notes"
        assert edge["role"]
        adjacency[edge["parent"]].append(edge["dependency"])

    visiting: set[str] = set()
    visited: set[str] = set()

    def walk(node: str) -> None:
        assert node not in visiting, f"cycle at {node}"
        if node in visited:
            return
        visiting.add(node)
        for child in adjacency[node]:
            walk(child)
        visiting.remove(node)
        visited.add(node)

    walk(data["root_id"])
    assert visited == set(ids), f"unreachable: {set(ids)-visited}"
    assert {node["id"] for node in nodes if node["status"] == "open"} == {
        "Z9.R", "Z9.J", "Z9.CP", "Z9.T", "Z9.TS", "Z9.T5", "Z9.FD", "Z9.TG", "Z9.S"
    }
    return {"node_count": len(nodes), "reduction_count": len(reductions),
            "research_input_count": len(data["research_inputs"]),
            "proof_dependency_count": len(data["proof_dependencies"]),
            "open_nodes": [node["id"] for node in nodes if node["status"] == "open"]}


def finite_case(case: dict, minor: dict) -> dict:
    n = int(case["n"])
    assert n in {12, 24, 48, 96, 192}
    D, s1, N, d = (int(case[k]) for k in ("D", "s1", "N", "d_n"))
    assert d == math.lcm(*range(1, n+1)) and N > 0 and D > 0 and s1 > 0
    assert int(minor["n"]) == n and int(minor["N"]) == N
    q, delta3, delta4 = (int(minor[k]) for k in ("q", "delta3", "delta4_star"))
    assert q == d**9 and D*delta4 == q*delta3*s1
    assert N*delta4**2 == abs(int(minor["determinant_cleared"]))*delta3
    J = [[int(value) for value in row] for row in case["J_rows_B_A"]]
    assert abs(J[0][0]*J[1][1]-J[0][1]*J[1][0]) == s1*s1*N
    assert all(value % s1 == 0 for row in J for value in row)
    M = [[value//s1 for value in row] for row in J]
    mode, = [row for row in case["modes"] if row["mode"] == "n2r"]
    weights = [int(w) for w in mode["weights"]]
    assert weights == [n**(2*r) for r in range(5)]
    K = [[int(v) for v in row] for row in case["K_rows"]]
    A, B, C = exact_gram(K, weights)
    delta2 = A*C-B*B
    assert delta2 > 0 and delta2 == int(mode["deltaK_squared"])
    kernel_area = kernel_area_check(n, delta2, weights)
    tier, = [row for row in mode["tiers"] if "gcd_N_d_n_pow_2" in row["labels"]]
    g = int(tier["g"])
    assert g == math.gcd(N, d*d) and N % g == 0
    intrinsic_rows = [[g, 0], [0, g],
                      [M[1][1], -M[0][1]], [-M[1][0], M[0][0]]]
    assert all(all(sum(row[k]*M[k][j] for k in range(2)) % g == 0
                   for j in range(2)) for row in intrinsic_rows)
    intrinsic_index = math.gcd(*(intrinsic_rows[i][0]*intrinsic_rows[j][1]
                                 -intrinsic_rows[i][1]*intrinsic_rows[j][0]
                                 for i, j in itertools.combinations(range(4), 2)))
    assert intrinsic_index == g
    factors = [(int(row[0]), int(row[1])) for row in minor["prime_exponents_and_uniform_bounds"]]
    assert math.prod(p**v for p, v in factors) == N
    excess_product = 1
    high_product = 1
    for p, v in factors:
        if p > n:
            high_product *= p**v
        else:
            a = 0
            power = p
            while power <= n:
                a += 1
                power *= p
            excess_product *= p**max(0, v-11*a)
    assert (d**9*excess_product*high_product) % (N//g) == 0
    valuation_by_prime = dict(factors)
    remaining_d = d
    discount_product = 1
    for p in range(2, n+1):
        if remaining_d % p:
            continue
        a = 0
        while remaining_d % p == 0:
            remaining_d //= p
            a += 1
        discount_product *= p**min(max(11*a-valuation_by_prime.get(p, 0), 0), 9*a)
    assert remaining_d == 1
    assert d**9*excess_product*high_product == (N//g)*discount_product
    U = [[int(v) for v in row] for row in case["smith_U"]]
    basis = matmul([[g, 0], [0, 1]], matmul(U, K))
    assert basis == [[int(v) for v in row] for row in tier["basis_rows_diag_g_1_UK"]]
    H = [[int(v) for v in row] for row in tier["gauss_unimodular_H"]]
    assert abs(H[0][0]*H[1][1]-H[0][1]*H[1][0]) == 1
    reduced = matmul(H, basis)
    assert reduced == [[int(v) for v in row] for row in tier["gauss_reduced_rows"]]
    mu2, cross, second2 = exact_gram(reduced, weights)
    assert 0 < mu2 <= second2 and 2*abs(cross) <= mu2
    assert mu2 == int(tier["mu1_squared"])
    assert mu2*second2-cross*cross == g*g*delta2
    g_taylor = taylor_coefficients(reduced[0], n)
    assert one_sign(g_taylor)
    g_lift_norm2 = Fraction(D*D*mu2, s1*s1*g*g)
    assert g_lift_norm2 < Fraction(251, 250)**(5282*n)
    full_tier, = [row for row in mode["tiers"] if int(row["g"]) == N]
    full_rows = [[int(value) for value in row]
                 for row in full_tier["gauss_reduced_rows"]]
    chosen = {12: 0, 24: 1, 48: 0, 96: 0, 192: 1}[n]
    full_taylor = taylor_coefficients(full_rows[chosen], n)
    assert one_sign(full_taylor)
    full_norm2 = sum((full_rows[chosen][r]*weights[r])**2 for r in range(5))
    s2 = int(case["s2"])
    assert Fraction(D*D*full_norm2, s2*s2) < 2**(2641*n//125)
    if n in (24, 192):
        first_taylor = taylor_coefficients(full_rows[0], n)
        assert first_taylor[0]*first_taylor[4] < 0
    bound2 = Fraction(4*D*D*delta2, 3*s1*s1*mu2)
    saved_bound2 = Fraction(*[int(v) for v in tier["lambda2_upper_squared_numerator_denominator"]])
    assert bound2 == saved_bound2

    with ctx.workprec(512):
        log_delta = arb(fmpz(delta2)).log()/2
        log_g = arb(fmpz(g)).log()
        log_mu = arb(fmpz(mu2)).log()/2
        baseline = (arb(fmpz(D)).log()-arb(fmpz(s1)).log()+log_delta/2-log_g/2)/n
        arithmetic_rate = (arb(fmpz(N)).log()-log_g)/(2*n)
        excess_rate = arb(fmpz(excess_product)).log()/n
        high_rate = arb(fmpz(high_product)).log()/n
        discount_rate = arb(fmpz(discount_product)).log()/n
        inverse_area_rate = (log_delta+2*arb(fmpz(D)).log()
                             -2*arb(fmpz(s1)).log()-arb(fmpz(N)).log())/(2*n)
        volume_discrepancy = arithmetic_rate+inverse_area_rate-baseline
        assert volume_discrepancy.lower() <= arb(0) <= volume_discrepancy.upper()
        shape = (log_g/2+log_delta/2-log_mu)/n
        total = baseline+shape
        gauss_offset = (arb(2).log()-arb(3).log()/2)/n
        old_rate = arb(fmpq(bound2.numerator, bound2.denominator)).log()/(2*n)
        discrepancy = total+gauss_offset-old_rate
        assert discrepancy.lower() <= arb(0) <= discrepancy.upper()
        assert old_rate.upper() < arb(fmpq(2641, 250)).lower()
        recorded = tier["log_lambda2_upper_per_n"]
        scale = fmpq(10) ** int(recorded["exp"])
        lo = (int(recorded["mid"])-int(recorded["rad"]))*scale
        hi = (int(recorded["mid"])+int(recorded["rad"]))*scale
        assert old_rate.lower() >= arb(lo).lower() and old_rate.upper() <= arb(hi).upper()
        result = {"n": n, "g": str(g), "delta_squared": str(delta2), "mu1_squared": str(mu2),
                  "kernel_area": kernel_area,
                  "volume_cancellation": {
                      "q_content_identity": True, "smith_determinant_identity": True,
                      "arithmetic_rate_per_n": interval(arithmetic_rate),
                      "inverse_area_rate_per_n": interval(inverse_area_rate)},
                  "prime_budget": {
                      "exact_divisibility_bound": True,
                      "exact_discount_identity": True,
                      "excess_rate_per_n": interval(excess_rate),
                      "high_prime_rate_per_n": interval(high_rate),
                      "discount_rate_per_n": interval(discount_rate)},
                  "positive_one_form_finite_checks": {
                      "partial_first_taylor_one_sign": True,
                      "partial_first_lifted_norm_below_exp_tau": True,
                      "full_selected_taylor_one_sign": True,
                      "full_selected_norm_below_exp_tau": True,
                      "full_first_endpoint_leading_opposite": n in (24, 192)},
                  "intrinsic_adjugate_generator_index": True,
                  "baseline_per_n": interval(baseline), "shape_per_n": interval(shape),
                  "baseline_plus_shape_per_n": interval(total),
                  "gauss_offset_per_n": interval(gauss_offset),
                  "reported_lambda2_upper_per_n": interval(old_rate),
                  "finite_upper_strictly_below_10_564": True}
    return result


def build_audit() -> dict:
    graph_path = BASE / "dag.json"
    graph = json.loads(graph_path.read_text(encoding="utf-8"))
    checked = check_graph(graph)
    source = ROOT / "missions/zeta9/round7/verification/modulus-scan.json"
    scan = json.loads(source.read_text(encoding="utf-8"))
    minor_source = ROOT / "missions/zeta9/round7/verification/minor-smoothness-audit.json"
    minor_audit = json.loads(minor_source.read_text(encoding="utf-8"))
    minor_by_n = {int(case["n"]): case for case in minor_audit["cases"]}
    script = ROOT / "missions/zeta9/round7/scripts/modulus_scan.py"
    assert scan["source_sha256"]["modulus_scan"] == digest(script)
    cases = [finite_case(case, minor_by_n[int(case["n"])]) for case in scan["cases"]]
    assert [case["n"] for case in cases] == [12, 24, 48, 96, 192]
    return {"status": "passed", "scope": "local DAG and five finite diagnostics only; no R, J, T, T5, TS, TG, V, VC, VD, or S proof",
            "graph_sha256": digest(graph_path), "finite_source_sha256": digest(source),
            "minor_source_sha256": digest(minor_source),
            "graph": checked, "cases": cases}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-audit", action="store_true")
    args = parser.parse_args()
    audit = build_audit()
    output = BASE / "verification/finite-audit.json"
    rendered = json.dumps(audit, ensure_ascii=False, indent=2) + "\n"
    if args.write_audit:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(rendered, encoding="utf-8")
    else:
        assert output.read_text(encoding="utf-8") == rendered, "audit file differs; rerun with --write-audit"
    print(f"passed: {audit['graph']['node_count']} nodes, {audit['graph']['reduction_count']} reductions, "
          f"{len(audit['cases'])} frozen finite cases; root remains open")


if __name__ == "__main__":
    main()
