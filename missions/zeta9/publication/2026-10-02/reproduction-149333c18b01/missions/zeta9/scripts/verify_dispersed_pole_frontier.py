"""Finite exact audit of the h=1, S=1 dispersed-pole classification.

This is a predetermined proof audit, not an unbounded candidate search.  The
uniform theorem is proved in research/dispersed-pole-frontier-2026-10-02.md.
Integer poles and abstract rational square-node controls are kept separate.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import math
from collections import Counter
from pathlib import Path

from verify_pole_dimension_frontier import Q, Poly, arb, ctx, primitive, ball, vp
import sympy as sp

HERE = Path(__file__).resolve().parents[1]
OUT = HERE / "verification/dispersed-pole-frontier-2026-10-02"
E8 = math.lcm(*range(1, 9)) ** 9


def harmonic_prefix(bound):
    answer = [Q(0)]
    for n in range(1, bound + 1):
        answer.append(answer[-1] + Q(1, n**9))
    return answer


def complete_homogeneous(nodes, degree):
    if degree < 0:
        return 0
    answer = [1] + [0] * degree
    for x in nodes:
        for j in range(1, degree + 1):
            answer[j] += x * answer[j - 1]
    return answer[degree]


def weights_for_squares(nodes):
    d = [math.prod((y - x for j, y in enumerate(nodes) if i != j), start=Q(1))
         for i, x in enumerate(nodes)]
    weights = [x**4 / value for x, value in zip(nodes, d)]
    tails = [sum(weights[j:], Q(0)) for j in range(len(nodes))] + [Q(0)]
    return d, weights, tails


def color_at(poles, weights, threshold, small_harmonics):
    colors = [int((Q(a) / threshold).floor()) for a in poles]
    return colors, sum((w * small_harmonics[k] for w, k in zip(weights, colors)), Q(0))


def cells(poles, weights, low, high, small_harmonics):
    endpoints = {Q(low), Q(high)}
    for a in poles:
        for k in range(1, len(small_harmonics)):
            point = Q(a, k)
            if low < point < high:
                endpoints.add(point)
    endpoints = sorted(endpoints)
    answer = []
    for x, y in zip(endpoints, endpoints[1:]):
        colors, f = color_at(poles, weights, (x + y) / 2, small_harmonics)
        answer.append((x, y, colors, f))
    return answer


def serialize_cells(answer):
    return [{"low": str(x), "high": str(y), "colors": k, "F": str(f)}
            for x, y, k, f in answer]


def selected_budget(poles, weights, tails, small_harmonics):
    m, b = len(poles), poles[-1]
    half = cells(poles, weights, Q(b, 2), Q(b), small_harmonics)
    g = sum((y - x for x, y, _, f in half if f), Q(0))
    live_half = [(x, y, k, f) for x, y, k, f in half if f]
    if m <= 2:
        assert g == Q(b, 2)
        return "no-zero-tail", g, live_half
    if m in (3, 4):
        assert (2 * g + b)**2 >= (6 - m) * b**2
        return "three-four-pole-half-budget", g, live_half
    assert m == 5
    u, t = tails[1], tails[3]
    if g >= Q(b, 50):
        return "five-pole-half-budget", g, live_half
    assert t == 0
    if u:
        assert poles[2] < Q(13 * b, 25)
        assert poles[3] > Q(49 * b, 50)
        assert poles[0] > Q(2 * b, 5)
        chosen = cells(poles, weights, Q(b, 3), Q(2 * b, 5), small_harmonics)
        assert all(k == [1, 1, 1, 2, 2] and f == 1 for _, _, k, f in chosen)
        return "top-two-zero-second-level", g, chosen
    assert poles[0] > Q(b, 4)
    chosen = cells(poles, weights, Q(b, 8), Q(b, 4), small_harmonics)
    assert all(f >= 1 and min(k) >= 1 and max(k) <= 8 for _, _, k, f in chosen)
    return "both-even-tails-zero-third-level", g, chosen


def predetermined_cases():
    answer = []
    bounds = {1: 16, 2: 16, 3: 12, 4: 10, 5: 9}
    for m, bound in bounds.items():
        for poles in itertools.combinations(range(1, bound + 1), m):
            answer.append((poles, "complete-bounded-grid"))
    for poles in ((60, 65, 75, 100, 156), (420, 525, 580, 609, 700),
                  (1, 2, 11, 71, 127), (1, 3, 31, 67, 127),
                  (5, 19, 73, 109), (1, 47, 127), (1, 127),
                  (1, 3, 17, 31, 71, 127), (11, 19, 37, 59, 83, 101, 127)):
        answer.append((poles, "dispersed-and-exception-controls"))
    return answer, bounds


def rational_square_controls():
    # These are geometric controls with positive rational squared nodes.
    # They are deliberately NOT reported as integer-pole functional cases.
    x, y = Q(16), Q(25)
    a = x * y * (x*x + x*y + y*y)
    d = (x + y) * (x*x + y*y)
    u3 = a / d
    v = Q(12)
    c4 = x*x*y*y * (x + y)
    u4 = (c4 - v*a) / (a - v*d)
    v, w = Q(2), Q(9)
    c5, a5 = x**3*y**3, x*x*y*y*(x + y)
    u5 = (c5 - (v+w)*a5 + v*w*a) / (a5 - (v+w)*a + v*w*d)
    answer = []
    for nodes in ((u3, x, y), (u4, Q(12), x, y), (u5, v, w, x, y)):
        assert all(0 < p < q for p, q in zip(nodes, nodes[1:]))
        _, _, tails = weights_for_squares(nodes)
        assert tails[-3] == 0
        necessary_sum = sum((Q(1) / (1 - z / x) for z in nodes[:-2]), Q(0))
        assert necessary_sum > 4
        for high_count in range(1, len(nodes) + 1, 2):
            assert (-1)**(len(nodes)-1) * tails[len(nodes)-high_count] > 0
        answer.append({"square_nodes": [str(z) for z in nodes],
                       "top_two_tail": "0", "Rolle_sum": str(necessary_sum),
                       "kind": "rational-square geometry; not integer poles"})
    inequality_one = Q(2401, 2001) + Q(4802, 1725)
    inequality_two = Q(9604, 8979) + Q(9604, 8354) + Q(2401, 1725)
    assert inequality_one < 4 and inequality_two < 4
    return {"top_two_zero_controls": answer,
            "first_contradiction_bound": str(inequality_one),
            "second_contradiction_bound": str(inequality_two)}


def audit(poles, tag, harmonics, small_harmonics):
    m, b = len(poles), poles[-1]
    nodes = [Q(a*a) for a in poles]
    denominators, weights, tails = weights_for_squares(nodes)
    v = math.prod((poles[j]**2 - poles[i]**2 for i in range(m) for j in range(i+1, m)))
    B = sum(weights, Q(0))
    assert B == complete_homogeneous([-a*a for a in poles], 5-m)
    assert B.denom() == 1
    C = sum(((-a**8 * harmonics[a] - Q(1, 8) + Q(1, 2*a)) / d
             for a, d in zip(poles, denominators)), Q(0))
    delta = Poly([C, B])
    scalar, coefficients = primitive(delta)
    value, precision = ball(coefficients)
    # Verify partial fractions independently at three positive rational points.
    for point in (Q(1, 3), Q(1), Q(7)):
        assert sum((Q(1) / (d*(point + a*a)) for a, d in zip(poles, denominators)), Q(0)) == \
            Q(1) / math.prod((point + a*a for a in poles), start=Q(1))
    result = {"poles": list(poles), "tag": tag, "B": str(B), "C": str(C),
              "weights": [str(w) for w in weights], "tails": [str(w) for w in tails],
              "scalar": str(scalar), "primitive_coefficients": [str(x) for x in coefficients],
              "positive_arb_ball": str(value), "arb_precision_bits": precision,
              "prime_checks": []}
    if m >= 6:
        assert B == 0 and coefficients == [1] and C > 0
        result["budget_branch"] = "degree-zero-primitive-one"
        return result
    assert B and delta.degree() == 1
    assert int(B.numer()) % int(scalar.denom()) == 0
    for high_count in range(1, m + 1, 2):
        assert (-1)**(m-1) * tails[m-high_count] > 0
    if m in (3, 4, 5) and tails[m-2] == 0:
        assert sum((Q(1) / (1 - Q(a*a, poles[-2]**2)) for a in poles[:-2]), Q(0)) > 4
    if m == 5 and tails[1] == 0:
        assert math.prod(a*a - poles[0]**2 for a in poles[1:]) == poles[0]**8
        assert poles[1]**2 < 2 * poles[0]**2
    branch, g, chosen = selected_budget(poles, weights, tails, small_harmonics)
    assert chosen and all(f for _, _, _, f in chosen)
    length = sum((y-x for x, y, _, _ in chosen), Q(0))
    if m == 5:
        assert length >= Q(b, 50)
    result.update(budget_branch=branch, nonzero_half_length=str(g),
                  selected_total_length=str(length), selected_color_cells=serialize_cells(chosen))
    fixed_exclusion = abs(E8 * v * math.prod(poles) * int(B.numer()))
    for p in sp.primerange(5, b + 1):
        if p*p <= b or fixed_exclusion % p == 0:
            continue
        selected = next((f for x, y, _, f in chosen if x < p < y), None)
        if selected is None or int(selected.numer()) % p == 0:
            continue
        colors, f = color_at(poles, weights, Q(p), small_harmonics)
        assert f == selected and vp(f, p) == 0
        assert vp(C, p) == -9 and vp(scalar, p) == 9
        # The individual harmonic principal parts, before summing residues.
        for a, k in zip(poles, colors):
            assert vp(harmonics[a] - Q(1, p**9)*small_harmonics[k], p) >= 0
        result["prime_checks"].append({"prime": p, "colors": colors, "F": str(f),
                                       "v_C": -9, "v_scalar": 9})
    assert arb(value / arb(scalar)) >= arb(Q(1, 4*20643840*(b*b+1)**m))
    return result


def main():
    cases, bounds = predetermined_cases()
    harmonics = harmonic_prefix(max(p[-1] for p, _ in cases))
    small_harmonics = harmonics[:9]
    controls = rational_square_controls()
    rows = [audit(poles, tag, harmonics, small_harmonics) for poles, tag in cases]
    exception = next(r for r in rows if r["poles"] == [420, 525, 580, 609, 700])
    assert exception["tails"][1] == "0"
    assert exception["nonzero_half_length"] == "245"
    live_values = [(ball([int(c) for c in r["primitive_coefficients"]])[0], r)
                   for r in rows if len(r["poles"]) <= 5]
    best_value, best_row = live_values[0]
    for value, row in live_values[1:]:
        if value < best_value:
            best_value, best_row = value, row
    assert all(row is best_row or best_value < value for value, row in live_values)
    summary = {"status": "PASS", "integer_case_count": len(rows),
               "complete_grid_max_pole_by_m": bounds,
               "prime_valuation_checks": sum(len(r["prime_checks"]) for r in rows),
               "branch_counts": dict(Counter(r["budget_branch"] for r in rows)),
               "exact_zero_tail_integer_cases": [r["poles"] for r in rows
                   if len(r["poles"]) <= 5 and any(w == "0" for w in r["tails"][1:-1])],
               "rational_square_control_count": len(controls["top_two_zero_controls"]),
               "finite_minimum_live_degree": {"poles": best_row["poles"],
                   "primitive_coefficients": best_row["primitive_coefficients"],
                   "positive_arb_ball": str(best_value)},
               "live_degree_below_one_cases": [row["poles"] for value, row in live_values if value < 1],
               "scope": "finite exact audit; all-parameter claims require the written proof",
               "unexercised_integer_branches": [s for s in (
                   "top-two-zero-second-level", "both-even-tails-zero-third-level")
                   if not any(r["budget_branch"] == s for r in rows)]}
    certificate = {"summary": summary, "geometric_controls": controls, "cases": rows,
                   "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "certificate.json").write_text(json.dumps(certificate, indent=2), encoding="utf-8")
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
