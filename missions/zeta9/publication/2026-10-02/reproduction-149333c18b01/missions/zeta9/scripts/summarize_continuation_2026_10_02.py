"""Summarize the five frozen 2026-10-02 zeta9 verification groups."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification/continuation-2026-10-02"
DATE = "2026-10-02"
GROUPS = (
    "direction-arithmetic-next", "growing-rank-one-route",
    "dispersed-pole-frontier", "new-linear-form-route",
    "new-linear-form-route-repair",
)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(relative: str):
    return json.loads((ROOT / relative).read_text(encoding="utf-8"))


def main():
    documents = {}
    hashes_checked = 0
    for group in GROUPS:
        base = f"verification/{group}-{DATE}"
        cert = read_json(f"{base}/certificate.json")
        summary_path = ROOT / base / "summary.json"
        summary = read_json(f"{base}/summary.json") if summary_path.exists() else cert
        status = summary.get("result", summary.get("status"))
        assert status == "PASS", (group, status)
        documents[group] = (cert, summary)
        for relative, expected in summary.get("source_hashes", {}).items():
            assert sha(ROOT / relative) == expected, relative
            hashes_checked += 1
        if "proof_sha256" in cert:
            assert sha(ROOT / f"research/{group}-{DATE}.md") == cert["proof_sha256"]
            hashes_checked += 1
        stem = {
            "new-linear-form-route": "verify_new_linear_form_route",
            "new-linear-form-route-repair": "verify_new_linear_form_repair",
            "dispersed-pole-frontier": "verify_dispersed_pole_frontier",
        }.get(group)
        if stem:
            expected = cert.get("script_sha256", cert.get("source_sha256"))
            assert sha(ROOT / f"scripts/{stem}.py") == expected
            hashes_checked += 1

    direction = documents["direction-arithmetic-next"][1]
    growing = documents["growing-rank-one-route"][1]
    dispersed = documents["dispersed-pole-frontier"][1]
    isolated = documents["new-linear-form-route"][0]
    repair = documents["new-linear-form-route-repair"][0]
    assert direction["actual_matrix_cases"] == direction["primitive_values_below_one"] == 6
    assert direction["gram_cases"] == 358 and direction["local_cases"] == 2864
    assert direction["denominator_minimal_interval_cases"] == 160
    assert growing["case_count"] == 39 and growing["large_minor_gcd_one_cases"] == 38
    assert dispersed["integer_case_count"] == 701 and dispersed["prime_valuation_checks"] == 213
    assert len(isolated["partial_fraction_parameters"]) == 24
    assert isolated["residue_polynomial_checks"] == 324
    assert isolated["prime_congruence_checks"] == 79
    assert isolated["good_prime_exact_valuation_checks"] == 77
    assert len(repair["parameters"]) == 6
    assert repair["residue_polynomial_checks"] == 90
    assert repair["endpoint_zero_derivative_checks"] == 168

    workspace_log = (OUT / "workspace-check.log").read_text(encoding="utf-8-sig")
    old_unassigned = [
        "Solutions/Sol_TaoFivePrimes_mertens_tail_upper_bound.lean",
        "Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large_mawia_v2.lean",
    ]
    assert all(path in workspace_log for path in old_unassigned)
    errors = [line for line in workspace_log.splitlines() if line.startswith("ERROR:")]
    assert errors == [f"ERROR: Unassigned solution: {path}; add it to a mission scope.json"
                      for path in old_unassigned], errors
    build_log = (OUT / "build-dry-run.log").read_text(encoding="utf-8-sig")
    assert build_log.startswith("zeta9: 8 selected root modules (plus their imports)"), build_log
    scope = read_json("scope.json")
    expected_sources = (
        [f"research/{name}-{DATE}.md" for name in GROUPS]
        + [f"research/continuation-review-{DATE}.md", f"research/progress-{DATE}.md"]
        + ["scripts/verify_direction_arithmetic_next.py", "scripts/verify_growing_rank_one_route.py",
           "scripts/verify_dispersed_pole_frontier.py", "scripts/verify_new_linear_form_route.py",
           "scripts/verify_new_linear_form_repair.py", "scripts/summarize_continuation_2026_10_02.py"]
    )
    assert all(f"missions/zeta9/{p}" in scope["sources"] for p in expected_sources)
    assert all(f"missions/zeta9/verification/{g}-{DATE}/*" in scope["sources"]
               for g in GROUPS + ("continuation",))

    selected_files = ["status.md", "scope.json"] + expected_sources + [
        "scripts/verify_direction_frontier.py", "scripts/probe_exterior_cone.py",
        "scripts/probe_positive_hankel.py", "scripts/verify_pole_dimension_frontier.py",
        "round6/scripts/independent_audit.py", "verification/local-connection-2026-09-28/symbolic.json",
        "verification/continuation-2026-10-02/README.md",
        "verification/continuation-2026-10-02/workspace-check.log",
        "verification/continuation-2026-10-02/build-dry-run.log",
    ]
    for group in GROUPS:
        for name in ("certificate.json", "summary.json"):
            relative = f"verification/{group}-{DATE}/{name}"
            if (ROOT / relative).exists():
                selected_files.append(relative)
    sources = {relative: sha(ROOT / relative) for relative in selected_files}
    output = {
        "result": "PASS", "date": DATE,
        "five_verifiers_root_rerun": "PASS", "certificate_embedded_source_hashes_checked": hashes_checked,
        "direction": {key: direction[key] for key in (
            "actual_matrix_cases", "actual_local_checks", "gram_cases", "local_cases",
            "denominator_minimal_interval_cases", "primitive_values_below_one")},
        "growing_rank_one": {key: growing[key] for key in (
            "case_count", "below_one_cases", "large_minor_gcd_one_cases", "exponential_constants")},
        "dispersed": {key: dispersed[key] for key in (
            "integer_case_count", "prime_valuation_checks", "rational_square_control_count",
            "exact_zero_tail_integer_cases", "unexercised_integer_branches")},
        "isolated": {key: isolated[key] for key in (
            "partial_fraction_parameters", "residue_polynomial_checks", "prime_congruence_checks",
            "good_prime_exact_valuation_checks", "extra_local_and_ball_parameters")},
        "repair": {key: repair[key] for key in (
            "parameters", "residue_polynomial_checks", "endpoint_zero_derivative_checks")},
        "workspace_check": {
            "global_pass": False, "new_zeta9_sources_owned": True,
            "preexisting_other_task_unassigned": old_unassigned,
        },
        "formal": {"actual_lean_build_run": False, "build_dry_run_only": True,
                   "existing_selected_entry_count": 8, "new_formal_modules": 0},
        "irrationality_proved": False, "external_submission": False,
        "boundaries": [
            "Minimum-interval denominator infinite decay still equals the unproved main exit.",
            "Growing-rank-one error squeeze is proved in writing; denominator asymptotic is unproved.",
            "Scalar dispersed theorem covers all integer positions, but not higher-rank dispersed matrices.",
            "Isolated-series exceptional-prime mass bound and repair asymptotics remain unproved.",
            "Finite exact/Arb checks and independent written proof reviews are not Lean verification.",
        ],
        "source_sha256": sources,
    }
    (OUT / "summary.json").write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"result": "PASS", "groups": len(GROUPS),
                      "embedded_source_hashes_checked": hashes_checked,
                      "manifest_file_count": len(sources), "irrationality_proved": False}, indent=2))


if __name__ == "__main__":
    main()
