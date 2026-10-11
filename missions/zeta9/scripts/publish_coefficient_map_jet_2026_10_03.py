"""Publish the actual formal local jets after their public Base definition exists."""
from __future__ import annotations
import argparse
import json
import sys

import publish_coefficient_map_2026_10_03 as common

common.OUT = common.api.TASK / "formalization/platform/coefficient-map-jet"
common.SOURCE = "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a"
common.EXPECTED_CHECKS = 13
common.SCOPE_LABEL = "actual formal local-jet entry"
common.EXPLANATION_OVERRIDES = {
    "clearedSeries_unique": "The actual erased pole-product polynomial has nonzero constant coefficient, proved from its genuine finite product. Its ninth power is a unit in Q[[z]]. Multiplying the assumed numerator identity by the actual inverse proves uniqueness of the explicitly constructed cleared series. The only given S condition is its legitimate cleared numerator equation, not any coefficient or F-invertibility result.",
    "coefficient_convolution_explicit": "The genuine weighted cleared series is the actual numerator/unit-denominator quotient multiplied by W composed with the true local quadratic coordinate. The power-series multiplication coefficient formula and an explicitly proved antidiagonal-to-Icc bijection give the complete convolution at every order 1<=s<=9. No abstract coefficient array or partial-fraction assumption is used; this is a formal local-series statement.",
    "integer_coefficient_convolution": "Apply the actual all-order coefficient convolution and the proved map from the integer local quadratic polynomial to its exact rational counterpart. Polynomial map_comp and coefficient mapping identify the integer multiplier coefficients and their rational casts. This does not assert integrality of all underlying local rational coefficients, numeric-series convergence, aggregate F invertibility or the exact infinite L identity.",
}
common.TITLE_OVERRIDES = {
    "clearedSeries_unique": "Z9.F local model — Uniqueness of the genuine cleared formal series",
    "coefficient_convolution_explicit": "Z9.F local model — All nine actual weighted coefficient convolutions",
    "integer_coefficient_convolution": "Z9.F local model — Exact integer-polynomial multiplier convolution",
}


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("definitions", "poll-jobs", "problems", "verify", "poll-proofs", "link", "check-only"))
    args = parser.parse_args()
    definitions, problems = common.gate()
    if args.mode == "check-only":
        print("Actual local-jet frozen sources, independent review, installed bytes and scoped build verified. No API operation.")
        return
    api = common.api
    client = api.Client()
    path = api.TASK / "formalization/platform/coefficient-map/definition-receipts/ZetaNine_CoefficientMap.json"
    receipt = json.loads(path.read_text(encoding="utf-8"))
    base_job = client.call("GET", "/publish-jobs/" + receipt["job_id"])
    api.save("base-definition-live-readback.json", base_job)
    if base_job["status"] != "PUBLISHED":
        raise RuntimeError("Base definition is still " + base_job["status"] + "; wait for its existing job before publishing dependent Jet modules.")
    if args.mode == "definitions": api.publish_definitions(client, definitions)
    elif args.mode == "poll-jobs": api.poll_jobs(client, definitions, problems)
    elif args.mode == "problems": api.publish_problems(client, definitions, problems)
    elif args.mode == "verify": api.verify(client, problems)
    elif args.mode == "poll-proofs": api.poll_proofs(client, problems)
    else: common.link(client, problems)


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        raise SystemExit(str(error)) from None
