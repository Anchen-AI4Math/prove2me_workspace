"""Refresh only the original mission's current proof supplement and live counts."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from publish_mission_2026_10_02 import Client, MISSION

TASK = Path(__file__).resolve().parents[1]
OUT = TASK / "formalization/platform"
HEADER = "## Formal proof supplement (2 October 2026)"
ARCHIVE = "https://github.com/Anchen0823/zeta9-research-notes/releases/download/research-2026-10-02/zeta9-formal-proofs-2026-10-02.zip"


def save(name, value):
    path = OUT / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    client = Client()
    before = client.mission()
    assert before["main_theorem"]["status"] == "Open"
    rows = client.call("GET", f"/missions/{MISSION}/milestones?limit=200&offset=0")["milestones"]
    linked = {row["theorem"]["id"]: row["theorem"] for row in rows if row.get("theorem")}
    completed = sum(bool(row.get("completed")) for row in rows)
    batches = []
    for label, folder in (("core", OUT), ("finite-prime arithmetic", OUT / "prime-valuation"),
                          ("C3 coefficient", OUT / "coefficient"), ("unconditional harmonic rates", OUT / "pnt"),
                          ("actual highest-pole coefficients", OUT / "coefficient-map"),
                          ("actual formal local jets", OUT / "coefficient-map-jet"),
                          ("complete local-array injectivity", OUT / "coefficient-map-injectivity"),
                          ("actual global partial fractions", OUT / "coefficient-map-partial-fractions"),
                          ("actual reflection and cancellation", OUT / "coefficient-map-reflection"),
                          ("actual finite harmonic summation", OUT / "coefficient-map-finite-sum"),
                          ("actual absolute infinite summation", OUT / "coefficient-map-summation"),
                          ("actual polynomial shift-degree obstruction", OUT / "coefficient-map-shift-degree"),
                          ("actual five-output linear structure", OUT / "coefficient-map-aggregate"),
                          ("actual telescoper and quotient degree", OUT / "coefficient-map-telescoper"),
                          ("actual rational quartic kernel and inverse", OUT / "coefficient-map-kernel-bridge"),
                          ("actual original polynomial connection system", OUT / "coefficient-map-connection"),
                          ("actual original F matrix and selected rational inverse", OUT / "coefficient-map-matrix")):
        audit_path = folder / "publication-audit.json"
        if audit_path.exists():
            audit = json.loads(audit_path.read_text(encoding="utf-8"))
            proofs = audit["new_proved_theorems"]
            assert all(p["theorem_id"] in linked and linked[p["theorem_id"]]["status"] == "Proved" for p in proofs)
            batches.append({"batch": label, "accepted_and_linked": len(proofs), "theorems": proofs})
    accepted = sum(batch["accepted_and_linked"] for batch in batches)
    assert accepted >= 6
    published = {batch["batch"]: batch["accepted_and_linked"] for batch in batches}
    c3_state = ("Both C3 proofs are Accepted, public Proved, and linked to this mission."
                if published.get("C3 coefficient") == 2 else
                "The C3 additions are undergoing platform verification.")
    pnt_state = ("All four PNT-transfer and harmonic-rate proofs are Accepted, public Proved, and linked to this mission."
                 if published.get("unconditional harmonic rates") == 4 else
                 "Four exact PNT-transfer and harmonic-rate statements have been submitted; their platform verification is ongoing.")
    supplement = f"""{HEADER}

A separate [reproducible Lean proof supplement]({ARCHIVE}) contains nine complete solutions: primitive-row Gram divisibility, an actual center-denominator divisor, eightfold endpoint derivative cancellation, harmonic denominator clearing and perturbation stability, and three finite-prime arithmetic results for the actual reduced harmonic denominators. It includes exact sources, independent audits, Lean 4.33.1 / the pinned Mathlib revision, and a fresh minimal-project build. Every solution axiom report contains only the three standard foundational axioms. Its SHA-256 is `50e1058a1c44f65271837a1943bc0a0a7c80385c941413d284e7dcb70ad82405`.

The latest live readback confirms **{accepted} newly accepted public proofs linked to this original mission**. The first six core results are all accepted and Proved; subsequent results are counted here only after acceptance and an actual linked-theorem readback. Queued work is recorded separately from completed milestones.

Two further developments now have complete native kernel proofs: the genuine short-zero coefficient has an explicit signed lower bound and is nonzero for every even degree and every nonnegative parameter; actual MediumPNT discharges the two former PNT inputs and proves the full-sequence harmonic denominator rate, including the order-nine doubled rate 18. The C3 statement concerns the actual coefficient A; nonvanishing of A zeta(9)+B remains a separate obligation. The rational-perturbation rate retains its actual small-denominator assumption. {c3_state} {pnt_state} The conditional appendix in the immutable nine-proof archive records its earlier scope; the new unconditional proof uses an actual independently replayed PNT dependency.

The original research archive and the nine-proof archive are unchanged. The main J exit and the irrationality target remain open.

"""
    finite_count = published.get("actual highest-pole coefficients", 0)
    jet_count = published.get("actual formal local jets", 0)
    array_count = published.get("complete local-array injectivity", 0)
    pf_count = published.get("actual global partial fractions", 0)
    reflection_count = published.get("actual reflection and cancellation", 0)
    finite_sum_count = published.get("actual finite harmonic summation", 0)
    summation_count = published.get("actual absolute infinite summation", 0)
    if finite_count or jet_count:
        finite_state = ("All three actual highest-pole endpoints are Accepted, public Proved and linked: genuine rational-function pole clearance, the exact signed binomial coefficient, and the actual weighted multiplier. "
                        if finite_count == 3 else "")
        jet_state = ("All three formal local-jet endpoints are Accepted, public Proved and linked: uniqueness of the actual cleared formal series and its complete rational and integer-polynomial multiplier convolutions at orders 1 through 9. "
                     if jet_count == 3 else "")
        supplement = supplement.replace("The original research archive", finite_state + jet_state +
            "These are bridges toward the written five-dimensional coefficient map. They do not prove injectivity of that aggregate map, an inverse, numerical-series convergence or the exact infinite L identity.\n\nThe original research archive")
    if array_count == 3:
        supplement = supplement.replace("The original research archive",
            "Three complete local-array proofs are Accepted, public Proved and linked: vanishing of all actual pole coefficients forces a strict proper multiplier to vanish, the full (n+1)-by-9 local coefficient array is injective on that domain, and every quartic multiplier satisfies strict properness. This array retains each pole location and order; its injectivity does not establish invertibility of the five aggregated outputs of the original F. Strict properness permits a simple-pole term and does not supply infinite-sum convergence.\n\nThe original research archive")
    if pf_count == 3:
        supplement = supplement.replace("The original research archive",
            "Three actual global partial-fraction proofs are Accepted, public Proved and linked: the genuine candidate reconstructs all nine local orders, the true polynomial numerator equals the candidate, and the actual rational function equals its partial fractions at every regular rational point under strict properness. This algebraic identity still permits a simple-pole total; the stronger degree gap and a separate genuine summability proof are required for the infinite identity.\n\nThe original research archive")
    if reflection_count == 3:
        supplement = supplement.replace("The original research archive",
            "Three actual reflection and cancellation proofs are Accepted, public Proved and linked: the genuine reflected local coefficient signs for even n, vanishing of the actual even-order totals, and cancellation of the simple-pole total under the stronger degree gap. Even-order cancellation requires even n; the simple-pole result does not. The n=0, W=X^4 boundary satisfies strict properness and has rho_1=1, so those degree conditions remain distinct.\n\nThe original research archive")
    if finite_sum_count == 3:
        supplement = supplement.replace("The original research archive",
            "Three actual finite-sum proofs are Accepted, public Proved and linked: the genuine harmonic shift difference and the exact finite and grouped summation identities for the actual rational family. The simple-pole harmonic term remains present until the separately proved stronger degree cancellation is applied; these finite identities do not assume infinite convergence.\n\nThe original research archive")
    if summation_count == 3:
        supplement = supplement.replace("The original research archive",
            "Three actual infinite-summation proofs are Accepted, public Proved and linked: absolute summability under the stronger degree gap, genuine HasSum of the actual series to its exact odd-zeta linear form for even n, and the original even n>=2 integer-quartic identity. The actual cancellation, harmonic limits and absolute summability are derived in the complete proof; no series-convergence or zeta-identity assumption is supplied. These statements concern p=9, q=1, m=n, d=0.\n\nThe original research archive")
    if published.get("actual polynomial shift-degree obstruction") == 3:
        supplement = supplement.replace("The original research archive",
            "Three actual polynomial shift-degree proofs are Accepted, public Proved and linked: the exact next surviving coefficient, its genuine degree lower bound, and the low-degree obstruction forcing the input polynomial to vanish. The original quotient bound and n>=1 are retained; no rational-telescoper relationship or coefficient-map inverse is assumed by these polynomial statements.\n\nThe original research archive")
    if published.get("actual five-output linear structure") == 3:
        supplement = supplement.replace("The original research archive",
            "Three actual aggregate proofs are Accepted, public Proved and linked: additivity of the original five outputs, exact quartic-coordinate restoration, and cancellation of all order totals from a zero aggregate under evenness and the stronger degree gap. The proof-bearing linear-map definitions were checked against the genuine native definitions by kernel equality; omitted proof fields in pretty printing are not used as equality evidence. These three statements establish the linear structure; the kernel and inverse require the subsequent bridge.\n\nThe original research archive")
    if published.get("actual telescoper and quotient degree") == 3:
        supplement = supplement.replace("The original research archive",
            "Three genuine telescoper proofs are Accepted, public Proved and linked: the actual weighted rational function is a difference of cumulative partial fractions, the cumulative function has its actual cleared rational representation, and the true numerator has the root-factor divisibility and quotient degree bound. Parity, degree-gap, zero-output and regular-point conditions remain exactly where required. No telescoper or quotient existence premise substitutes for the construction.\n\nThe original research archive")
    if published.get("actual rational quartic kernel and inverse") == 3:
        supplement = supplement.replace("The original research archive",
            "Three actual kernel-and-inverse proofs are Accepted, public Proved and linked for every even n>=2: the rational quartic aggregate kernel is zero, the original five-dimensional map is bijective, and its inverse multiplier gives a genuine HasSum with absolute summability for every prescribed rational target. Integer output coordinates still have rational multiplier preimages; these statements do not prove integral multiplier preimages, effective denominator heights, small nonzero integer forms, J or irrationality.\n\nThe original research archive")
    if published.get("actual original polynomial connection system") == 3:
        supplement = supplement.replace("The original research archive",
            "Three original polynomial connection proofs are Accepted, public Proved and linked for every n>=1: the genuine homogeneous kernel vanishes, the actual fifteen-coordinate map is bijective, and all five original right-side systems have unique rational polynomial solutions with the stated degree bounds. The even t-coefficient basis determines the full original polynomial equation and is triangularly equivalent to the u-coefficient basis. Actual rational-function and five-output parameter transport remain separate obligations.\n\nThe original research archive")
    if published.get("actual original F matrix and selected rational inverse") == 3:
        supplement = supplement.replace("The original research archive",
            "Three actual matrix and selected-inverse proofs are Accepted, public Proved and linked for every even n>=2: the genuine five-output matrix has nonzero determinant, the selected rational quartic coordinates equal (b,a) S F inverse, and its actual weighted rational function has absolutely convergent sum b+a zeta(9) for integer targets b,a. The multiplier coefficients remain rational; integer coefficients, effective denominator heights, full parameter transport, J and irrationality are separate obligations.\n\nThe original research archive")
    advanced_receipt = TASK / "publication/2026-10-02/advanced-proofs/release-upload-receipt.json"
    if advanced_receipt.exists():
        receipt = json.loads(advanced_receipt.read_text(encoding="utf-8"))
        assert receipt["verified"] is True
        supplement = supplement.replace("The original research archive", f"A separate [advanced proof source package]({receipt['url']}) provides the complete C3 and unconditional harmonic-rate developments, the actual fixed upstream source closure and licenses, and a native build with no PNT placeholder. Its SHA-256 is `{receipt['sha256']}`.\n\nThe original research archive")
        independent_assets = [a for a in receipt.get("assets", []) if a["name"] == "ADVANCED-PROOFS-INDEPENDENT-REVIEW.json"]
        if independent_assets:
            url = independent_assets[0]["url"]
            supplement = supplement.replace("The original research archive", f"The [independent source-package review]({url}) records the full recursively checked import closures and any manifest metadata corrections.\n\nThe original research archive")
    description = before["description"]
    assert description.count(HEADER) == 1
    begin = description.index(HEADER)
    end = description.index("## Selected references", begin)
    updated = description[:begin] + supplement + description[end:]
    updated, matches = re.subn(r"The current formal record reports \d+ milestones, \d+ theorem links, and\n\d+ completed entries\.",
        f"The current formal record reports {len(rows)} milestones, {len(linked)} theorem links, and\n{completed} completed entries.", updated)
    assert matches == 1
    updated = updated.replace("these results; the recent proofs have not been checked in Lean. Their",
        "these results. Parts now have complete Lean proofs, described below; other\nparts retain their written-proof scope. Their")
    save("mission-formal-refresh-before.json", before)
    save("mission-formal-refresh-request.json", {"description": updated})
    if updated != description:
        save("mission-formal-refresh-receipt.json", client.call("PATCH", "/missions/" + MISSION, {"description": updated}))
    after = client.mission()
    assert after["description"] == updated
    assert after["main_theorem"]["status"] == "Open"
    save("mission-current.json", after)
    save("milestones-current.json", rows)
    save("mission-formal-refresh-audit.json", {"mission_id": MISSION, "milestones": len(rows),
        "linked_theorems": len(linked), "completed_milestones": completed, "new_accepted_linked": accepted,
        "root_status": "Open", "visibility": after["visibility"], "batches": batches,
        "description_readback_matches": True})
    print(f"Original mission refreshed: {len(rows)} milestones, {len(linked)} theorem links, {completed} completed; {accepted} new accepted proofs. Root Open, visibility {after['visibility']}.")


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        raise SystemExit(str(error)) from None
