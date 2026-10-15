# Retained exact box-count cost audit

## Finding

The source-level relaxation is at the Corollary 26/31 cost step named
`dominated_cost8_of_eq_10`, identified in the light-language guide at
`foundation-exact-triangle-solution.lean:8733-8750`. Its explanation says the
Corollary 31 proof reuses the Corollary 26 proof and derives the cost from the
first term of (8) plus equation (10). The handoff records the already-relaxed
first term of `cost8` as `L * m * rho^t / (1-rho) * N^2`
(`algorithm-bridge-obligations.md:22-32`). This is where the geometric tail
has replaced the exact box-count tail.

The program's actual offline cost is stated at
`foundation-exact-triangle-solution.lean:10101-10108`: equation (9) has query
cost `L |W| sum_{d=0}^t alpha_d`, preprocessing term
`L m rho^t/(1-rho) N^2`, and encoding/tile-fit term
`N * 10^L/(sqrt(K) N0)`. This is the cost theorem to strengthen while keeping
the correctness proof reusable. The snapshot labels the actual procedure as
`preCore` and its step function `tPreCore` in
`upstream-PROGRAMS.md:523-530`; `fillList` inserts boxes, `tile` builds each
tile's trie, and `allTiles` constructs all of them (`upstream-PROGRAMS.md:520-528`).
The concrete parameter program includes `pre31Body G` at procedure 64
(`foundation-exact-triangle-solution.lean:10761-10773`).

## Existing tail theorem and downstream consumers

`Definitions/Def_ThreeSumSharpTail_Analysis.lean:23` defines
`boxCount c m d = choose (c*m) (m-d) * 9^(c*m-m+d)`, the exact beta sequence
needed by the certificate. `Solutions/Sol_ThreeSumSharpTail_sharp_normalized_tail.lean:146-183`
proves a geometric estimate for the tail, and `:220-294` proves the sharper
entropy estimate for the exact finite sum from `ceil(theta*m)` through `m`.
Thus the analytic result exists; the missing result is a step-count lemma for
the program that still mentions this finite sum.

The existing parameter bridge first obtains `Corollary31.costs` and then
packages its result as `CostsWithin` in
`upstream/ThreeSumApsp/Programs/Sec4/ChoosingParameters/RealParameters.lean:23-27,112-140`.
The compiled correctness interfaces consume `CostsWithin` in
`upstream/ThreeSumApsp/Programs/Sec4/ChoosingParameters/Program.lean:119-142`.
The newly fetched `foundation-mirror/Definitions/Def_APSPSource_RemainingDefinitions.lean`
now exposes the actual step functions. `tFillStep`, `tFillList`, `tTile`, and
`tAllTiles` are at lines 33937-33960; `tPreCore` is at 34663-34664. The precise
old contract is visible at lines 35456-35467: `CostsWithin` requires the
preprocessing cost to be bounded by `cost8`, so the old geometric rate cannot
be recovered or reused for the sharper exponent. The detailed upstream
`Costs.lean` proof remains absent from the snapshot.

## Smallest useful next theorem

Add a sibling cost theorem at the `Corollary31.costs` layer (in the local
proof-bearing bridge, preserving upstream reference files) whose preprocessing
bound names the actual box-work sum
`(m + 1) * sum_{d in Icc (ceil(theta*m)) m} boxCount c m d`, alongside the
existing encoding and tile-fit terms. Prove that bound from the `pre31` /
`preCore` step assembly, rather than from `dominated_cost8_of_eq_10`; then use
the existing `sharp_normalized_tail` result to show this retained term fits
the chosen preprocessing exponent. Once that theorem yields the same
`CostsWithin` contract, the existing `exists_ratParams`, compiled program,
offline solver, and correctness proofs remain usable.

The first Lean lemma is now an exact structural arithmetic bridge for the
actual program's `tTile`: with
`B := sum e in range (m - t + 1), (starBoxes L m t e).length`, expansion of the
published cost definitions gives
`tTile = 220 + (m - t + 1) * (30*L + 150) + B * (580*L + 790)`, hence
`tTile ≤ 1500 * (L + 1) * (B + m + 1)`. The corresponding `tAllTiles` bound
follows directly from its exact formula. These lemmas are in
`lean/RetainedTileWork.lean`. They expose real program work and assume no box
count identity. A new retained-tail cost interface must replace or extend
`CostsWithin`; the existing interface still embeds the old `cost8` rate. The
actual preCore step-count assembly can then consume the all-tiles bound, and
only afterward can the entropy tail be applied. Do not replace the target with
a certificate-only or oracle statement.
