# Generic program bridge audit

Current continuation (2026-10-14): the active route is the full-D native
`ThinInst`/`TaskN` host. Generic parameter procedures, the full-D host and
all cost/exponent assembly have received ACCEPTED. The `mid` instantiation
outline below is historical: with only the weakened preprocessing saving s,
it loses a factor D^(s^2/2) and cannot establish the required exponent.

The original `cost_regime_solve_3sum` reduction now compiles against explicit
interfaces for native Lop detection and all-size uniformization. Those two
interfaces are still unfinished and unpublished. Generic resource bounds
use `Hyp30` below/top proofs from the actual accepted program source;
their fixed (N+1)^5 bounding polynomial is independent of G, while the
level/switch/threshold overhead constants depend on G. The finite regime
test uses the exact equivalence D<=N^a iff D^den(a)<=N^num(a), proved in
`rational_power_representation`. None of these local draft references is
evidence of a completed main theorem.

This audit records which pieces of the accepted foundation are genuinely generic and which are tied to the published numerical specialization. It is based on the task's platform-source mirror and read-only API metadata; it does not replace the open `admissible_parameters_solve_3sum` theorem with the fixed `threeSum_1999017` result.

## Reusable interfaces

- The accepted source `verification/claim_aeUniform_mid-source.lean:7230-7246` gives the exact generic theorem: `(a b c e : ℕ)`, `1 ≤ b`, `1 ≤ e`, `a ≤ b`, and `2*c ≤ e`; the conclusion instantiates `Claim.Theorem_17_mid aeModel strassen` at `D = paramDr a b` and `g = paramGr c e ∘ paramDr a b`. Its proof is generic: `midClaim17_of_host`, `mid_solves`, and the generic parameter-program specifications. The mirror's `Claim.Theorem_17_mid` definition is at `verification/foundation-mirror/Definitions/Def_APSP299791_Defs4.lean:33-47`. The fixed `theorem19_mid` is a separate specialization at `13/228, 11/300` in accepted source lines 7646-7649.
- `.../Def_APSP299791_Defs4.lean:156-162` gives `Claim.Theorem_19_explicitAt`: one exact-triangle solver and constants `K,T`, valid for every `n ≥ n₀`, `κ ≥ 1`, and weight bound `u ≤ n^κ`, with time `K * κ * n^(3-δ) * log(n)^e`.
- The exact generic `exactTriangleUniform_of_explicitAt` statement and proof are in accepted source lines 7395-7411: for any model `M`, `δ`, `e`, and threshold `n₀`, an explicit-at-threshold algorithm plus brute force, `ChooseBySize`, and `MonoExactTriangle` gives `Claim.ExactTriangleUniform M δ e`. Its proof chooses threshold `max n₀ 3` and combines small and large sizes. `foundation-retuned-uniform.lean:3744-3760` already has the parameter-generic `exactTriangleUniform_of_ae {δ} {e}` conversion from the all-edges host to the light host.
- `.../Def_APSP299791_Defs4.lean:884-947` proves `CorollaryP.costs` for real `c, θ, ε` under `AdmissibleP`; it retains the binomial tail and pruned-encoding term and returns the preprocessing and query estimates. This is the analytic bridge to feed into the program interface.
- `.../Def_APSP299791_Defs4.lean:1091-1125` defines generic `program31P G` and `CostsWithinP G`. The source comment at lines 1096-1100 records `exists_tPre31_le_p`, `exists_tQuery31_le_p`, `exists_tOffline32_le_p`, and `programSolves_of_costsWithinP`. These are cost-to-correctness helpers for arbitrary `G : RatParams`; the mirror keeps the definition of `CostsWithinP` but skeleton-subtracts the helper declarations and their proof bodies, so it does not provide a standalone theorem id or verbatim Lean proof to copy.

## Fixed specialization boundary

`ratParamsP` at `.../Def_APSP299791_Defs4.lean:1162-1181` fixes the program parameters to `c=22`, `θ=29/250`, and the regime `D^91 ≤ N^5`. `programP` at lines 1269-1302 is `program31P ratParamsP` plus the fixed all-instances wrapper. The accepted `Light.Sec4.allInstancesP_programP` theorem is correspondingly only the fixed `programP` solver. Its platform statement is `SolvesN thinTask programP Proc.allInstancesP (allInstancesTimeP cShared30) allInstancesNeedP`.

The read-only submission record's explanation (saved at `allInstancesP_programP-submissions.json`) confirms the correctness path: the regime test selects `offline32` when `D^91 ≤ N^5`; `lim31_of_needP` supplies its limit hypotheses; `preCoreSpec_all`, `queryAtSpec_all`, and `shared_base58` discharge the offline routine's program specifications; outside the regime the thin-product brute force is used.

The accepted Lean source was retrieved from the documented `GET /submissions/{id}/solution` route and saved at `allInstancesP_programP-source.lean`. Its generic part is lines 3800-3867: `pre31_program31_b299791`, `query31_program31`, and `offline32_program31` are all quantified over `G : RatParams`; they assemble actual procedure specifications from procedure-location lemmas and the imported accepted `preCoreSpec_all`, `queryAtSpec_all`, and `shared_base58`. A concise independent extraction is at `generic-program31P-correctness.lean`. The later `regimeP` (lines 4141-4158) and `allInstancesP_solves` (lines 4442-4486) are specialized to `ratParamsP`.

The accepted source of `claim_aeUniform_mid` is also saved at `claim_aeUniform_mid-source.lean`; it contains both the generic `claim_ae_theorem_17_mid` and the generic threshold helper. This confirms that the generic host and uniformization exist as actual Proved-source code, while the `theorem19_mid` route that packages them into one number is fixed.

## Generic instantiation still needed

For the open theorem, keep `c : ℕ` as the exact levels-per-`m` parameter and approximate the arbitrary real `θ` by a rational `p/q`. Use the strict margins in `hprep` and `hquery` and continuity of the entropy expressions to choose `p/q` close enough that the fixed rational program's exponents still obey the desired inequalities. For `claim_ae_theorem_17_mid`, choose integer exponent data with `a/b` the requested outer exponent and `c'/e = s/2`; the side condition `2*c' ≤ e` is exactly `s ≤ 1`. `GammaOf c θ` is the sharp-tail exponent used by `CorollaryP.costs`; its formula is the same as `ThreeSumSharpTail.sharpSaving c θ`. The query exponent is the entropy expression represented by `qOf θ` in the foundation. Instantiate `AdmissibleP` with this rational point and a thin-regime exponent whose product with `Apruned c + GammaOf c (p/q)` is below one; then transfer its cost bounds to `CostsWithinP G` for `G` built from `c` and `p/q`.

Use the generic `programSolves_of_costsWithinP` path to obtain the concrete parameterized offline solver, assemble the generic all-edges host through `claim_ae_theorem_17_mid` with `D=⌊n^(a/b)⌋` and `g=⌈D^(c/e)⌉`, and prove the thresholded exact-triangle bound using the actual scan, prime-selection, instance-build, preprocessing, and query terms. The hypotheses `hprime` and `hbuild` absorb the prime and construction terms; `hprep` and `hquery` absorb the two costs. Apply `exactTriangleUniform_of_explicitAt`, then `exactTriangleUniform_of_ae`, before composing with the original 3SUM reduction and transferring to the shared `EndStatement` model. The finite-program-per-`κ`, bounded-size, and all-sufficient-word-width obligations remain part of that final bridge.

This is an interface outline, not a closed proof: the accepted source gives the generic actual-program specifications, but the rational approximation, transferring its cost estimates through the quantified cost-to-uniform reduction, and the original 3SUM composition still need formal Lean lemmas in the bridge file.
