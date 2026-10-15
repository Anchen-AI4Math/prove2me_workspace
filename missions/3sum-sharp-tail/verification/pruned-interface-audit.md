# Pruned-program interface audit for the sharp-tail bridge

## Finding

The accepted retuned foundation already has the right *program-level* interface for a new
parameter choice. It defines `program31P G` from the same base58 code plus the parameterized
`procs31 G` (`foundation-mirror/Definitions/Def_APSP299791_Defs3.lean:461`), and its
`CostsWithinP` contract feeds directly into preprocessing/query/offline time theorems. The gap is
the analytic proof of that contract at the mission's sharp-tail parameters and target rates. The
existing generic corollary is reusable as a fallback with its old `GammaOf` estimate and log
losses, but it does not establish the exact new `s`-saving costs needed by the target theorem.

## Reusable interfaces and bodies

- `tPreCoreP c p t` is the concrete pruned preprocessing core: `c * sharedShapeP` plus
  `tAllTiles` and a constant (`Def_APSP299791_Defs2.lean:662`); `tPre31P` sets up and calls that
  core (`Def_APSP299791_Defs2.lean:1155-1168`).
- The accepted proof `exists_tPreCore_le_p` proves the core costs `O(cost8p)`
  (`foundation-retuned-uniform.lean:2862-2865`). `exists_tPre31_le_cost8p` then proves the whole
  setup is `O(cost8p)`, relying only on `N * 4^m` and `N * (L+1)` lower bounds for that cost
  (`:2898-2919`). `exists_tPre31_le_p` transports a `CostsWithinP` witness into any preprocessing
  bound `tp` (`:2923-2937`); `exists_tOffline32_le_p` combines it with the unchanged query bound
  (`:2970-2994`). These proofs are parameter-generic in `G`; no new program correctness theorem is
  needed for `c=21`.
- The exact cost contract is `CostsWithinP G C N D₀ tp tq` at
  `Def_APSP299791_Defs4.lean:1112-1125`: above `G.m₀`, it asks for `Hyp30`, `cost8p ≤ C*tp`, and
  `costQuery ≤ C*tq`. The actual scalar parameters are encoded by
  `RatParams` (`Def_APSPSource_RemainingDefinitions.lean:35085-35104`), with
  `parOf`/`switchOf31` at `:35145-35147`. Thus the exact rational choices `a/b=21/1` and
  `p/q=5601/50000` give `L=21m` and `t=ceil(0.11202m)` for every integer `m`, subject to the
  routine `Nat` ceiling simplifications. `ratParamsP` at `Defs4:1170-1181` is only the older
  `22,29/250` instance; its constants/threshold cannot simply be reused.
- The accepted generic `CorollaryP.costs` (`Defs4:880-890`) takes arbitrary real
  `AdmissibleP c θ ε`, but currently concludes preprocessing
  `C*N²*log²(D)/D^(GammaOf c θ)` and query `C*D^(qOf θ)*log(D)`.
  `AdmissibleP` requires `ε*(Apruned c + GammaOf c θ)<1` (`:451-456`). The proof splits cost into
  `first_term_le` (`:791-820`) and `second_term_le` (`:821-...`), then absorbs ceiling padding
  (`CorollaryP.costs`, `:923-948`). The second-term argument specifically uses
  `retained ≤ M/(1-rhoC c)` (`:837-842`), so it does not yet exploit the mission's new encoding
  estimate.
- Retained counts are already connected to the source combinatorics:
  `retW_eq_sum` and `retW_eq_retained` (`foundation-retuned-uniform.lean:2567-2593`) identify
  `retW` with the finite beta sum, and `sqrt_M_eq` (`:2601-2604`) identifies `sqrt M` with
  `sqrtKN0`. The source definitions give `M = choose(L,m)*3^(2*(L-m))`
  (`Def_APSPSource_PaperStatements.lean:326,330,432`) and beta
  `= choose(L,m-d)*9^(L-m+d)` (`Defs4:560`); hence the `d=0` mission `boxCount` is exactly the
  denominator `M` when `L=21m`. These definitional equalities need a short Lean lemma, not a new
  combinatorial hypothesis.

## Exact missing analytic bridge

For `c=21`, `theta=0.11202`, set `L=21m` and `t=ceil(theta*m)`. The new mission proof should first
produce the sharp tail ratio directly in the existing numerator convention:

```lean
tailBeta (21*m) m (Nat.ceil (theta*m)) / (ThreeSumApsp.M (21*m) m : ℝ)
  ≤ Ctail * (ThreeSumApsp.D m : ℝ) ^ (-(ThreeSumSharpTail.sharpSaving 21 theta))
```

with whatever explicit polynomial-in-`m` factor is actually discharged by the mission's
`sharp_normalized_tail` certificate. The exponent `GammaOf 21 theta` in
`tail_div_M_le` (Defs4:634-...) is algebraically the same entropy expression as
`ThreeSumSharpTail.sharpSaving 21 theta`; the difference to prove is the certificate's sharper
prefactor/rate and the conversion to the exact requested `s`, not a different exponent identity.
The accepted `first_term_le` currently adds `log²(D)` to the generic `D^(-GammaOf)` estimate.

For the retained/encoding summand, use the new `encoding_bound` theorem with `c=21` and `m` to
bound `10^(21m)/sqrt(boxCount 21 m 0)`. The count identity above converts this to
`10^L/sqrt(M) ≤ sqrt(L+1)*4^(m*encodingExponent 21)`. The missing helper is the combinatorial
upper bound `retW L m ≤ 10^L` (then `retW_eq_retained` transfers it); the retuned source currently
has only the lower bound `nine_pow_le_retW` (`foundation-retuned-uniform.lean:2080`). It should
follow by recognizing the retained sum as an initial segment of the binomial expansion of
`(1+9)^L`; the platform mirror already contains `Nat.choose_mul_pow_mul_pow_le` with `a=1,b=9`
(`Def_APSP299791_Defs1.lean:1657`), which gives a safe fallback `retW L m ≤ (m+1)*10^L`
termwise if the finite-sum proof is awkward. Once the sharper form is proved,
the cost second summand is at most
`L*N*sqrt(L+1)*4^(m*encodingExponent 21)`. Relating `4^m` to `D` contributes a fixed factor and
the displayed `L*sqrt(L+1)` is an extra polylogarithmic factor. This is exactly where the
parameter slack `henc` and the `a,s` exponent inequalities must be used; the old helper
`second_term_le` instead assumes `sqrtKN0*D^Gamma ≤ N` and uses the retained/M bound.

The query side is already generic in `theta` (`CorollaryP.dominated_costQuery` is used at
`Defs4:898,945-948`), but to meet the main theorem's bound it still needs the explicit slack step
from `s < 1/2 - queryExponent(theta)` to absorb the query's log factor. Likewise, the sharp tail
and encoding bounds must be converted to the target `tp` with a strict exponent margin from
`hprep : s < sharpSaving 21 theta`; prove those conversions for sufficiently large `m`, then fold
the finite prefix into a new threshold.

## Recommended theorem boundary

Keep the accepted program and transport proofs unchanged. Add a parameter-specific certificate
whose conclusion is a `CostsWithinP G C N D₀ tp tq` witness for
`G := {a:=21, b:=1, p:=5601, q:=50000, m₀:=m₀}` and the rates required by the main theorem.
Its above-threshold proof should establish `Hyp30` with the existing source lemmas, prove the new
sharp-tail first-summand estimate, prove `retW≤10^L` plus the encoding-bound second-summand
estimate, and invoke the existing query estimate. Then apply
`exists_tOffline32_le_p`/`programSolves_of_costsWithinP`. The target theorem's remaining `a,s,r`
arithmetic (`Thm_ThreeSumSharpTail_admissible_parameters_solve_3sum.lean:9-18`) is a final exponent
bookkeeping step after the actual finite program cost is exposed.

The accepted `claim_etUniform_mid` at
`foundation-retuned-uniform.lean:3761-3763` is a valid fixed ExactTriangle uniform result, but it
does not supply this parameterized `CostsWithinP` certificate or discharge the mission's sharp-tail
cost analysis. It should remain a useful downstream theorem, not a substitute for this bridge.
