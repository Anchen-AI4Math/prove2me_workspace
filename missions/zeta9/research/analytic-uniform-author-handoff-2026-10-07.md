# Actual uniform weighted analytic upper bound: author handoff

The native author run proves the complete weighted upper-bound endpoint below.
Independent reproduction and platform publication are pending. Integer
preimage/height, the final J/nonzero condition, the exact f-star limit, and the
irrationality of zeta(9) remain open.

Let `R_n(k)` be the original `ZetaNine.CoefficientMap.actualR`, with its actual
rational numerator/pole-product definition, and let `W` be an arbitrary rational
polynomial of degree at most four. The endpoint is the full type of
`ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one`:

```
∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
  ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
    |∑' m : ℕ, actualWeightedSequence n W m| ≤
      Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) *
        weightedCoefficientHeight n W
```

Here `actualWeightedSequence n W m` is exactly the real cast of
`CoefficientMap.weightedR n W (m+1)`, and the height is
`∑ r∈range 5, |W.coeff r| n^(2*r)`. The error is independent of `W`, so `W`
may change arbitrarily with `n`. Summability, the moment upper bounds and the
vanishing error are all proved in the SOURCE chain; none is an input assumption.
Evenness is not needed for this upper bound.

The explicit finite prefactor is

```
C * (n+1)^10 * exp(-(2641/250)*n),
C = 5184*exp(18) + (729/224)*exp(7),
ε_n = (log C + 10*log(n+1))/n.
```

The chain consists of eight new complete SOURCE modules with 70 theorem bodies
and 13 mathematical definitions: factorial log induction, the genuine rational
product/factorial bridge, shifted log/compact bounds, direct product tail bounds,
quantitative p-series tails, actual raw moments, uniform moments and arbitrary
weighted polynomials. Its dependencies are the original CoefficientMap SOURCE
and the already reviewed native Phase/Upper SOURCE. Those dependencies were
freshly compiled inside the same author project.

## Actual author evidence

- Frozen audit:
  `verification/formalization-analytic-factorial-preparation-2026-10-07/author-complete-audit.json`
  (56,280 bytes, SHA-256
  `fa1b455c1de84c664c89d169a39538e77e229a6c16961abbebe5b84951020c81`).
- Actual calls: 29, with 18 successes and 11 preserved historical failures.
  Every final required SOURCE/control call exited zero. No handle remains live;
  the final project-specific WMI check found zero active processes.
- Complete controls: 70 expected full theorem types; 29 whole dependency/new
  definition type-and-value checks and whole-function `rfl` checks; 34 strictly
  paired compiler proof-helper checks; 15 typed boundary controls.
- The complete module inventory contains 291 declarations. All actual values
  were reconstructed from a full-field lossless Expr DAG, checked with
  `Expr.equal`, `isDefEq` and `inferType`, and checked against the three standard
  axioms `propext`, `Classical.choice` and `Quot.sound`.
- The serializer was freshly source-compiled in this project and passed 20
  constructor/metadata/payload fixtures plus three small-source raw-tree
  reconstruction checks. The format retains all expression constructors,
  universe levels, names, binder annotations, literals, metadata and syntax
  payloads.
- Raw `Expr.equal` is false for 14 whole definition values because their own
  proposition proof-helper names differ. These false diagnostics and both raw
  complete values are retained. All helper pairs have literally equal complete
  types and values, are proposition-valued, are separately type checked, and
  have standard axioms. Expanding only those verified helper pairs produces
  literally equal complete values. No binders or metadata were removed.
- Full control records: 401 AFTypes, 232 AFKernel, 15 AFBoundary, and 5,725 actual
  module resolver records. The actual own 11 mathematical module paths resolve
  exclusively to the author's fresh objects; package paths resolve to the
  pinned dependencies and intrinsic Lean 4.33.1. No foreign mathematical object
  or Root proof fallback was used.
- The freezer rehashed 1,546 recorded input/output/snapshot/log/path bindings.
  The frozen calls and full unabridged records are alongside the audit.

## Independent reproduction inputs

Use the complete actual successful SOURCE exports under
`verification/formalization-analytic-factorial-preparation-2026-10-07/native-author-export/`:

- `src/` contains the 11 mathematical modules, including the proper full-path
  `missions/zeta9/formalization/AnalyticPhase.lean` imported by Upper.
- `controls/` contains AFTypes, AFKernel, AFBoundary, AFResolver, AFExprDag and
  AFExprDagValidation.

The export bindings and module-to-source mappings are in the frozen author
audit. Reproduce by copying these SOURCE files into a fresh private project,
keeping their real import paths, freshly compiling them serially, and comparing
the complete type/definition/record inventories. Pinned package objects and the
intrinsic Lean runtime may be used. Author, Root, API or other private proof
objects must not be borrowed.

The original `formalization/Analytic*.lean` preparation candidates and the
preparation v1/v2 audits are intentionally preserved as historical immutable
inputs. Successful proof-body repairs are in the exported private v2 SOURCES;
all original complete theorem prefixes and all whole mathematical definition
types/values remain exactly unchanged. Audit controls advanced separately to v4
after retaining an IO-lifting failure and a raw-tree memory failure. These
preparation labels are not claims that every historical file compiled.
