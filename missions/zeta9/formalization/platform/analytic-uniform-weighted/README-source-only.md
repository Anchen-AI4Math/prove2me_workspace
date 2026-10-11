# Analytic uniform weighted platform batch — SOURCE only

Stage: **UNCOMPILED TRANSPLANT**. This preparation has run no Lean, API or
credential access. Native independent review was pending when the package was
prepared. No platform author/independent PASS or upload is claimed.

The author-native result is an actual weighted analytic **upper bound**.
Integer preimage/height, J/nonzero, the exact f-star limit and irrationality
remain open.

## Selected original endpoints

1. `ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound`:
   for every natural `n,r` with `1 ≤ n` and `r ≤ 4`, the actual raw moment is at
   most `C*(n+1)^10*exp(-(2641/250)*n)*n^(2*r)`.
2. `ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound`:
   for any family `W : ℕ → ℚ[X]` whose degree is at most four at every index,
   the weighted actual series satisfies the same coefficient-independent
   prefactor times `∑r<5 |coeff(W_n,r)|*n^(2*r)` for every `n ≥ 1`.
3. `ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one`:
   there exists one `ε : ℕ → ℝ` tending to zero, independent of the coefficients,
   for which every `n ≥ 1` and every rational quartic satisfy the original
   `exp((-2641/250+ε_n)*n)` bound.

All three exact original headers, including every parameter, binder, cast and
domain condition, are in `target-plan.json`. No summability, HasSum, moment
bound, coefficient-size, parity or uniform-error assumption has been added.

## Payload layout

- `native-source-closure/`: eleven byte-exact successful mathematical author
  SOURCES. Their 122 original theorem declarations comprise CoefficientMap18,
  Phase34 and the new analytic70. Historical SOURCE-only comments are preserved
  as part of the actual bound native input, with their status explained here.
- `staged/Definitions/Def_ZetaNine_AnalyticUniformWeighted.lean`: exactly the 13
  new functions in their original namespaces, with their complete original
  types and bodies. It imports the canonical CoefficientMap and Phase public
  definition modules. Their staged copies are byte-exact local canonical
  sources; all sixteen old function bodies match the native baseline.
- `staged/Theorems/`: three complete original statements with `by sorry`, used
  only for statement registration/type catalogs. No solution imports them.
- `staged/Solutions/`: each of the three solutions contains all 122 complete
  original theorem bodies inline and one exact `solution` wrapper. Definitions
  resolve to the genuine imported canonical/new function bodies. There are no
  Theorems placeholders, extra mathematical assumptions or omitted proof bodies.
- `catalog/`: the three statements together, still type-only `by sorry`.
- `controls/`: uncompiled future audit SOURCE. Each target has a separate
  AF-derived type/kernel/boundary/resolver set, expanded to all 122 expected
  complete types, all 29 whole type/value and `rfl` controls, the exact wrapper
  type and complete wrapper proof, fifteen typed boundaries, and all actual
  declarations/compiler-helper inventories. Common SOURCE includes the full
  lossless Expr-DAG serializer and the twenty constructor/metadata/payload
  fixtures plus three small-source reconstruction checks.

Each selected Solution contains the same 122 canonical native theorem names.
Future native checks must therefore use separate projects/environments for the
three targets; importing their three Solution modules together would duplicate
those names. This separation changes no theorem domain or definition value.

## Pure preparation evidence

`source-preparation-v1.json` pins the successful native author audit, all eleven
SOURCE input/copy hashes, all 122 original complete prefixes, all 29 whole
definition blocks, payload hashes and the future full-control plan.

`pure-fidelity-v1.json` rechecks 69 recorded bindings. In every solution, each
of the 122 **complete proof declarations** occurs exactly once as the unchanged
original text. Every original full header is unchanged; the wrapper preserves
the complete original header except the name `solution`. All 29 function bodies
are exact, and the SOURCE controls preserve all required target sets. These are
lexical/byte checks, not native or independent proof verification.

The source assembler's one blank-separator assertion failure is retained in
`preparation-failure-01.json`; no mathematical source body changed in its fix.
The original native author frozen directory has not been modified.

## Required future actual verification

After an explicit lane grant, freshly compile the staged canonical definitions,
new definition, selected complete solution, lossless serializer/fixtures and
all controls serially. Use pinned Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474` and intrinsic Lean 4.33.1. Borrow no
author, Root, API or other private mathematical proof objects.

Retain all failures, complete actual stdout/stderr/exit logs, object/source
bindings and actual canonical import paths. Record full lossless type/value
payloads, exact reconstruction, `Expr.equal` diagnostics, `isDefEq`, `inferType`,
whole-function `rfl`, all actual/generated kernel helpers and the standard
axioms. Keep any raw inequality of compiler-helper names visible; normalize
only full-expression-identical paired proposition-valued helpers after their
separate complete checks. Independently reproduce the entire transplant before
publication. This package has not performed those future checks.
