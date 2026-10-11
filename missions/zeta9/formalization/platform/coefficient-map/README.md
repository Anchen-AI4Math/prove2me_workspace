# CoefficientMap finite-entry offline platform batch

This batch preserves the actual finite products from `formalization/CoefficientMap.lean`, SHA256 `e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03`. It uses Lean 4.33.1 and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`.

The three public endpoints are:

- `ZetaNine.CoefficientMap.clear_highest_pole`: clearing the factor at a rational point where every factor `t + k`, for `k ≤ n`, is nonzero.
- `ZetaNine.CoefficientMap.leadingPoleCoefficient_eq`: the actual cleared highest coefficient equals the signed binomial formula for all natural `n` and `j ≤ n`, including `n = 0` and both endpoint poles.
- `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even`: for even `n` and any rational polynomial `W`, the actual weighted highest coefficient is the unweighted binomial factor times `W(-j(n-j))`. This value may be zero.

The one lightweight Definition module contains nine original `def` declaration spans: `numerator`, `poleProduct`, `actualR`, `clearedPoleProduct`, `clearedR`, `leadingPoleCoefficient`, `weightedR`, `clearedWeightedR`, and `weightedLeadingPoleCoefficient`. It contains no lemmas or proofs and never defines a coefficient using the closed formula. `weightedR` is retained beyond the strict three-root union because it is the actual weighted rational function and is used by the original `clear_weighted_highest_pole` helper, retained with the complete mathematical source core.

The actual official Stage1 declaration metaprogram and Stage2 Lean parser/reference oracle were executed against the frozen original source. Stage2 additionally emits parser command spans solely to remove the eight `#print axioms` diagnostics. Every Solution preserves all 18 original helper theorems and proofs inline, deletes only the nine moved definition declarations and those diagnostics, renames its selected theorem binding and resolved references, and appends an exact original-signature `solution` wrapper. No external platform theorem is assumed.

Seven staged modules and eight actual import/type/value reports compile with observed exit code zero. The original/Solution/reference statement types agree exactly under full-name printing. All nine definition types and values agree in the original, Definition, and all six Solution/reference environments; their source declaration bytes are exact. The three Solution proofs have precisely `propext`, `Classical.choice`, and `Quot.sound`. The reference theorem files contain `sorryAx` deliberately and serve only as statement stubs.

`definitions-request.json` and `problems-request.json` contain only fields documented in the local 2026-10-03 `contribute.md`. `author-audit.json` is an author's offline gate, separate from independent mathematical and transplant review. `root-copy-plan.json` lists the seven source files for installation by the parent agent. The author has not modified shared modules, `scope.json`, old batches, or the frozen source and has not read credentials or called the platform API. Local compilation does not claim publication or server acceptance.

This is a finite entry. It does not establish a complete Laurent expansion, lower partial fractions, full reflection or invertibility of a coefficient map, an exact infinite L-sum, a J certificate, or irrationality of zeta(9).

Evidence is frozen by `SHA256SUMS.txt`. Reproduction scripts are `run_oracles.py`, `prepare_coefficient_map.py`, `compile_staged.py`, and `audit_and_freeze.py`; all compilation outputs are task-local. The frozen original source is also hash-bound by the audit.
