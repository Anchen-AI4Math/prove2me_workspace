# Direct route to the conditional determinant contradiction

This is a bounded inventory and staging recommendation, not a compilation or
publication certificate. Source commit:
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The 22 published Definitions were
checked through their literal recorded POST bodies and exact public readbacks;
the preserved audit is `published-definition-coverage.json`.

The target is
`OAI.PiExponent.DeterminantContradiction.no_fixed_data_of_interpolation_and_analytic_aggregate`.
Its full original project graph closure has 194 declarations over 14 source
modules. This includes already published providers and proof auxiliaries; it
does not imply that 194 separate submissions are needed.

## Foundation needed by the actual statement

After the two AP9 packages are actually validated and published, the missing
statement data can be supplied in three source-module slices containing only
definitions and abbreviations:

| Original module | Remaining definitions |
| --- | --- |
| InterpolationMatrix | `exponentVector`, `truncatedLog`, `monomialImage`, `entry`, `matrix`, `truncatedLogMatrix` |
| MatrixArithmetic | `logWeights`, `rationalCenters`, `truncationOrders`, `rowWeightedSum`, `meanRowWeight`, `selectedMinor` |
| DeterminantContradiction | `FixedData`, `finiteNumerators`, `finiteDenominators`, `Row`, `Column`, `actualMatrix`, `actualMinor`, `actualMean`, `actualRowCount`, `lowIndexCount`, `collisionRate`, `GlobalInterpolationStatement`, `AnalyticAggregateStatement` |

These are 25 missing statement definitions. Include the additional original
`collisionLimit` in the last package because the proof uses it, giving 26 total.
The existing collision constant, AdmissibleParameters, Parameters and arithmetic
constant providers are reused. The packages are ordered as the table: the matrix
arithmetic data imports the interpolation data; the determinant data imports
both and the already published parameter packages. The AP9 domain package is a
prerequisite, not a substitute for the remaining matrix definitions.

All three packages should copy exact AST slices and actual contexts. Future
stages should preserve the original Mathlib import union (CoreImports plus the
real direct Mathlib imports), reducing it only with an actual successful check.
The current AP9 stages are frozen and must not be recompiled merely for import
performance.

## Coarse proof nodes

The original target proof calls three remaining major intermediate theorems:

1. `actual_minor_arithmetic_lower_bound` calls
   `MatrixArithmetic.selectedMinor_arithmetic_lower_bound`. Its proof branch
   contains the Gaussian coefficient clearing, row and column determinant
   scaling, and denominator estimates. Use the original Arithmetic module
   (329 lines), the necessary PolynomialShift/FiniteExpansion portion of
   RowTranslation (through line 143), and the relevant MatrixArithmetic source
   slice (through line 391) as inline proof auxiliaries. Do not put these
   substantial lemmas into a Definition provider. Attempt one bounded solution
   with source helpers copied inline; if it exceeds 300 seconds, split along
   the actual three module boundaries, exposing a few substantial source
   theorem nodes rather than every helper.
2. `actualMean_bounds` uses `meanRowWeight_nonneg` and
   `meanRowWeight_le_theta`, with `row_weighted_cost_le`,
   `actual_row_card_pos`, `ceil_log_weight_pos`, and the simplex membership/row
   weight lemmas copied inline. It is a short module-sized proof branch once
   the data packages exist.
3. `tendsto_collisionRate` calls `MatrixCounting.tendsto_collisionRatio`.
   Copy the six MatrixCounting lemmas together with the rational-simplex
   asymptotic closure. This closure consists of the needed SimplexCounting
   lemmas, `positive_rational_weights_common_denominator`, and the three
   SimplexRational asymptotic lemmas. Existing SimplexFloor and
   SimplexUnweighted providers already supply their source dependencies.
   `natWeightedSimplex`, `residueRectangle`, and the three MatrixCounting
   count definitions are proof auxiliaries and can remain inline in this
   solution rather than requiring extra published data packages.

The target also uses five AdmissibleParameters methods whose exact source
commands are absent from the 22 public bodies:
`total_error_lt_gap` (266–278), `collision_exceeds_one_add_error` (280–293),
`error_sum_eq` (309–316), `error_sum_lt_gap` (318–322), and
`collision_exceeds_error_sum` (324–328). Copy these five short original methods
together in the parent Sol and any intermediate that actually needs them.

Once these three major child nodes are Accepted, the original
`no_fixed_data` proof can use their platform Theorems, the already Accepted
`determinant_bounds_inconsistent`, and the AP8 full-row-minor theorem, with
short same-module helpers (`finiteDenominators_two_le`, `logWeights_eq`) inline.
For local preflights, use their actual proved OLeans. The source proof must not
derive Std3 evidence from a sorry comparator.

No timing success is asserted for the proposed combined solutions. Each newly
generated file needs its own <=300-second source/type/proof-reference/axiom
checks. Private helpers and equation names must come from actual elaborated CI,
never reconstructed from a presumed suffix. This theorem remains conditional
on the source geometry and analytic aggregate statements; proving it alone does
not complete the final campaign root.
