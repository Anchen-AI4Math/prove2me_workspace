# Read-only next-parent review (2026-10-11)

This is a route assessment, not a compilation or platform-readiness certificate.
Inputs: `verified-stage-progress.json` SHA-256 `ef3f68761fa9c4e1565e11696b9120e104847e4ae77ab8400616f69c9c96c261` (22 published Definitions, 20 accepted/proved own proofs); `decl_graph.jsonl` SHA-256 `dcae43b0481ca8781071ec96ac5920bdebc3280636c3a610fb855ba8e8a769c4`; fixed source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

## Correction to the frozen AP7 queue

`verification/ap7/next-after-comparison.json` says `strictWeightedSimplex` and `realWeightedSimplex` are in one of the 22 published Definition packages. The current publication inventory lists `SimplexFloor` and `SimplexUnweighted`, but no package containing the two weighted definitions. Treat that sentence as stale. Preserve the AP7 queue unchanged as historical evidence. The new AP9 simplex/domain provider stages address the missing definitions; neither is published at this checkpoint.

## Two substantial helper branches before `no_fixed_data`

The source of `OAI.PiExponent.DeterminantContradiction.no_fixed_data_of_interpolation_and_analytic_aggregate` is lines 125–165 of `DeterminantContradiction.lean` (SHA-256 `74329150cc64ac655ee0ce56454519170ce15b4b58dfd85ba5a9ab850c740e53`). Its direct dependency set has 36 source-graph names. The generic full-row-minor proof is locally certified in AP8, but the following two direct proof dependencies remain larger:

| Own target to solve | Direct source-graph names | Raw transitive source-graph closure | Dominant source modules |
| --- | ---: | ---: | --- |
| `actual_minor_arithmetic_lower_bound` | 36 | 125 names, 75 theorems | `MatrixArithmetic` 34, `Arithmetic` 27, `InterpolationMatrix` 16, `DeterminantContradiction` 12 |
| `tendsto_collisionRate` | 20 | 71 names, 40 theorems | `SimplexCounting` 16, `DeterminantContradiction` 10, `MatrixCounting` 9 |

These are raw closures before subtracting any available Definition or accepted theorem interfaces; they are not a count of required new platform submissions. The generic arithmetic engine `MatrixArithmetic.selectedMinor_arithmetic_lower_bound` alone reaches 90 graph names (63 theorems); the counting engine `MatrixCounting.tendsto_collisionRatio` reaches 44 (33 theorems).

## Practical grouped route

1. Finish and certify the AP9 weighted simplex and row/column domain Definitions. Then isolate the few data declarations used by the two helper statements: `MatrixArithmetic.logWeights`, `meanRowWeight`, `selectedMinor`, rational centers/truncation orders, and the `DeterminantContradiction` `FixedData`/row/column/actual-matrix/actual-minor/mean/count/rate/limit abbreviations and definitions. Preserve original definitional equality: the `no_fixed_data` source transfers nonzero determinant from `actualMatrix` to `actualMinor` by direct elaboration.
2. Target `tendsto_collisionRate` as one accepted proof. Its short source proof calls `MatrixCounting.tendsto_collisionRatio`; group that module's rational-log, normalized row/count, ratio and collision lemmas (137-line module), backed by a coherent rational simplex counting package. The existing `SimplexFloor` and `SimplexUnweighted` providers can be imported. Keep the original complete lemma commands together where a compiler file remains within 300 seconds; split at the counting/rational-simplex boundary if needed.
3. Target `actual_minor_arithmetic_lower_bound` as one accepted proof. Its 12-line source proof calls `MatrixArithmetic.selectedMinor_arithmetic_lower_bound`; group the arithmetic/row-translation/matrix-cost lemmas as a few source-faithful proof packages rather than submitting each low-level theorem separately. `MatrixArithmetic` is 448 lines and `Arithmetic` is 329 lines, so preflight each proposed package under the 300-second per-file budget before choosing a split.
4. Once both own helper targets are accepted/proved and the data providers are published, stage `no_fixed_data` using its original proof plus the accepted generic minor and comparison theorems. Require fresh exact platform readbacks for each imported theorem and actual CI/type/Std3 checks. This parent remains open until those gates pass.

Only AP8's generic minor has a local actual proof certificate at this point. Grouped helper packaging and compile times are recommendations to test, not verified results.
