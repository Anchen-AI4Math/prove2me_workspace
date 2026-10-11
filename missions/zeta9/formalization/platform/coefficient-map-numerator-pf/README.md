# Generic numerator PF platform preparation

This folder contains pure preparation only. No Lean/Lake oracles, declaration
graph, parser result, kernel result, platform author PASS, upload, installation
or platform acceptance is claimed. The Root agent controls the next Lean lane.

Both fixed native reports and every bound byte are reverified: native author
24 checks / 188 bindings and independent native review 32 checks / 388 bindings.
Their historical compiler failures, object reuse and exclusions remain explicit.

The native source writer follows actual import lines, obtaining 16 source
modules. Those lines are compilation scheduling hints; they are not an
elaborated declaration dependency graph. Five existing pure platform Definition
sources are copied and hash-matched to installed sources. No object is copied.
The new `.rt/pa1` project was absent initially; its `b` and `.lake` remain absent.
Only after a lane grant may the driver link the pinned shared package directory.

The first real phase is 43 serial calls: runtime 1, native sources 16, native
controls 4, Stage1 1, source Stage2 16, header 1, existing Definition sources 4.
The official graph/parser/header templates are copied as source. Actual input
normalization and span evidence will be recorded only after genuine calls.

The three targets preserve their complete native domains:

- `actual_numerator_polynomial_partial_fractions`: arbitrary `m` and actual `A`,
  with `A.natDegree < 9*(m+1)`.
- `actual_numerator_global_partial_fractions`: the same bound, rational `t`,
  and `t+k != 0` for every `k <= m`.
- `actual_numerator_local_coefficients_injective`: two actual polynomials,
  their two strict degree bounds, and equality of actual jets for `j <= m`
  and `1 <= s <= 9`.

The four PF source definitions and two generic Data definitions are candidates;
the minimal included Data set is pending actual reachability, and all twelve
Data definitions are never selected merely because they share a source module.
Exact source spans will determine complete proof closure and declaration order.
New staged controls will explicitly select original generic declarations from
actual parser facts and list any Data/Connection-only exclusions. There is no
PF-existence hypothesis, abstract-array hypothesis or coefficient transport
assumption. Full native/staged type/value kernel comparisons and whole-function
`rfl` are required for every included new pure definition.

Short platform module suffixes `polynomial`, `global`, `injective` preserve
Windows private-object path space; original theorem names and types stay exact.
This task-local preparation writes no Root modules, scope, API or credentials.

Pure commands: `python prepare.py`, `python write_driver.py`, then
`python freeze_preparation.py`. Run `prepare.py` only on the initially absent
project. Future `python execute_oracles.py --lane-granted` requires an explicit
Root grant and must not run while both global Lean lanes are occupied.
